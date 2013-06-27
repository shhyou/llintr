#include <stdexcept>
#include <string>
#include <vector>
#include <memory>
#include <tuple>
#include "runtime.h"

using namespace std;

string show(ValueType type) {
  switch (type) {
  case ValueType::ClosureType:
    return "ClosureType";
  case ValueType::IntType:
    return "IntType";
  default:
    throw logic_error("show: not valid ValueType");
    return "unknown type";
  }
}

shared_ptr<Env> Nil() {
  return shared_ptr<Env>(new EnvNil());
}

shared_ptr<Env> Cons(const shared_ptr<Value>& _car,
                     const shared_ptr<Env>& _cdr)
{
  return shared_ptr<Env>(new EnvCons(_car, _cdr));
}

static shared_ptr<Value> env_access(shared_ptr<Env> env, uint64_t idx) {
  while (env->type != EnvType::NilType) {
    EnvCons* cons = dynamic_cast<EnvCons*>(env.get());
    if (idx == 0) {
      return cons->car;
    }
    env = cons->cdr;
    idx = idx - 1;
  }
  throw runtime_error("Environment access index out of bound");
  return shared_ptr<Value>(nullptr);
}

shared_ptr<Value> run(const code_t *codes, size_t _code_len) {
  using VT = ValueType;
  Machine M {0, _code_len, codes, {}, {}, Nil()};
  for (;;) {
    Code op = M.fetch<Code>();
    switch (op) {
    case ACCESS:
      {
        uint64_t idx = M.fetch<uint64_t>();
        M.values.push_back(env_access(M.env, idx));
      }
      break;
    case FUNCTION:
      {
        addr_t addr = M.fetch<addr_t>();
        M.values.emplace_back(new Closure(addr, M.env));
      }
      break;
    case SAVE:
      M.stk.emplace_back(M.env);
      break;
    case RESTORE:
      if (M.stk.empty() || M.stk.back().type!=StackType::EnvType)
        throw runtime_error("Expected saved environment at stack top");
      M.env = M.stk.back().env;
      M.stk.pop_back();
      break;
    case CALL:
      {
        shared_ptr<Value> closure_val = M.get_value(VT::ClosureType);
        Closure& closure = dynamic_cast<Closure&>(*closure_val);
        M.values.pop_back();
        shared_ptr<Value> val = M.get_value();
        M.values.pop_back();

        M.stk.emplace_back(M.eip);
        M.env = Cons(val, closure.env);
        M.eip = closure.code_addr;
      }
      break;
    case RETURN:
      if (M.stk.back().type != StackType::AddrType)
        throw runtime_error("Expected return address at stack top");
      M.eip = M.stk.back().addr;
      M.env = dynamic_cast<EnvCons&>(*M.env).cdr;
      M.stk.pop_back();
      break;
    case HALT:
      return M.values.empty()? shared_ptr<Value>(nullptr) : M.values.back();
    case CONSTINT:
      {
        int integer = M.fetch<int>();
        M.values.emplace_back(new IntValue(integer));
      }
      break;
    case ADD:
      {
        int val2 = dynamic_cast<IntValue&>(*M.get_value(VT::IntType)).integer;
        M.values.pop_back();

        int val1 = dynamic_cast<IntValue&>(*M.get_value(VT::IntType)).integer;
        M.values.pop_back();

        M.values.emplace_back(new IntValue(val1 + val2));
      }
      break;
    case BRANCHNZ_REL:
      {
        diff_t rel = M.fetch<diff_t>();

        int val = dynamic_cast<IntValue&>(*M.get_value(VT::IntType)).integer;
        M.values.pop_back();

        if (val != 0) {
          M.eip = M.eip + rel;
        }
      }
      break;
    case JUMP_REL:
      {
        diff_t rel = M.fetch<diff_t>();
        M.eip = M.eip + rel;
      }
      break;
    default:
      throw runtime_error(string("Undefined OP Code: ") + to_string(op));
    }
  }
}
