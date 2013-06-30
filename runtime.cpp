#include <stdexcept>
#include <string>
#include <vector>
#include <memory>
#include <tuple>
#include <unordered_set> //used in show(Machine)
#include <unordered_map>
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

string show(const shared_ptr<Value>& val) {
  if (val->type == ValueType::IntType) {
    return to_string(dynamic_cast<IntValue&>(*val.get()).integer);
  } else if (val->type == ValueType::ClosureType) {
    return string("<function@")
          + to_string(dynamic_cast<Closure&>(*val.get()).code_addr)
          + ">";
  } else {
    return "(unknown type)";
  }
}

string show(Machine& M) {
  static const unordered_set<uint64_t> dbl_op =
    {ACCESS, FUNCTION, CONSTINT, BRANCHNZ_REL, JUMP_REL};
  static const unordered_map<uint64_t, string> disasm =
    {{ACCESS, "ACCESS"}, {FUNCTION, "FUNCTION"}, {SAVE, "SAVE"}, {RESTORE, "RESTORE"},
     {CALL, "CALL"}, {RETURN, "RETURN"}, {HALT, "HALT"}, {CONSTINT, "CONSTINT"},
     {ADD, "ADD"}, {MUL, "MUL"}, {BRANCHNZ_REL, "BRANCHNZ_REL"}, {JUMP_REL, "JUMP_REL"}};
  string res;
  res += string("EIP: ") + to_string(M.eip);
  res += string("    op code: ") + to_string(M.code[M.eip]);
  if (dbl_op.count(M.code[M.eip]))
    res += string(" ") + to_string(M.code[M.eip+1]);
  res += string("   ") + disasm.at(M.code[M.eip]);
  if (dbl_op.count(M.code[M.eip]))
    res += string(" ") + to_string(M.code[M.eip+1]);
  res += "\nvalues:";
  for (auto it=M.values.rbegin(); it!=M.values.rend(); ++it) {
    res += " ";
    res += show(*it); 
  }
  res += "\nstk:";
  for (auto it=M.stk.rbegin(); it!=M.stk.rend(); ++it) {
    res += " ";
    if (it->type == StackType::AddrType) {
      res += "AddrType@";
      res += to_string(it->addr);
    } else {
      res += "EnvType";
    }
  }
  res += "\nenv:";
  for (shared_ptr<Env> e=M.env; e->type!=EnvType::NilType;) {
    res += " " + show(dynamic_cast<EnvCons&>(*e).car);
    e = dynamic_cast<EnvCons&>(*e).cdr;
  }
  res += "\n";
  return move(res);
}

shared_ptr<Value> run(const code_t *codes, size_t _code_len) {
  using VT = ValueType;
  Machine M {0, _code_len, codes, {}, {}, Nil()};
  for (;;) {
//cout<<show(M)<<endl;
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
    case TAILCALL:
      {
        shared_ptr<Value> closure_val = M.get_value(VT::ClosureType);
        Closure& closure = dynamic_cast<Closure&>(*closure_val);
        M.values.pop_back();
        shared_ptr<Value> val = M.get_value();
        M.values.pop_back();

        if (op == CALL) {
          M.stk.emplace_back(M.eip);
        }
        M.env = Cons(val, closure.env);
        M.eip = closure.code_addr;
      }
      break;
    case RETURN:
      if (M.stk.back().type != StackType::AddrType)
        throw runtime_error("Expected return address at stack top");
      M.eip = M.stk.back().addr;
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
    case MUL:
      {
        int val2 = dynamic_cast<IntValue&>(*M.get_value(VT::IntType)).integer;
        M.values.pop_back();

        int val1 = dynamic_cast<IntValue&>(*M.get_value(VT::IntType)).integer;
        M.values.pop_back();

        M.values.emplace_back(new IntValue(val1 * val2));
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
