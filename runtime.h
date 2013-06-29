#pragma once

#include<cstdint>
#include<string>
#include<stdexcept>
#include<vector>
#include<memory>

enum Code {
  ACCESS = 1,
  FUNCTION = 2,
  SAVE = 3,
  RESTORE = 4,
  CALL = 5,
  RETURN = 6,
  HALT = 7,
  CONSTINT = 16,
  ADD = 17,
  MUL = 18,
  BRANCHNZ_REL = 32,
  JUMP_REL = 33
};

typedef std::uint64_t addr_t;
typedef std::uint64_t code_t;
typedef std::int64_t diff_t;

struct Value; //forward declaration

enum class EnvType { NilType, ConsType };

struct Env {
  const EnvType type;
protected:
  Env(const EnvType& _type) : type(_type) {}
public:
  Env(const Env&) = delete;
  Env(Env&&) = delete;
  virtual ~Env() {}
};

struct EnvNil : Env {
  EnvNil() : Env(EnvType::NilType) {}
  EnvNil(const EnvNil&) = default;
  EnvNil(EnvNil&&) = default;
  ~EnvNil() = default;
};

struct EnvCons : Env {
  std::shared_ptr<Value> car;
  std::shared_ptr<Env> cdr;
  EnvCons(const std::shared_ptr<Value>& _car,
          const std::shared_ptr<Env>& _cdr)
    : Env(EnvType::ConsType), car(_car), cdr(_cdr) {}
  EnvCons(const EnvCons&) = default;
  EnvCons(EnvCons&&) = default;
  ~EnvCons() = default;
};

std::shared_ptr<Env> Nil();
std::shared_ptr<Env> Cons(const std::shared_ptr<Value>& _car,
                          const std::shared_ptr<Env>& _cdr);

enum class ValueType { ClosureType, IntType };
std::string show(ValueType type);

struct Value {
  const ValueType type;
protected:
  Value(const ValueType& _type) : type(_type) {}
public:
  virtual ~Value() {}
};

struct Closure : Value {
  addr_t code_addr;
  std::shared_ptr<Env> env;
  Closure(const addr_t& _code_addr,
          const std::shared_ptr<Env>& _env)
    : Value(ValueType::ClosureType), code_addr(_code_addr), env(_env) {}
  Closure(const Closure&) = default;
  Closure(Closure&&) = default;
  ~Closure() = default;
};

struct IntValue : Value {
  int integer;
  IntValue(const int& _integer)
    : Value(ValueType::IntType), integer(_integer) {}
  IntValue(const IntValue&) = default;
  IntValue(IntValue&&) = default;
  ~IntValue() = default;
};

enum class StackType { AddrType, EnvType };

struct Stack {
  StackType type;
//  union {
    addr_t addr;
    std::shared_ptr<Env> env;
/*  };
  Stack(addr_t _addr) : type(StackType::AddrType), addr(_addr) {}
  Stack(const std::shared_ptr<Env>& _env)
    : type(StackType::EnvType), env(_env) {}
  Stack(const Stack& that) {
    this->type = that.type;
    if (that.type == StackType::EnvType) {
      new (&this->env) std::shared_ptr<Env>(that.env);
    } else {
      this->addr = that.addr;
    }
  }
  Stack(Stack&&) = delete;
  Stack& operator=(const Stack& that) {
    this->~Stack();
    this->type = that.type;
    switch (that.type) {
    case StackType::AddrType:
      this->addr = that.addr;
      break;
    case StackType::EnvType:
      new (&this->env) std::shared_ptr<Env>(that.env);
      break;
    }
    return *this;
  }
  ~Stack() noexcept(true) {
    if (this->type == StackType::EnvType) {
      this->env.~shared_ptr<Env>();
    }
  }*/
  Stack(addr_t _addr) : type(StackType::AddrType), addr(_addr), env(nullptr) {}
  Stack(const std::shared_ptr<Env>& _env)
    : type(StackType::EnvType), addr(0), env(_env) {}
};

struct Machine {
  addr_t eip;
  size_t code_len;
  const code_t *code;
  std::vector<std::shared_ptr<Value>> values;
  std::vector<Stack> stk;
  std::shared_ptr<Env> env;
  template<typename T> T fetch() {
    if (this->eip == this->code_len) {
      throw std::runtime_error("Machine::fetch: unexpected end of code");
    }
    T t = static_cast<T>(this->code[this->eip]);
    this->eip = this->eip + 1;
    return t;
  }

  std::shared_ptr<Value> get_value() {
    if (this->values.empty()) {
      throw std::runtime_error("Machine::get_value: the value stack is empty");
    }
    return this->values.back();
  }

  std::shared_ptr<Value> get_value(ValueType type) {
    if (this->values.empty()) {
      throw std::runtime_error("Machine::get_value: the value stack is empty");
    }
    std::shared_ptr<Value>& val = this->values.back();
    if (val->type != type) {
      throw std::runtime_error(
              std::string("Machine::get_value: type error; expected '")
              + show(type) + "' but got '" + show(val->type) + "'");
    }
    return val;
  }
};

std::string show(const std::shared_ptr<Value>& val);
std::string show(Machine& M);
std::shared_ptr<Value> run(const code_t *codes, size_t code_len);
