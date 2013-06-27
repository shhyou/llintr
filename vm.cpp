#include <algorithm>
#include <iostream>
#include <cstdint>
#include <memory>
#include <vector>
#include <string>
#include "runtime.h"

using namespace std;

vector<code_t> get_input() {
  int64_t c;
  vector<code_t> res;
  while (cin >> c) {
    res.push_back(c);
  }
  return move(res);
}

vector<string> disassemble(const vector<code_t>& code) {
  vector<string> res;
  for (auto it=code.begin(); it<code.end(); ++it) {
    switch (*it) {
    case ACCESS:
      ++it;
      res.push_back(string("access ") + to_string(*it));
      break;
    case FUNCTION:
      ++it;
      res.push_back(string("function ") + to_string(*it));
      break;
    case SAVE:
      res.push_back("save");
      break;
    case RESTORE:
      res.push_back("restore");
      break;
    case CALL:
      res.push_back("call");
      break;
    case RETURN:
      res.push_back("return");
      break;
    case HALT:
      res.push_back("halt");
      break;
    case CONSTINT:
      ++it;
      res.push_back(string("constint ") + to_string(static_cast<int64_t>(*it)));
      break;
    case ADD:
      res.push_back("add");
      break;
    case BRANCHNZ_REL:
      ++it;
      res.push_back(string("jnz_rel ") + to_string(*it));
      break;
    case JUMP_REL:
      ++it;
      res.push_back(string("jmp_rel ") + to_string(*it));
      break;
    default:
      res.push_back(string("Unrecognized op-code: ") + to_string(*it));
    }
  }
  return move(res);
}

int main() {
  try {
    vector<code_t> code(get_input());
    vector<string> disasm(disassemble(code));
    for (string& str : disasm) {
      cout << str << endl;
    }
    shared_ptr<Value> res = run(code.data(), code.size());
    if (not res) {
      cout << "result is null" << endl;
    } else {
      cout << show(res->type) << ": ";
      switch (res->type) {
      case ValueType::IntType:
        cout << dynamic_cast<IntValue*>(res.get())->integer << endl;
        break;
      case ValueType::ClosureType:
        cout << "<function>" << endl;
        break;
      default:
        cout << "unknown value type" << endl;
      }
    }
  } catch (const exception& e) {
    cout << "***Exception: " << e.what() << endl;
  }
  return 0;
}
