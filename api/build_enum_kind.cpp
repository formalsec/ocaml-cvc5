#include <iostream>
#include <sstream>
#include <cstring>
#include <cvc5/cvc5.h>
#include <cvc5/cvc5_kind.h>

using namespace cvc5;

extern "C" void build_enum_kind(){
  std::stringstream type_stream, to_string_stream;
  std::stringstream to_cpp_stream, of_cpp_stream;
  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  to_cpp_stream << "let to_cpp = function" << std::endl;
  of_cpp_stream << "let of_cpp = function" << std::endl;
  for (int i = 0; i < (int)Kind::LAST_KIND; i += 1) {
    Kind k = (Kind)i;
    std::string ln(kindToString(k));
    std::string name(ln);
    for (int j = 1; j < name.length(); j += 1)
      name[j] = std::tolower(name[j]);
    type_stream << "  | " << name << std::endl;
    to_string_stream <<
      "  | " << name << " -> " << '"' << ln << '"' << std::endl;
    to_cpp_stream <<
      "  | " << name << " -> " << i << std::endl;
    of_cpp_stream << "  | " << i << " -> " << name << std::endl;
  }
  of_cpp_stream << "  | _ -> assert false" << std::endl;
  std::cout << type_stream.str() << std::endl
	    << to_string_stream.str() << std::endl
	    << to_cpp_stream.str() << std::endl
	    << of_cpp_stream.str();
}