/*------------------------------------------------------------------------*
 *  Copyright (C) 2024 João Pereira                                       *
 *                                                                        *
 *  This file is part of ocaml-cvc5                                       *
 *                                                                        *
 *  ocaml-cvc5 is free software: you can redistribute it and/or modify    *
 *  it under the terms of the GNU General Public License as published     *
 *  by the Free Software Foundation, either version 3 of the License,     *
 *  or (at your option) any later version.                                *
 *                                                                        *
 *  ocaml-cvc5 is distributed in the hope that it will be useful,         *
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of        *
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *
 *  See the GNU General Public License for more details.                  *
 *                                                                        *
 *  You should have received a copy of the GNU General Public License     *
 *  along with ocaml-cvc5. If not, see <http://www.gnu.org/licenses/>.    *
 *------------------------------------------------------------------------*/

#include <iostream>
#include <sstream>
#include <cstring>
#include <string>
#include <cvc5/cvc5.h>
#include <cvc5/cvc5_kind.h>
#include <cvc5/cvc5_types.h>
#include <cvc5/cvc5_proof_rule.h>

using namespace cvc5;

extern "C" void build_enums(){
  std::stringstream type_stream, to_string_stream;
  std::stringstream to_cpp_stream, of_cpp_stream;
  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  to_cpp_stream << "let to_cpp = function" << std::endl;
  of_cpp_stream << "let of_cpp = function" << std::endl;
  for (int i = 0; i < (int)Kind::LAST_KIND; i += 1) {
    std::stringstream ss;
    ss << (Kind)i;
    std::string ln(ss.str());
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
  std::cout << "module Kind = struct" << std::endl
      << type_stream.str() << std::endl
	    << to_string_stream.str() << std::endl
	    << to_cpp_stream.str() << std::endl
	    << of_cpp_stream.str() << "end" << std::endl;

  type_stream.str("");
  to_string_stream.str("");
  to_cpp_stream.str("");
  of_cpp_stream.str("");

  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  to_cpp_stream << "let to_cpp = function" << std::endl;
  of_cpp_stream << "let of_cpp = function" << std::endl;
  for (int i = 0; i < 5; i += 1){
    std::stringstream ss;
    ss << (RoundingMode)i;
    std::string ln(ss.str());
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
  std::cout << "module RoundingMode = struct" << std::endl
      << type_stream.str() << std::endl
	    << to_string_stream.str() << std::endl
	    << to_cpp_stream.str() << std::endl
	    << of_cpp_stream.str() << "end" << std::endl;

  type_stream.str("");
  to_string_stream.str("");
  to_cpp_stream.str("");
  of_cpp_stream.str("");

  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  to_cpp_stream << "let to_cpp = function" << std::endl;
  of_cpp_stream << "let of_cpp = function" << std::endl;
  for (int i = 0; i < 10; i += 1){
    std::stringstream ss;
    ss << (UnknownExplanation)i;
    std::string ln(ss.str());
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
  std::cout << "module UnknownExplanation = struct" << std::endl
      << type_stream.str() << std::endl
	    << to_string_stream.str() << std::endl
	    << to_cpp_stream.str() << std::endl
	    << of_cpp_stream.str() << "end" << std::endl;
}