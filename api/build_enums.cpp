/* SPDX-License-Identifier: MIT */ 
/* Copyright (C) 2024-2025 formalsec */
/* Written by Joao Pereira */

#include <cctype>
#include <cstring>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <cvc5/cvc5.h>
#include <cvc5/cvc5_kind.h>
#include <cvc5/cvc5_types.h>
#include <cvc5/cvc5_proof_rule.h>

using namespace cvc5;

template <typename Enum>
static void emit_enum_module(const std::string& module_name,
                             const std::vector<Enum>& values)
{
  std::stringstream type_stream, to_string_stream;
  std::stringstream to_cpp_stream, of_cpp_stream;
  type_stream << "type t =" << std::endl;
  to_string_stream << "let to_string = function" << std::endl;
  to_cpp_stream << "let to_cpp = function" << std::endl;
  of_cpp_stream << "let of_cpp = function" << std::endl;

  for (Enum value : values)
  {
    int idx = static_cast<int>(value);
    std::stringstream ss;
    ss << value;
    std::string raw_name(ss.str());
    std::string ocaml_name(raw_name);
    if (!ocaml_name.empty())
    {
      ocaml_name[0] = std::toupper(ocaml_name[0]);
    }
    for (size_t j = 1; j < ocaml_name.length(); ++j)
    {
      ocaml_name[j] = std::tolower(ocaml_name[j]);
    }
    type_stream << "  | " << ocaml_name << std::endl;
    to_string_stream << "  | " << ocaml_name << " -> " << '"' << raw_name
                     << '"' << std::endl;
    to_cpp_stream << "  | " << ocaml_name << " -> " << idx << std::endl;
    of_cpp_stream << "  | " << idx << " -> " << ocaml_name << std::endl;
  }

  of_cpp_stream << "  | _ -> assert false" << std::endl;
  std::cout << "module " << module_name << " = struct" << std::endl
            << type_stream.str() << std::endl
            << to_string_stream.str() << std::endl
            << to_cpp_stream.str() << std::endl
            << of_cpp_stream.str() << "end" << std::endl;
}

extern "C" void build_enums(){
  std::vector<Kind> kinds;
  for (int i = 0; i < (int)Kind::LAST_KIND; i += 1) {
    kinds.push_back((Kind)i);
  }
  emit_enum_module("Kind", kinds);

  std::vector<RoundingMode> rounding_modes;
  for (int i = 0; i < 5; i += 1){
    rounding_modes.push_back((RoundingMode)i);
  }
  emit_enum_module("RoundingMode", rounding_modes);

  std::vector<UnknownExplanation> unknown_explanations;
  for (int i = 0; i < 10; i += 1){
    unknown_explanations.push_back((UnknownExplanation)i);
  }
  emit_enum_module("UnknownExplanation", unknown_explanations);

  emit_enum_module("BlockModelsMode",
                    std::vector<modes::BlockModelsMode>{
                        modes::BlockModelsMode::LITERALS,
                        modes::BlockModelsMode::VALUES,
                    });
  emit_enum_module("LearnedLitType",
                    std::vector<modes::LearnedLitType>{
                        modes::LearnedLitType::PREPROCESS_SOLVED,
                        modes::LearnedLitType::PREPROCESS,
                        modes::LearnedLitType::INPUT,
                        modes::LearnedLitType::SOLVABLE,
                        modes::LearnedLitType::CONSTANT_PROP,
                        modes::LearnedLitType::INTERNAL,
                        modes::LearnedLitType::UNKNOWN,
                    });
  emit_enum_module("ProofComponent",
                    std::vector<modes::ProofComponent>{
                        modes::ProofComponent::RAW_PREPROCESS,
                        modes::ProofComponent::PREPROCESS,
                        modes::ProofComponent::SAT,
                        modes::ProofComponent::THEORY_LEMMAS,
                        modes::ProofComponent::FULL,
                    });
  emit_enum_module("ProofFormat",
                    std::vector<modes::ProofFormat>{
                        modes::ProofFormat::NONE,
                        modes::ProofFormat::DOT,
                        modes::ProofFormat::LFSC,
                        modes::ProofFormat::ALETHE,
                        modes::ProofFormat::CPC,
                        modes::ProofFormat::DEFAULT,
                    });
  emit_enum_module("FindSynthTarget",
                    std::vector<modes::FindSynthTarget>{
                        modes::FindSynthTarget::ENUM,
                        modes::FindSynthTarget::REWRITE,
                        modes::FindSynthTarget::REWRITE_UNSOUND,
                        modes::FindSynthTarget::REWRITE_INPUT,
                        modes::FindSynthTarget::QUERY,
                    });
  emit_enum_module("OptionCategory",
                    std::vector<modes::OptionCategory>{
                        modes::OptionCategory::REGULAR,
                        modes::OptionCategory::EXPERT,
                        modes::OptionCategory::COMMON,
                        modes::OptionCategory::UNDOCUMENTED,
                    });
  emit_enum_module("InputLanguage",
                    std::vector<modes::InputLanguage>{
                        modes::InputLanguage::SMT_LIB_2_6,
                        modes::InputLanguage::SYGUS_2_1,
                        modes::InputLanguage::UNKNOWN,
                    });
}
