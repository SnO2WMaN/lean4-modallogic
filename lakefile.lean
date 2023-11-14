import Lake
open Lake DSL

package «ModalLogic» {
  -- add package configuration options here
}

lean_lib «ModalLogic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "2865aeda84135fad248864181270996cbf195fe2"
require aesop from git "https://github.com/JLimperg/aesop"

require logic from git "https://github.com/iehality/lean4-logic" @ "master"
