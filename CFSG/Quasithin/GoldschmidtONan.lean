module

public import Theory.Representation.GoldschmidtONan.Assembly
public import CFSG.Quasithin.GoldschmidtONan.OddTerminal

/-!
# The Goldschmidt–O’Nan classification of TI modules

The actual Odd Order Theorem instantiates the reusable induction proof.
Thus the original finite faithful binary action with its cyclic actor and
TI fixed-space orbit satisfies one of the four exact source alternatives.
No geometry, induction, solvability or classification premise remains.
The two irreducibility consequences use this completed source theorem.

Source: GLS, Number 2, Chapter C, Definition 14.1 and Proposition 14.2,
`refs/KGroup/GLS2/ChapterC.tex`. Applications include Aschbacher–Smith 2.2.2
and the Even Type argument in 16.5.1, 16.5.4 and 16.5.13.
-/

public section

namespace CFSG.Quasithin.GoldschmidtONan

open Representation Representation.GoldschmidtONan
open Representation.BinaryOffender

universe u v
variable {X : Type u} {V : Type v} [Group X] [Finite X]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

theorem alternatives (h : Input ρ Y) : Alternatives ρ Y :=
  h.alternatives_of_odd_order_solvable (fun H _ _ hodd => odd_order_theorem H hodd)

theorem swapped_or_exceptional_of_irreducible [IsIrreducible ρ] (h : Input ρ Y) :
    SwappedCase ρ Y ∨ ExceptionalCase ρ Y :=
  h.swapped_or_exceptional_of_irreducible (alternatives h)

theorem model_of_irreducible_of_no_index_two [IsIrreducible ρ] (h : Input ρ Y)
    (hindex : ∀ H : Subgroup X, H.Normal → H.index ≠ 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1 ∧
      Module.finrank (ZMod 2) V = 3 ∧ Nonempty (X ≃* Frobenius21.Model) :=
  h.model_of_irreducible_of_no_index_two (alternatives h) hindex

end CFSG.Quasithin.GoldschmidtONan
