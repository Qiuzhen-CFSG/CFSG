module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.Binary
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The doubled binary natural module

An elementary abelian subgroup of SL₃(2) has rank at most two: its Sylow
overgroup has order eight and contains an element whose square is not one.
Each nontrivial subgroup has positive fixed codimension on the faithful
natural module. Codimensions add on the two natural summands, excluding
strong offending everywhere, without an assumed ratio bound.

Source: Aschbacher–Smith, combined manuscript, B.5.1(1ii), printed p.99,
and the L₃(2) branch on printed p.1145.
-/

public section

open Subgroup Representation Representation.BinaryOffender Matrix.PSL3Two
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.BinaryDouble
private noncomputable def B : Sylow 2 SL := Sylow.ofCard borelSL (by
  rw [card_borelSL,card_SL]
  decide +kernel)
private theorem card_sylow (S : Sylow 2 SL) : Nat.card S = 8 := by
  rw [S.card_eq_multiplicity,card_SL]
  decide +kernel
private def t : B := ⟨⟨!![1,1,0;0,1,1;0,0,1],by decide⟩,
  (mem_borelSL_iff _).mpr (by decide)⟩
private theorem t_square : t ^ 2 ≠ 1 := by
  intro he
  have h := congrArg (fun x : B => x.val.val 0 2) he
  exact (by decide : (1 : ZMod 2) ≠ 0) h

theorem elementary_rank_le_two {A : Subgroup SL} (hA : IsElementaryTwo A) :
    rank A ≤ 2 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hc : Nat.card A ≤ 8 := (Subgroup.card_le_of_le hS).trans_eq (card_sylow S)
  have hn : Nat.card A ≠ 8 := by
    intro he
    have hAS : A = (S : Subgroup SL) := Subgroup.eq_of_le_of_card_ge hS (by rw [card_sylow,he])
    have hsquare (x : S) : x ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (A := A) x.val (by rw [hAS]; exact x.property)
    let e : S ≃* B := S.equiv B
    apply t_square
    have hh := congrArg e (hsquare (e.symm t))
    simpa only [map_pow,map_one,e.apply_symm_apply] using hh
  have hr : rank A < 3 := Nat.log_lt_of_lt_pow' (by decide : 3 ≠ 0) (lt_of_le_of_ne hc hn)
  omega

private theorem faithful : Function.Injective Binary.natural := by
  intro g h he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  exact LinearEquiv.toLinearMap_injective he

theorem not_strong_double (A : Subgroup SL) :
    ¬ IsStrongOffender (Binary.natural.prod Binary.natural) A := by
  intro hs
  have hr := elementary_rank_le_two hs.1
  have hp := fixedCodim_pos_of_faithful Binary.natural faithful hs.1.1
  have hh := hs.2
  rw [fixedCodim_prod] at hh
  omega
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.BinaryDouble
