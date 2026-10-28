module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.FixedMovedComplement


/-!
# Invariant summands and the original central involution line

A nonzero invariant binary subspace of a normal elementary subgroup meets
the centre of the original Sylow two-subgroup. The resulting vector is an
actual central involution in G. If Ω₁Z(T) has order two, two such invariant
subspaces cannot be disjoint and nonzero: their central vectors coincide.

This proves the central-line obstruction used in Aschbacher–Smith 14.1.7,
printed p.977. The action is the literal M/C_M(U) conjugation action.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

private theorem exists_central_involution_in_subspace
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (W : Submodule (ZMod 2) (Additive U)) (hne : W ≠ ⊥)
    (hstable : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M))) ≤
        subspaceStabilizer (NormalElementaryQuotient.representation U
          (QuotientGroup.mk' (centralizer (U : Set M)))
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) W) :
    ∃ v : Additive U, v ∈ W ∧ v ≠ 0 ∧ ((v.toMul : M) : G) ∈ centralInvolutions T := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let S := T.subtype hTM
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  let act : MulAction S W := {
    smul s w := ⟨ρ (q s) w, (hstable (mem_map_of_mem q s.property) w).2 w.property⟩
    one_smul w := by
      apply Subtype.ext
      change ρ (q 1) (w : Additive U) = w
      simp
    mul_smul s t w := by
      apply Subtype.ext
      change ρ (q ((s : M) * t)) (w : Additive U) = ρ (q s) (ρ (q t) w)
      simp only [map_mul, Module.End.mul_apply] }
  let : MulAction S W := act
  have hcard : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
    exact dvd_pow_self 2 (Nat.ne_of_gt (Module.finrank_pos (R := ZMod 2) (M := W)))
  have hz : (0 : W) ∈ MulAction.fixedPoints S W := by
    apply MulAction.mem_fixedPoints.mpr
    intro s
    apply Subtype.ext
    exact map_zero (ρ (q s))
  obtain ⟨v, hv, hvne⟩ := S.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := W) hcard hz
  refine ⟨v, v.property, (fun he => hvne (Subtype.ext he).symm), ?_⟩
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  have hUS : U ≤ (S : Subgroup M) :=
    (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S
  refine ⟨hUS v.val.toMul.property, ?_, ?_⟩
  · exact congrArg M.subtype
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ v.val.toMul.property)
  · intro t ht
    let s : S := ⟨⟨t, hTM ht⟩, ht⟩
    have hf : ρ (q (s : M)) (v : Additive U) = v :=
      congrArg Subtype.val (MulAction.mem_fixedPoints.mp hv s)
    have he := congrArg (fun w : Additive U => (w.toMul : M)) hf
    rw [NormalElementaryQuotient.representation_apply] at he
    exact congrArg M.subtype (mul_inv_eq_iff_eq_mul.mp he)

/-- A central involution line prevents two disjoint nonzero invariant summands. -/
theorem disjoint_stable_subspaces_of_central_order_two
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hZ : Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (W F : Submodule (ZMod 2) (Additive U)) (hd : Disjoint W F)
    (hW : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M))) ≤
        subspaceStabilizer (NormalElementaryQuotient.representation U
          (QuotientGroup.mk' (centralizer (U : Set M)))
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) W)
    (hF : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M))) ≤
        subspaceStabilizer (NormalElementaryQuotient.representation U
          (QuotientGroup.mk' (centralizer (U : Set M)))
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) F) : W = ⊥ ∨ F = ⊥ := by
  by_contra hn
  push Not at hn
  obtain ⟨w, hw, hw0, hwZ⟩ := exists_central_involution_in_subspace T hTM U W hn.1 hW
  obtain ⟨f, hf, hf0, hfZ⟩ := exists_central_involution_in_subspace T hTM U F hn.2 hF
  have hwne : (⟨((w.toMul : M) : G), hwZ⟩ : centralInvolutions T) ≠ 1 := by
    intro he
    apply hw0
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralInvolutions T => (z : G)) he
  have hfne : (⟨((f.toMul : M) : G), hfZ⟩ : centralInvolutions T) ≠ 1 := by
    intro he
    apply hf0
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralInvolutions T => (z : G)) he
  have he := ((Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp hZ).unique hwne hfne
  have hwf : w = f := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralInvolutions T => (z : G)) he
  exact hw0 (Submodule.disjoint_def.mp hd w hw (hwf.symm ▸ hf))

end CFSG.Quasithin.Chapter15.Section03.InitialSource
