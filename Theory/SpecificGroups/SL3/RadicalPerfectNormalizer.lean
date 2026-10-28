module
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
/-!
# Perfect normal subgroups in binary SL₃ radical normalizers

Each affine point or plane local is perfect with quasisimple two-core
quotient, hence is a C-component. Its minimality identifies every nontrivial
perfect normal subgroup of the corresponding parabolic with that literal
local. Combining this with the radical-normalizer theorem marks both the
normalizer and the specified subgroup in the same natural-module basis.

This supplies the intrinsic recognition required by the original L-image
in the rank-one block argument. No abstract affine isomorphism is substituted
for its actual subgroup placement.
Source: Aschbacher–Smith C.4.5–7, printed pp.152–153.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.RadicalNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem isPPerfect_of_perfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem perfect_normal_eq_residual {G : Type*} [Group G] [Finite G]
    (B P L : Subgroup G) [Group.IsPerfect B] (hne : B ≠ ⊥) (hBP : B ≤ P)
    (hPB : P ≤ normalizer (B : Set G))
    (he : (solvableResidual P).map P.subtype = L)
    [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)] : B = L := by
  have hBL : B ≤ L := he ▸ le_map_solvableResidual_of_isPerfect B P hBP
  have hLP : L ≤ P := he ▸ map_subtype_le (solvableResidual P)
  let : (B.subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBL).mpr (hLP.trans hPB)
  let : Group.IsPerfect (B.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hBL).symm.toMonoidHom)
      (subgroupOfEquivOfLe hBL).symm.surjective
  have hb : B.subgroupOf L ≠ ⊥ := by
    intro hb
    have hh := congrArg (Subgroup.map L.subtype) hb
    rw [map_subgroupOf_eq_of_le hBL,Subgroup.map_bot] at hh
    exact hne hh
  have hc := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 L) pCore_isPGroup (isPPerfect_of_perfect (G := L))
  have ht : B.subgroupOf L = ⊤ := top_unique (hc.minimal _ le_top hb inferInstance
    (inferInstance : (B.subgroupOf L).Normal).isSubnormal)
  exact le_antisymm hBL (subgroupOf_eq_top.mp ht)

/-- A nontrivial perfect normal subgroup of the full point parabolic is its
literal vector stabilizer, not merely an abstract affine group. -/
theorem perfect_normal_point_eq (hcard : 4 ≤ Nat.card F)
    (B : Subgroup SL(3,F)) [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBP : B ≤ pointParabolicSL F)
    (hPB : pointParabolicSL F ≤ normalizer (B : Set SL(3,F))) :
    B = pointLocalSL F := by
  let := pointLocalSL_isPerfect F hcard
  let : IsQuasisimple (pointLocalSL F ⧸ pCore 2 (pointLocalSL F)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by omega) (pointLocalSLCoreQuotientEquiv F)
  exact perfect_normal_eq_residual B _ _ hne hBP hPB (pointParabolicSL_residual F hcard)

/-- The analogous normal-subgroup recognition for the full plane parabolic. -/
theorem perfect_normal_line_eq (hcard : 4 ≤ Nat.card F)
    (B : Subgroup SL(3,F)) [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBP : B ≤ lineParabolicSL F)
    (hPB : lineParabolicSL F ≤ normalizer (B : Set SL(3,F))) :
    B = lineLocalSL F := by
  let := lineLocalSL_isPerfect F hcard
  let : IsQuasisimple (lineLocalSL F ⧸ pCore 2 (lineLocalSL F)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by omega) (lineLocalSLCoreQuotientEquiv F)
  exact perfect_normal_eq_residual B _ _ hne hBP hPB (lineParabolicSL_residual F hcard)
/-- Simultaneous marking of the radical normalizer and its given nontrivial
perfect normal subgroup. The same linear change of basis supplies both. -/
theorem radical_perfect_normal_frame
    (R B : Subgroup SL(3,F)) (hR : R.IsPRadical 2)
    [Group.IsPerfect B] (hne : B ≠ ⊥)
    (hBN : B ≤ normalizer (R : Set SL(3,F)))
    (hNB : normalizer (R : Set SL(3,F)) ≤ normalizer (B : Set SL(3,F)))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      ((normalizer (R : Set SL(3,F))).map
          (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom = pointParabolicSL F ∧
        B.map (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom = pointLocalSL F) ∨
      ((normalizer (R : Set SL(3,F))).map
          (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom = lineParabolicSL F ∧
        B.map (Matrix.HigherLinear.SubspaceTransport.slConj e).toMonoidHom = lineLocalSL F) := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  obtain ⟨e,he⟩ := radical_normalizer_frame_of_perfect R B hR hne hBN hn hF
  let a := Matrix.HigherLinear.SubspaceTransport.slConj e
  let C := B.map a.toMonoidHom
  let : Group.IsPerfect C := Group.IsPerfect.map a.toMonoidHom
  have hC : C ≠ ⊥ := fun hc => hne ((B.map_eq_bot_iff_of_injective a.injective).mp hc)
  have hCN : C ≤ (normalizer (R : Set SL(3,F))).map a.toMonoidHom := map_mono hBN
  have hNC : (normalizer (R : Set SL(3,F))).map a.toMonoidHom ≤ normalizer (C : Set SL(3,F)) := by
    rw [←map_equiv_normalizer_eq B a]
    exact map_mono hNB
  refine ⟨e,?_⟩
  rcases he with he | he
  · exact Or.inl ⟨he,perfect_normal_point_eq hcard C hC (he ▸ hCN) (he ▸ hNC)⟩
  · exact Or.inr ⟨he,perfect_normal_line_eq hcard C hC (he ▸ hCN) (he ▸ hNC)⟩
end Matrix.PSL3.LinearThree.RadicalNormalizer
