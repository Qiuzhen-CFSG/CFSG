module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Identifying the binary quotient of the ordinary component

The normal component maps nontrivially through the ambient two-core
quotient: a trivial image would make the perfect component a two-group.
Its image in the actual automorphism group is perfect and normal.
The proved cyclicity of the binary outer group places it inside the
simple inner subgroup, where normality forces equality. The kernel is
exactly the component's intrinsic two-core by subnormal core transport.

This identifies K/O₂(K), without asserting that K has trivial center.
The comparison with all six alternatives of 1.1.5 is still required to
identify K itself and its ambient inner actions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164; 1.1.5, printed pp.501–503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels

private theorem simple_perfect_center {S : Type*} [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S] : center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h)).elim

private noncomputable def innerEquiv {S : Type*} [Group S]
    (hcenter : center S = ⊥) : S ≃* MulAut.innerSubgroup S := by
  apply MulEquiv.ofBijective (MulAut.conj (G := S)).rangeRestrict
  refine ⟨?_, MonoidHom.rangeRestrict_surjective _⟩
  intro x y hxy
  have hconj : MulAut.conj x = MulAut.conj y := congrArg Subtype.val hxy
  have hz : y⁻¹ * x ∈ center S := by
    rw [mem_center_iff]
    intro z
    have he := MulEquiv.congr_fun hconj z
    change x * z * x⁻¹ = y * z * y⁻¹ at he
    have he' : x * z = y * z * y⁻¹ * x := (mul_inv_eq_iff_eq_mul).mp he
    calc
      z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹ * x) := by group
      _ = y⁻¹ * (x * z) := by rw [he']
      _ = y⁻¹ * x * z := by group
  have h1 : y⁻¹ * x = 1 := by simpa only [hcenter, mem_bot] using hz
  exact (inv_mul_eq_one.mp h1).symm

private theorem normal_perfect_in_aut {S : Type*} [Group S] [IsSimpleGroup S]
    [Group.IsPerfect S] [IsCyclic (MulAut.Outer S)] (J : Subgroup (MulAut S))
    [J.Normal] [Group.IsPerfect J] (hne : J ≠ ⊥) : J = MulAut.innerSubgroup S := by
  let e := innerEquiv (simple_perfect_center (S := S))
  let : IsSimpleGroup (MulAut.innerSubgroup S) := e.symm.isSimpleGroup
  have hle : J ≤ MulAut.innerSubgroup S := by
    have hout : commutator (MulAut S) ≤ MulAut.innerSubgroup S :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    exact (commutator_eq_self (H := J)) ▸ ((commutator_mono le_top le_top).trans hout)
  rcases (inferInstance : (J.subgroupOf (MulAut.innerSubgroup S)).Normal).eq_bot_or_eq_top
      with hb | ht
  · have he := congrArg (Subgroup.map (MulAut.innerSubgroup S).subtype) hb
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at he
    exact (hne he).elim
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

private noncomputable def normalComponentQuotientEquiv {A S : Type*}
    [Group A] [Finite A] [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    [IsCyclic (MulAut.Outer S)] (L : Subgroup A) [L.Normal]
    (hc : IsComponent A L) (e : A ⧸ pCore 2 A ≃* MulAut S) :
    (L ⧸ pCore 2 L) ≃* S := by
  let := hc.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let J := L.map f
  let : J.Normal := Subgroup.Normal.map inferInstance f hf
  let : Group.IsPerfect J := Group.IsPerfect.map f
  have hkf : f.ker = pCore 2 A := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 A) x) = 1 ↔ x ∈ pCore 2 A
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hne : J ≠ ⊥ := by
    intro hb
    have hle : L ≤ pCore 2 A := by
      intro x hx
      have hfx : f x = 1 := by
        exact mem_bot.mp (hb ▸ (mem_map_of_mem f hx : f x ∈ J))
      exact hkf ▸ (show x ∈ f.ker from hfx)
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let : Group.IsNilpotent L := (pCore_isPGroup (p := 2) (G := A)).to_le hle |>.isNilpotent
    exact Group.IsPerfect.not_isSolvable L inferInstance
  have hJ := normal_perfect_in_aut J hne
  let q := f.subgroupMap L
  have hk : q.ker = pCore 2 L := by
    rw [Subgroup.ker_subgroupMap]
    rw [hkf]
    exact (pCore_subnormal_eq_comap 2 hc.1).symm
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective q (f.subgroupMap_surjective L)).trans
      ((MulEquiv.subgroupCongr hJ).trans (innerEquiv (simple_perfect_center (S := S))).symm))

variable {G : Type*} [Group G] [Finite G]
open OrdinaryReduction

/-- The actual binary PSL quotient of the normal ordinary component. -/
theorem source_binary_quotient {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (hc : IsComponent H (K.subgroupOf H))
    (hm : BinaryAutomorphismModel H) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2 := by
  obtain ⟨n, hn, F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let eS := Atlas.fieldEquivPSL n eF
  let : IsSimpleGroup PSL(n, ZMod 2) := Atlas.psl_simple_high_rank n (by omega)
  let : Group.IsPerfect PSL(n, ZMod 2) := Atlas.psl_perfect n (by omega)
  let : IsCyclic (MulAut.Outer PSL(n, ZMod 2)) := BinaryLinear.OuterCyclic.psl_outer_isCyclic hn
  let : (K.subgroupOf H).Normal := by
    rw [s.closure]
    exact EmbeddingReduction.normalClosureIn_normal _ _
  let eQ := normalComponentQuotientEquiv (K.subgroupOf H) hc (e.trans (MulAut.congr eS))
  have hKH : K ≤ H := s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  let eK := subgroupOfEquivOfLe hKH
  let eQK := QuotientGroup.congr (pCore 2 (K.subgroupOf H)) (pCore 2 K) eK
    (pCore_map_iso 2 eK)
  exact ⟨n, hn, ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨eQK.symm.trans eQ⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
