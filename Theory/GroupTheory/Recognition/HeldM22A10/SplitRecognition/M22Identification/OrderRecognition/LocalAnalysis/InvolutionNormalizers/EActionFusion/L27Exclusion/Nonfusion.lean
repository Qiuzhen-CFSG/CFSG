module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.VectorFusion

/-!
# The seven- and eight-point orbits in the order-168 branch

Orbit-stabilizer makes the marked involution's N(E)-orbit have size seven.
Printed z₂ has eight distinct conjugates under the known local S4 action.
Any ambient conjugator from z₁ to z₂ normalizes E, so these counts prove
that z₁ and z₂ are not conjugate in G. The two normalizer orbits are disjoint
and avoid the identity; their sizes are therefore exactly seven and eight.
This gives |C_G(z₂) ∩ N(E)| = 336, without an abstract PSL2(7) identification.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, p.6. Printed z₂ is `CaseII.z 1`.
The eight local conjugates are counted by kernel reduction in TwistedModel.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private def zOneLocalOrbit : Finset TwistedModel :=
  Finset.univ.image fun s : SymmetricFour =>
    (SemidirectProduct.inr s : TwistedModel) * z 1 * (SemidirectProduct.inr s)⁻¹

private theorem zOneLocalOrbit_card : zOneLocalOrbit.card = 8 := by decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The marked involution has seven conjugates under its E-normalizer. -/
public theorem eNormalizerPoint_orbit_card_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k)).ncard = 7 := by
  rw [eNormalizerQuotient_card] at h168
  omega

/-- Printed z₂ as a point of the actual elementary subgroup E. -/
@[expose] public def eNormalizerZOnePoint : E D k := ⟨into D k (z 1), by
  rw [← modelE_map D k]
  exact mem_map_of_mem _ (z_mem_modelE 1)⟩

omit [Finite G] in
private theorem eNormalizerZOnePoint_ne_one : eNormalizerZOnePoint D k ≠ 1 := by
  intro h
  have he : z 1 = 1 := into_injective D k ((congrArg Subtype.val h).trans (map_one _).symm)
  have ho := z_order 1
  simp [he] at ho

private theorem z_one_orbit_card_ge : 8 ≤
    (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerZOnePoint D k)).ncard := by
  classical
  let N := normalizer (E D k : Set G)
  let O := MulAction.orbit N (eNormalizerZOnePoint D k)
  have hmem : ∀ v ∈ zOneLocalOrbit, ∃ x : O, ((x : E D k) : G) = into D k v := by
    intro v hv
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hv
    let a := (SemidirectProduct.inr s : TwistedModel)
    let n : N := ⟨into D k a, centralizer_le_normalizer_E D k (k a).property⟩
    refine ⟨⟨n • eNormalizerZOnePoint D k, MulAction.mem_orbit _ n⟩, ?_⟩
    change into D k a * into D k (z 1) * (into D k a)⁻¹ = _
    rw [map_mul, map_mul, map_inv]
  choose f hf using fun v : {v // v ∈ zOneLocalOrbit} => hmem v v.property
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply into_injective D k
    rw [← hf x, ← hf y, hxy]
  have hle := Nat.card_le_card_of_injective f hi
  rw [Nat.card_eq_fintype_card (α := {v // v ∈ zOneLocalOrbit}),
    Fintype.card_coe, zOneLocalOrbit_card] at hle
  exact hle

/-- Printed z₁ and z₂ are not conjugate even in the ambient group. -/
public theorem z_one_not_fused_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    ¬ IsConj D.z (into D k (z 1)) := by
  intro hfuse
  obtain ⟨g, hg⟩ := isConj_iff.mp hfuse
  let n : normalizer (E D k : Set G) :=
    ⟨g, z_one_conjugator_normalizes_E D k g hg⟩
  have hm : eNormalizerZOnePoint D k ∈
      MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) := by
    exact MulAction.mem_orbit_iff.mpr ⟨n, Subtype.ext hg⟩
  have he := MulAction.orbit_eq_iff.mpr hm
  have hle := z_one_orbit_card_ge D k
  rw [he, eNormalizerPoint_orbit_card_of_168 D k h168] at hle
  omega

/-- The second vector orbit contains exactly eight points. -/
public theorem eNormalizerZOnePoint_orbit_card_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerZOnePoint D k)).ncard = 8 := by
  apply le_antisymm ?_ (z_one_orbit_card_ge D k)
  have hsub : MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerZOnePoint D k) ⊆
      {1}ᶜ \ MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro hx1
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact eNormalizerZOnePoint_ne_one D k ((MulAction.injective g) (by simpa using hx1))
    · intro hy
      have he := (MulAction.orbit_eq_iff.mpr hx).symm.trans (MulAction.orbit_eq_iff.mpr hy)
      have hm : eNormalizerZOnePoint D k ∈
          MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) := by
        rw [← he]
        exact MulAction.mem_orbit_self _
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hm
      exact z_one_not_fused_of_168 D k h168
        (isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩)
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_sdiff (eNormalizerPoint_orbit_nonidentity D k),
    Set.ncard_compl, Set.ncard_singleton, E_card,
    eNormalizerPoint_orbit_card_of_168 D k h168] at hle
  exact hle

omit [Finite G] in
/-- The literal E-normalizer has order 16 · 168. -/
public theorem eNormalizer_card_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    Nat.card (normalizer (E D k : Set G)) = 2688 := by
  have hN := card_eq_card_quotient_mul_card_subgroup
    ((E D k).subgroupOf (normalizer (E D k : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe (E D k).le_normalizer).toEquiv, E_card] at hN
  change _ = Nat.card (eNormalizerQuotient D k) * 16 at hN
  rw [h168] at hN
  exact hN

/-- The centralizer of printed z₂ inside N(E) has order 336. -/
public theorem z_one_centralizer_inf_normalizer_card_of_168
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    Nat.card (centralizer ({into D k (z 1)} : Set G) ⊓
      normalizer (E D k : Set G) : Subgroup G) = 336 := by
  let N := normalizer (E D k : Set G)
  let C := centralizer ({into D k (z 1)} : Set G)
  have hs : MulAction.stabilizer N (eNormalizerZOnePoint D k) = C.subgroupOf N := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    change (⟨(g : G) * into D k (z 1) * (g : G)⁻¹, _⟩ : E D k) =
      eNormalizerZOnePoint D k ↔ (g : G) ∈ C
    rw [Subtype.ext_iff]
    change (g : G) * into D k (z 1) * (g : G)⁻¹ = into D k (z 1) ↔ _
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hc := (MulAction.stabilizer N (eNormalizerZOnePoint D k)).card_mul_index
  rw [MulAction.index_stabilizer, eNormalizerZOnePoint_orbit_card_of_168 D k h168,
    eNormalizer_card_of_168 D k h168, hs] at hc
  have he : Nat.card (C.subgroupOf N) = Nat.card (C ⊓ N : Subgroup G) := by
    rw [← inf_subgroupOf_right C N]
    exact Nat.card_congr (subgroupOfEquivOfLe (show C ⊓ N ≤ N from inf_le_right)).toEquiv
  rw [he] at hc
  change Nat.card (C ⊓ N : Subgroup G) = 336
  omega

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
