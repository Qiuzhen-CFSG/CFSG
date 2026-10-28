module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Parabolic

public import Theory.GroupAction.BinaryWreathVectorOrbits

/-!
# Singular lift centralizers in the original orthogonal four-space

A singular quotient vector has an eight-element stabilizer in the actual
orthogonal actor. Its full preimage in H is a two-group of order 8|Q_H|.
The commutator map into the central line bounds its index over C_H(u) by
two. Since |T:Q_H|=8, the actual lift centralizer is a two-group of order
at least |T|/2, which is the numerical input to exclude singular fusion.

All preimages and kernels use the original coordinate and actor maps.
Only elementary abelianness of the original module is needed in addition
to the literal marked action and F.9 hypothesis.

Source: Aschbacher--Smith, 14.6.17(4), printed p.1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
attribute [local instance] orthogonalAction
include h

/-- The quotient point stabilizer has exactly its marked actor order times the core order. -/
theorem quotient_point_stabilizer_card
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu2 : (u : G)^2 = 1) :
    Nat.card (h.kernel (zpowers (u : G))) =
      Nat.card (MulAction.stabilizer OrthogonalActor (d.coordinates u)) * Nat.card D.QH := by
  let B := MulAction.stabilizer OrthogonalActor (d.coordinates u)
  let K := B.comap d.actor
  let f : K →* B := d.actor.subgroupComap B
  have hf : Function.Surjective f := d.actor.subgroupComap_surjective_of_surjective B d.onto
  have hker : f.ker = d.actor.ker.subgroupOf K := by
    ext x
    exact Subtype.ext_iff
  have hkerK : d.actor.ker ≤ K := by
    intro x hx
    change d.actor x ∈ B
    rw [show d.actor x = 1 from hx]
    exact one_mem _
  have hkerCard : Nat.card f.ker = Nat.card D.QH := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hkerK).toEquiv,d.actor_kernel]
    exact Nat.card_congr (subgroupOfEquivOfLe (show D.QH ≤ D.H from pCoreIn_le 2 D.H)).toEquiv
  rw [suitable_kernel_eq_point_preimage h d u hu2,card_map_of_injective D.H.subtype_injective]
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,hkerCard] at hc
  exact hc

theorem quotient_point_stabilizer_two_group
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu2 : (u : G)^2 = 1)
    (hp : IsPGroup 2 (MulAction.stabilizer OrthogonalActor (d.coordinates u))) :
    IsPGroup 2 (h.kernel (zpowers (u : G))) := by
  rw [suitable_kernel_eq_point_preimage h d u hu2]
  apply IsPGroup.map
  apply hp.comap_of_ker_isPGroup
  rw [d.actor_kernel]
  exact (isPGroup_pCoreIn 2 D.H).comap_subtype

/-- Taking actual lifts costs at most the order of the central line. -/
theorem quotient_point_stabilizer_card_le_twice_centralizer
    (u : G) (hu : u ∈ D.UH) :
    Nat.card (h.kernel (zpowers u)) ≤
      2 * Nat.card (D.H ⊓ centralizer ({u} : Set G) : Subgroup G) := by
  let P := h.kernel (zpowers u)
  let C := D.H ⊓ centralizer ({u} : Set G)
  have hPH : P ≤ D.H := fun x hx => ((h.mem_kernel_iff
    (zpowers_le.mpr (h.UH_le_H hu))).mp hx).1
  have hcomm (x : G) (hx : x ∈ P) : ⁅u,x⁆ ∈ D.V₁ :=
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp hx).2 u (mem_zpowers u)
  let f : P →* D.V₁ := {
    toFun x := ⟨⁅u,(x : G)⁆,hcomm x x.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅u,(a : G)*(b : G)⁆ = ⁅u,(a : G)⁆ * ⁅u,(b : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have he := h.H_centralizes (hPH a.property) _ (hcomm b b.property)
      calc
        _ = ⁅u,(a : G)⁆ * ((a : G)*⁅u,(b : G)⁆) * (a : G)⁻¹ := by group
        _ = _ := by rw [←he]; group }
  have hCP : C ≤ P := by
    intro x hx
    apply (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr
    refine ⟨hx.1,fun a ha => ?_⟩
    have he : x ∈ centralizer (zpowers u : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact hx.2
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (he a ha)]
    exact one_mem _
  have hker : f.ker = C.subgroupOf P := by
    ext x
    change (⟨⁅u,(x : G)⁆,_⟩ : D.V₁) = 1 ↔
      (x : G) ∈ D.H ∧ (x : G) ∈ centralizer ({u} : Set G)
    rw [Subtype.ext_iff]
    change ⁅u,(x : G)⁆ = 1 ↔ (x : G) ∈ D.H ∧ (x : G) ∈ centralizer ({u} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm,
      mem_centralizer_singleton_iff,and_iff_right (hPH x.property)]
    exact eq_comm
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hker,
    Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv] at hc
  rw [hc]
  exact Nat.mul_le_mul_right _ ((card_le_card_group f.range).trans_eq h.point_card)

theorem singular_lift_centralizer_bound
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    [IsElementaryAbelian 2 D.UH]
    (u : (⁅D.UH,D.H⁆ : Subgroup G)) (hu : ∀ i, (u : G) ∉ d.plane i) :
    IsPGroup 2 (D.H ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) ∧
      Nat.card (D.T : Subgroup G) ≤
        2 * Nat.card (D.H ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) := by
  have hsupport : ∀ i, d.coordinates u i ≠ 1 := by
    intro i hi
    let j : OrthogonalPlaneIndex := i * Multiplicative.ofAdd (1 : ZMod 2)
    apply hu j
    rw [d.mem_plane_iff]
    intro k hkj
    have he : k = i := by
      have hh : ∀ i k : OrthogonalPlaneIndex,
          k ≠ i * Multiplicative.ofAdd (1 : ZMod 2) → k = i := by decide
      exact hh i k hkj
    rwa [he]
  have hs := BinaryWreathPointStabilizer.singular_stabilizer_card (d.coordinates u) hsupport
  have hp : IsPGroup 2 (MulAction.stabilizer OrthogonalActor (d.coordinates u)) :=
    IsPGroup.of_card (n := 3) hs
  have huU : (u : G) ∈ D.UH :=
    (le_normalizer_iff_commutator_le_left.mp d.normalized) u.property
  have hu2 : (u : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (u : G) huU
  have hP := quotient_point_stabilizer_two_group h d u hu2 hp
  have hC : D.H ⊓ centralizer ({(u : G)} : Set G) ≤ h.kernel (zpowers (u : G)) := by
    intro x hx
    apply (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H huU))).mpr
    refine ⟨hx.1,fun a ha => ?_⟩
    have he : x ∈ centralizer (zpowers (u : G) : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact hx.2
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (he a ha)]
    exact one_mem _
  refine ⟨hP.to_le hC,?_⟩
  have hc := quotient_point_stabilizer_card h d u hu2
  rw [hs] at hc
  have ht := (D.QH.subgroupOf (D.T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h.QH_le_T).toEquiv] at ht
  change Nat.card D.QH * D.QH.relIndex (D.T : Subgroup G) = Nat.card (D.T : Subgroup G) at ht
  rw [orthogonal_core_index h d] at ht
  have hsize := quotient_point_stabilizer_card_le_twice_centralizer h (u : G) huU
  omega

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
