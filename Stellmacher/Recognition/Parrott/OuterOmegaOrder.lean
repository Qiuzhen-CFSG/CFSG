module

public import Stellmacher.Recognition.Parrott.OuterOmegaCoreIndex
public import Stellmacher.Recognition.Parrott.OuterCoreFixedCentralization
public import Stellmacher.Recognition.Parrott.OuterCoreInvolutionCoset
public import Theory.GroupTheory.PGroup.OmegaInvolutionCosets

/-!
# The order of the actual outer omega

Write H=C_G(z), J=O₂(H), and D=J′. For an involution y outside J,
the image of C_H(y) in H/J is cyclic. A central involution therefore splits
its first omega into y and the kernel omega. Core involutions fixed by y
centralize C_D(y) and occupy at most one nonzero D-coset. Hence the kernel
omega is elementary of order eight or sixteen, and the actual outer omega
is elementary of order sixteen or thirty-two.

Both core facts are proved from the original centralizer hypotheses. No
fusion or normalizer assumption is used. The Sylow transport retains
exactly the supplied ParrottSecondElementaryData.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.674–676, especially the first paragraph of p.676.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

/-- The actual outer-centralizer omega is elementary of order sixteen or thirty-two. -/
public theorem parrott_outer_omega_order
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ y : H, orderOf y = 2 → y ∉ J →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      IsElementaryAbelian 2 X ∧ (Nat.card X = 16 ∨ Nat.card X = 32) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let DH := (commutator J).map J.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change ∀ y : H, orderOf y = 2 → y ∉ J → _
  intro y hy hyJ
  have hcoset := parrott_outer_core_involutions_single_coset z h y hy hyJ
  have hcentral := parrott_outer_core_centralizes_derived_fixed z h y hy hyJ
  let P := centralizer ({y} : Set H)
  let U := DH.subgroupOf P
  let embed : P →* G := H.subtype.comp P.subtype
  let X := (omega₁ P (p := 2)).map embed
  change IsElementaryAbelian 2 X ∧ (Nat.card X = 16 ∨ Nat.card X = 32)
  obtain ⟨_, _, _, _, _, hD, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hD
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  let : IsElementaryAbelian 2 U := {
    toIsMulCommutative := subgroupOf_isMulCommutative P DH
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      apply Subtype.ext
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := DH) (a : P).val a.property)) }
  have hUcard : Nat.card U = 8 := by
    let B := (centralizer ({(y : G)} : Set G)).subgroupOf E
    let i : U → B := fun a =>
      ⟨⟨embed a, by
          obtain ⟨d, hd, heq⟩ := a.property
          exact ⟨d, hd, congrArg H.subtype heq⟩⟩,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp (a : P).property))⟩
    have hi : Function.Bijective i := by
      constructor
      · intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        apply H.subtype_injective
        exact congrArg (fun c : B => ((c : E) : G)) hab
      · intro b
        obtain ⟨d, hd, hdb⟩ := (b : E).property
        have hdP : (d : H) ∈ P := by
          apply mem_centralizer_singleton_iff.mpr
          apply H.subtype_injective
          change ((d : H) : G) * (y : G) = (y : G) * ((d : H) : G)
          rw [show ((d : H) : G) = ((b : E) : G) from hdb]
          exact mem_centralizer_singleton_iff.mp b.property
        refine ⟨⟨⟨d, hdP⟩, mem_map_of_mem J.subtype hd⟩, ?_⟩
        exact Subtype.ext (Subtype.ext hdb)
    exact (Nat.card_congr (Equiv.ofBijective i hi)).trans
      (parrott_outer_involution_fixed_card z h y hy hyJ)
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let f := e.toMonoidHom.comp (QuotientGroup.mk' J)
  have hker : f.ker = J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hfy : orderOf (f y) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hy2, map_one]
    · intro heq
      exact hyJ (hker ▸ (show y ∈ f.ker from heq))
  let C := centralizer ({f y} : Set M)
  let : IsCyclic C := (faithful_five_four_involution_centralizer φ hφ (f y) hfy).1
  let π : P →* C := (f.comp P.subtype).codRestrict C (by
    intro a
    apply mem_centralizer_singleton_iff.mpr
    change f (a : H) * f y = f y * f (a : H)
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp a.property))
  have hπker (a : P) : a ∈ π.ker ↔ (a : H) ∈ J := by
    constructor
    · intro ha
      have hfa : f (a : H) = 1 := congrArg Subtype.val ha
      exact hker ▸ (show (a : H) ∈ f.ker from hfa)
    · intro ha
      have hfa : (a : H) ∈ f.ker := hker.symm ▸ ha
      exact Subtype.ext hfa
  let yP : P := ⟨y, mem_centralizer_singleton_iff.mpr rfl⟩
  have hyπ : orderOf (π yP) = 2 := (Subgroup.orderOf_coe (π yP)).symm.trans hfy
  have hUker : U ≤ π.ker := by
    intro a ha
    exact (hπker a).mpr ((map_subtype_le (commutator J)) ha)
  have hcent (a : P) (ha : a ∈ π.ker) (_ha2 : a ^ 2 = 1) :
      a ∈ centralizer (U : Set P) := by
    intro b hb
    exact Subtype.ext (hcentral a ((hπker a).mp ha)
      (mem_centralizer_singleton_iff.mp a.property)
      b hb (mem_centralizer_singleton_iff.mp b.property)).symm
  have hcos (a b : P) (ha : a ∈ π.ker) (hb : b ∈ π.ker)
      (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (haU : a ∉ U) (hbU : b ∉ U) :
      a⁻¹ * b ∈ U :=
    hcoset a b ((hπker a).mp ha) ((hπker b).mp hb)
      (congrArg P.subtype ha2) (congrArg P.subtype hb2)
      (mem_centralizer_singleton_iff.mp a.property)
      (mem_centralizer_singleton_iff.mp b.property) haU hbU
  obtain ⟨homega, hcard⟩ := omega₁_elementary_card_of_cyclic_image_involution_cosets
    π yP (Subtype.ext hy2)
    (fun a => show Commute a yP from Subtype.ext
      (mem_centralizer_singleton_iff.mp a.property)) hyπ U hUker hcent hcos
  let : IsElementaryAbelian 2 (omega₁ P (p := 2)) := homega
  refine ⟨IsElementaryAbelian.map embed, ?_⟩
  have hXcard : Nat.card X = Nat.card (omega₁ P (p := 2)) :=
    card_map_of_injective (H.subtype_injective.comp P.subtype_injective)
  simpa only [hXcard, hUcard, show 2 * 8 = 16 from rfl, show 4 * 8 = 32 from rfl]
    using hcard

namespace ParrottSecondElementaryData

/-- The actual outer omega in the supplied Sylow has the two orders required
by the outer-fusion reduction. No core-fusion assumption is needed. -/
public theorem outer_omega_order_alternatives
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) :
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    Nat.card X = 16 ∨ (IsElementaryAbelian 2 X ∧ Nat.card X = 32) := by
  let H := centralizer ({z} : Set G)
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  have hyH : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy
  have hyHJ : yH ∉ pCore 2 H := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hh := parrott_outer_omega_order z h yH hyH hyHJ
  dsimp only at hh
  rw [d.outer_centralizer_omega_eq h y hyT hyJ hy] at hh
  rcases hh with ⟨helem, h16 | h32⟩
  · exact Or.inl h16
  · exact Or.inr ⟨helem, h32⟩

end ParrottSecondElementaryData
end Stellmacher.Recognition
