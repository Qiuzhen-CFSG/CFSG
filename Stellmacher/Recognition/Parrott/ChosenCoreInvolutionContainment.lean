module

public import Stellmacher.Recognition.Parrott.SecondElementary
public import Theory.GroupAction.Order512FiveInvolutionCentralizer

/-!
# Involutions in the chosen core centralizer

Let H=C_G(z), J=O₂(H), and let a and F be the supplied second elementary
data. Every square-one element of J commuting with a belongs to F. Indeed,
the nonidentity derived cosets with square-one lifts form a sum-free five-orbit.
Since ax also squares to one, either x or ax belongs to J′. The supplied
fixed-join identities then put x in F. No index assumption or additional
global simple-group hypotheses are needed.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–676, especially the centralizer calculation on p.676.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- Every square-one element of the core centralizing the supplied a
belongs to the supplied fixed join F. -/
public theorem chosen_core_centralizer_involutions_mem_fixed_join {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ x : G, x ∈ K ⊓ S → x ^ 2 = 1 → x ∈ d.F := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let K := J.map H.subtype
  let S := H ⊓ centralizer ({(d.a : G)} : Set G)
  change ∀ x : G, x ∈ K ⊓ S → x ^ 2 = 1 → x ∈ d.F
  obtain ⟨P, hP⟩ := h.five_centralizer
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let _ : MulDistribMulAction P J :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (P : Subgroup H) J
      (Subgroup.le_normalizer_of_normal (H := J))
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro x hx
    apply hP
    change (x : H) ∈ centralizer (P : Set H)
    intro a ha
    have hfix := congrArg (fun y : J => (y : H)) (hx ⟨a, ha⟩)
    change a * (x : H) * a⁻¹ = x at hfix
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, (h.card_and_solvable z).1]
    decide +kernel
  let b : J := ⟨d.a, d.a_mem_core⟩
  have hb : b ^ 2 = 1 := by
    apply Subtype.ext
    change d.a ^ 2 = 1
    rw [← d.a_order]
    exact pow_orderOf_eq_one d.a
  have hbD : b ∉ commutator J := fun hbD =>
    d.a_not_mem_derived (mem_map_of_mem J.subtype hbD)
  have hEF : E ⊓ centralizer ({(d.a : G)} : Set G) ≤ d.F := by
    rw [← d.inf_eq]
    exact inf_le_right
  have haF : (d.a : G) ∈ d.F := by
    rw [d.fixed_join]
    exact mem_sup_left (mem_zpowers _)
  intro x hx hx2
  obtain ⟨xH, hxJ, hxval⟩ := hx.1
  change (xH : G) = x at hxval
  let y : J := ⟨xH, hxJ⟩
  have hy : y ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (xH : G) ^ 2 = 1
    rwa [hxval]
  have hcomm : Commute b y := by
    apply Subtype.ext
    apply Subtype.ext
    change (d.a : G) * (xH : G) = (xH : G) * (d.a : G)
    rw [hxval]
    exact (mem_centralizer_singleton_iff.mp hx.2.2).symm
  rcases Theory.GroupAction.parrott_commuting_involution_derived_cosets
    pCore_isPGroup h.core_card h.core_class hPcard hfixed b hb hbD y hy hcomm with hyD | hbyD
  · exact hEF ⟨⟨y, hyD, hxval⟩, hx.2.2⟩
  · have haxE : (d.a : G) * x ∈ E := by
      refine ⟨b * y, hbyD, ?_⟩
      change (d.a : G) * (xH : G) = (d.a : G) * x
      rw [hxval]
    have haxF : (d.a : G) * x ∈ d.F := hEF ⟨haxE,
      (centralizer ({(d.a : G)} : Set G)).mul_mem
        (mem_centralizer_singleton_iff.mpr rfl) hx.2.2⟩
    simpa only [inv_mul_cancel_left] using d.F.mul_mem (d.F.inv_mem haF) haxF

/-- The index-two form of the containment used in the chosen omega argument. -/
public theorem chosen_core_centralizer_involutions_mem_fixed_join_of_relIndex_two
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    K.relIndex S = 2 → ∀ x : G, x ∈ K ⊓ S → x ^ 2 = 1 → x ∈ d.F := by
  intro H J K S _
  exact d.chosen_core_centralizer_involutions_mem_fixed_join h

end Stellmacher.Recognition.ParrottSecondElementaryData
