module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates

/-!
# Centralizer divisibility in the pi class

A conjugate of the distinguished involution has centralizer order 384.
Consequently its centralizer inside any subgroup has order dividing 384,
and in particular its order is not divisible by nine. These are the ambient
order obstructions used in the normalizer arguments; no order for C_G(mu)
is assumed or derived here.

The proof transports centralizers by conjugation and applies Lagrange's theorem.
Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.4 and 2.6, pp.226--229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
universe u
variable {G : Type u} [Group G] (D : LocalData G)

/-- A conjugate of pi has an actual ambient centralizer of order 384. -/
public theorem centralizer_card_of_isConj {x : G} (hx : IsConj D.z x) :
    Nat.card (centralizer ({x} : Set G)) = 384 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  let f := MulAut.conj g
  have he : f D.z = x := hg
  have hc : Nat.card D.centralizer = Nat.card (centralizer ({f D.z} : Set G)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro a
    change a ∈ centralizer ({D.z} : Set G) ↔ f a ∈ centralizer ({f D.z} : Set G)
    simp only [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]
  rw [he] at hc
  exact hc.symm.trans D.centralizer_card

/-- The centralizer of a pi-conjugate inside any subgroup has order dividing 384. -/
public theorem centralizer_intersection_dvd {x : G} (hx : IsConj D.z x) (K : Subgroup G) :
    Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) ∣ 384 := by
  rw [← centralizer_card_of_isConj D hx]
  exact card_dvd_of_le inf_le_right

/-- The factor nine obstruction used in Held's normalizer arguments. -/
public theorem nine_not_dvd_centralizer_intersection {x : G} (hx : IsConj D.z x) (K : Subgroup G) :
    ¬ 9 ∣ Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  intro h
  have h9 : 9 ∣ 384 := h.trans (centralizer_intersection_dvd D hx K)
  norm_num at h9

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
