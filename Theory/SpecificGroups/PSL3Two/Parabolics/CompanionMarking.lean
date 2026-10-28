module
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking

/-!
# Marking the companion parabolic through a quotient

An index-seven subgroup whose image contains the standard Borel has image
of order 24, hence is a point or line parabolic. If a second subgroup maps
to the line parabolic and their intersection is a two-group, the first
image must be the point parabolic. Kernel containment retains the literal
subgroup correspondence, rather than merely comparing abstract isomorphism
types.

LinearParabolicPair applies this to the two original component intersections
in Aschbacher–Smith 13.4.7, printed pp.900–901.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two
variable {C : Type*} [Group C]

/-- An index-seven companion with two-group intersection is the other
parabolic under the same marking of the line parabolic and Borel. -/
theorem companion_point_image (f : C →* SL) (hf : Function.Surjective f)
    (P Q : Subgroup C) (hindex : P.index = 7)
    (hkP : f.ker ≤ P) (hkQ : f.ker ≤ Q)
    (hB : borelSL ≤ P.map f) (hQ : Q.map f = lineParabolicSL)
    (hPQ : IsPGroup 2 (P ⊓ Q : Subgroup C)) :
    P.map f = pointParabolicSL := by
  have hi : (P.map f).index = 7 := (P.index_map_eq hf hkP).trans hindex
  have hc : Nat.card (P.map f) = 24 := by
    have hh := (P.map f).index_mul_card
    have hSL : Nat.card SL = 168 := (Nat.card_congr equiv.toEquiv).trans card_PSL
    rw [hi,hSL] at hh
    omega
  have hnt : ¬ IsPGroup 2 (P.map f) := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hc] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 24)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hproper : P.map f ≠ ⊤ := by
    intro he
    rw [he,index_top] at hi
    omega
  rcases parabolic_of_borel_le_of_not_two (P.map f) hB hproper hnt with hp | hl
  · exact hp
  · have he : P = Q := map_injective_of_ker_le f hkP hkQ (hl.trans hQ.symm)
    have htwo : IsPGroup 2 P := by
      rw [←he,inf_idem] at hPQ
      exact hPQ
    exact (hnt (htwo.map f)).elim
end Matrix.PSL3Two
