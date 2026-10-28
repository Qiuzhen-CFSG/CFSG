module
public import Theory.Alternating.TripleSixLocalRank
public import Theory.Alternating.TripleSevenLocalRank.CentralPreimage
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Local rank in arbitrary central cubic extensions of A₆

The derived subgroup of a central extension of A₆ is a perfect central
cover. Its central kernel has order one or three. The first case reduces
to six-letter cycle lengths; the second is the actual hexacode triple
cover. Both exclude order-nine elements, and the central kernel shows
the same for the whole extension. The inverse image of the concrete duad
S₄ then supplies a rank-two three-subgroup normalizing a nontrivial
two-subgroup. The result passes to any ambient cubic cover containing a
marked A₆ through its literal subgroup preimage.

Source: Aschbacher–Smith A.2.12(I.i), printed p.36, with the actual triple
cover identification from GLS3 5.2.3. No perfectness assumption is imposed
on the intermediate inverse image.
-/

@[expose] public noncomputable section
namespace GLS3.Chapter5.OddCentralCovers
open Subgroup Theory.GroupTheory

theorem six_cube_eq_one_of_ninth (x : alternatingGroup (Fin 6)) (hx : x^9=1) : x^3=1 := by
  apply Subtype.ext
  have hx' : (x.val)^9=1 := congrArg Subtype.val hx
  have hd : orderOf x.val ∣ 9 := orderOf_dvd_of_pow_eq_one hx'
  apply Equiv.Perm.pow_prime_eq_one_iff.mpr
  intro c hc
  have hdc : c ∣ 9 := (Equiv.Perm.dvd_of_mem_cycleType hc).trans hd
  have hlo := Equiv.Perm.two_le_of_mem_cycleType hc
  have hhi : c ≤ 6 := (Multiset.le_sum_of_mem hc).trans x.val.sum_cycleType_le
  interval_cases c <;> norm_num at hdc
  rfl



/-- Every central cubic extension of A₆ has no element of order nine. -/
theorem central_six_cube_eq_one_of_ninth {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 3)
    (x : E) (hx : x^9=1) : x^3=1 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let D := commutator E
  let g : D →* alternatingGroup (Fin 6) := f.comp D.subtype
  have hg : Function.Surjective g := by
    have hm : D.map f = ⊤ := by
      rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,commutator_eq_self]
    intro a
    obtain ⟨y,hy,hya⟩ := (show a ∈ D.map f by rw [hm]; trivial)
    exact ⟨⟨y,hy⟩,hya⟩
  have hgc : g.ker ≤ center D := fun d hd => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (hc hd) y)
  let c : PerfectCentralCovering.Cover D (alternatingGroup (Fin 6)) := {
    toMonoidHom := g
    surjective := hg
    isPerfect := PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
    ker_le_center := hgc }
  let : IsQuasisimple D := c.isQuasisimple
  have hgZ : g.ker = center D := c.toCovering.ker_eq_center_of_isSimple
  let e : D ⧸ center D ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hgZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  let k : g.ker →* f.ker := (D.subtype.comp g.ker.subtype).codRestrict _ (fun y => y.prop)
  have hki : Function.Injective k := by
    intro y z h
    exact Subtype.ext (Subtype.ext (congrArg (fun t : f.ker => (t : E)) h))
  have hkd : Nat.card g.ker ∣ 3 := hk ▸ card_dvd_of_injective k hki
  have hD : ∀ y : D, y^9=1 → y^3=1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hkd with h1 | h3
    · have hi : Function.Injective g := g.ker_eq_bot_iff.mp (eq_bot_of_card_eq _ h1)
      intro y hy
      apply hi
      rw [map_pow,map_one]
      apply six_cube_eq_one_of_ninth
      rw [← map_pow,hy,map_one]
    · exact triple_six_cube_eq_one_of_ninth e (hgZ ▸ h3)
  obtain ⟨d,hd⟩ := hg (f x)
  let z : E := x * (d : E)⁻¹
  have hz : z ∈ f.ker := by
    change f (x * (d : E)⁻¹) = 1
    rw [map_mul,map_inv,show f (d : E) = f x from hd,mul_inv_cancel]
  have hz3 : z^3=1 := by
    exact congrArg Subtype.val (hk ▸ pow_card_eq_one' (x := (⟨z,hz⟩ : f.ker)))
  have hz9 : z^9=1 := by
    rw [show 9=3*3 from rfl,pow_mul,hz3,one_pow]
  have hzd : Commute z (d : E) := (mem_center_iff.mp (hc hz) d).symm
  have hxd : x = z * (d : E) := by simp [z]
  have hd9 : d^9=1 := by
    apply Subtype.ext
    have hh := hx
    rw [hxd,hzd.mul_pow,hz9,one_mul] at hh
    exact hh
  rw [hxd,hzd.mul_pow,hz3,one_mul]
  exact congrArg Subtype.val (hD d hd9)

/-- The actual S₄ preimage supplies local three-rank two in every central cubic A₆ extension. -/
theorem central_six_twoLocalThreeRank_ge_two {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 3) :
    2 ≤ twoLocalPrimeRank 3 E := by
  let j := Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer.subtype.comp
    Theory.SpecificGroups.SymmetricSix.a6DuadModelEquiv.toMonoidHom
  have hj : Function.Injective j :=
    Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer.subtype_injective.comp
      Theory.SpecificGroups.SymmetricSix.a6DuadModelEquiv.injective
  obtain ⟨P,q,hq,hqc,hqk⟩ := CubicCoverPreimage.exists_restriction f hf hc j hj
  apply Representation.Hexacode.LocalThreeRank.two_le_localRank_cubic_s4_subgroup P q hq
    (hqk.trans hk) hqc
  intro y hy
  apply Subtype.ext
  exact central_six_cube_eq_one_of_ninth f hf hc hk y (congrArg Subtype.val hy)

/-- The preimage of any concretely embedded A₆ gives the required local rank in a cubic cover. -/
theorem twoLocalThreeRank_ge_two_of_embedded_six {E G : Type*}
    [Group E] [Finite E] [Group G]
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 3)
    (j : alternatingGroup (Fin 6) →* G) (hj : Function.Injective j) :
    2 ≤ twoLocalPrimeRank 3 E := by
  obtain ⟨P,q,hq,hqc,hqk⟩ := CubicCoverPreimage.exists_restriction f hf hc j hj
  exact (central_six_twoLocalThreeRank_ge_two q hq hqc (hqk.trans hk)).trans
    (twoLocalPrimeRank_le_of_injective 3 P.subtype P.subtype_injective)

end GLS3.Chapter5.OddCentralCovers
