module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction
import all CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.Octad
import all CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.Sextet

/-!
# The native M₂₄ obstruction in central component coordinates

This internal extension exposes the native part of the existing octad and
sextet block proofs independently of the Chapter 2 ambient setup. The octad
quotient is A₈; the sextet uses the checked subnormal-order trichotomy. Both
exclude a chi-zero group with central kernel and subnormal image in a finite
power of the native local. The E.6.8 consumer supplies these exact coordinates
from its original component orbit, without an extra involution-centralizer
containment assumption. The internal imports deliberately reuse the original
native calculations and their private implementation lemmas.

Source: Aschbacher–Smith E.6.8, printed p.248, and 2.3.9(7), printed p.526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
open Subgroup ChapterC Theory.GroupTheory Sporadic.Mathieu M24LocalGeometry

theorem no_chiZero_of_geometry_central_coordinates {B : Type*} [Group B]
    (hB : IsChiZeroBlock B) (P : Subgroup M24) (hP : IsGeometryLocal P) {n : ℕ}
    (q : B →* (Fin n → P)) (hqc : q.ker ≤ center B) (hqs : q.range.IsSubnormal) : False := by
  rcases hP with ⟨O,rfl⟩ | ⟨X,rfl⟩
  · obtain ⟨f,hf,hk⟩ := octad_alternating_quotient O
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    have hc : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have htwo : ¬ IsPGroup 2 (alternatingGroup (Fin 8)) := by
      intro hp
      obtain ⟨n,hn⟩ := hp.exists_card_dvd_pow
      rw [hc] at hn
      have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 20160).trans hn
      have := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at this
    obtain ⟨e⟩ := quotient_equiv_of_central_coordinates hB.chi.short
      (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 8)))
      htwo q hqc hqs f hf hk
    exact LieType.not_chiZero_of_quotient_card_20160
      ((Nat.card_congr e.toEquiv).trans hc) hB
  · exact no_chiZero_central_power hB (subnormal_sextet_orders X) q hqc hqs
end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
