module

public import Stellmacher.Recognition.Parrott.SylowSeedMiddleAdjustment
public import Stellmacher.Recognition.Parrott.SylowSeedBxBound
public import Theory.SpecificGroups.Tits.RecognitionSylowBxCompatibility

/-!
# Equation (18) on the actual Sylow seed

The commutator bound gives [b,x] in a⟨t,z⟩ for the supplied seed's b.
Compatibility of the outer conjugation with equation (17) excludes its
t-coordinate. Multiplying x by u removes the remaining z-coordinate and
preserves (17). The actual seed constructor supplies the Sylow closure;
the other three generating closures and the marked z,t,v are unchanged.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, the paragraph leading to equation (18).
-/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] [Finite G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Once (17) holds, the error in (18) is central: its t-coordinate vanishes. -/
public theorem bx_eq_or_mul_z_of_eq17 (f : ParrottSylowSeedData n false)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z))
    (hyd : Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w) :
    Tits.parrottCommutator f.b f.x = f.a ∨
      Tits.parrottCommutator f.b f.x = f.a*z := by
  obtain ⟨hb,hc,hd⟩ := f.outer_discrepancies_mem_derived h
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  have hn := f.relations.bx_ne_mul_t_of_eq17 hz hax hyd hb hc hd
  rcases f.bx_cases h hax hby with he | he | he | he
  · exact Or.inl he
  · exact False.elim (hn false (by simpa only [Bool.toNat_false, pow_zero, mul_one] using he))
  · exact Or.inr he
  · apply False.elim (hn true ?_)
    simpa only [Bool.toNat_true, pow_one, mul_assoc, f.relations.comm_zt.eq] using he

set_option linter.unusedVariables false in
/-- Normalize (18) without disturbing (16), (17), or any actual subgroup. -/
public theorem exists_outer_middle_relations_of_eq17 [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z))
    (hyd : Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w) :
    ∃ f' : ParrottSylowSeedData n false, f'.OuterMiddleRelations := by
  rcases f.bx_eq_or_mul_z_of_eq17 h hax hby hyd with hb | hb
  · exact ⟨f, hax, hby, hyd, hb⟩
  · refine ⟨f.adjustXu, f.relations.adjust_xu_ax hax,
      f.relations.adjust_xu_by hby, f.relations.adjust_xu_eq17 hyd, ?_⟩
    have he := f.relations.adjust_xu_bx hb
      (f.relations.comm_au.symm.mul_right f.relations.comm_zu.symm)
      (f.relations.comm_az.symm.mul_right (Commute.refl z))
    simpa only [adjustXu, mul_assoc, ← pow_two, f.relations.z_sq, mul_one] using he

end Stellmacher.Recognition.ParrottSylowSeedData
