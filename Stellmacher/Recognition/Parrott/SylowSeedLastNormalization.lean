module
public import Stellmacher.Recognition.Parrott.SylowSeedOuterData
public import Stellmacher.Recognition.Parrott.SylowSeedOuterCentralization
public import Theory.SpecificGroups.Tits.RecognitionSylowLastParameters

/-!
# Normalizing the last two outer Sylow relations

The elementary error bounds, the conjugated core relations, and the prescribed
square action leave two coupled alternatives. The original seed works in the
first; the residual substitution (a,b,c,d) ↦ (at,bv,cu,dw) works in the second.
The seed constructor retains the marked witnesses and uses the proved actual
subgroup closure equalities. No presentation or completed frame is used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.680, the paragraph preceding (19).
-/
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- A further choice of core coordinates completes (19), leaving the central
factor in the d-equation for the final x ↦ xt correction. -/
public theorem exists_outer_last_normalization [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (f : ParrottSylowSeedData n false) (hm : f.OuterMiddleRelations)
    (hyc : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    ∃ g : ParrottSylowSeedData n false, g.OuterMiddleRelations ∧ g.OuterLastRelations := by
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  obtain ⟨hb, hc, hd⟩ := f.outer_discrepancies_mem_derived h
  obtain ⟨_, ⟨ci,cj,ck,hc⟩, ⟨di,dj,dk,hd⟩⟩ :=
    f.relations.outer_image_parameters hz hm.eq16_ax hb hc hd
  have halt := f.relations.last_image_alternatives hz hm.eq16_ax hm.eq18_bx
    hyc hm.eq17_yd ci cj ck di dj dk hc hd
  rcases f.relations.normalize_last_images halt with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · exact ⟨f, hm, ⟨hyc, hc, hd⟩⟩
  · let g : ParrottSylowSeedData n false :=
      { u := f.u
        w := f.w
        a := f.a*n.t
        b := f.b*n.v
        c := f.c*f.u
        d := f.d*f.w
        x := f.x
        derived_basis := f.derived_basis
        elementary_basis := Tits.ParrottSylowSeedRelations.residual_elementary_closure.trans
          f.elementary_basis
        core_generators := f.relations.residual_core_closure.trans f.core_generators
        sylow_generators := f.relations.residual_sylow_closure.trans f.sylow_generators
        relations := f.relations.residual_relations }
    have hgm : g.OuterMiddleRelations :=
      { eq16_ax := f.relations.residual_ax hm.eq16_ax
        comm_by := f.relations.residual_by hm.comm_by
        eq17_yd := f.relations.residual_yd hm.eq17_yd
        eq18_bx := f.relations.residual_bx hm.eq18_bx }
    exact ⟨g, hgm, ⟨f.relations.residual_yc hyc, hc, hd⟩⟩

end Stellmacher.Recognition.ParrottSylowSeedData
