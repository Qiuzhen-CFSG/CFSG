module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks0
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks1
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks3
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks4
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks5
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks6
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks7
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Checks8
/-!
# Checked Higman--Sims double-coset rows

Bounded kernel checks of invariant counts, intersection rejections, and
actual generation words. Source: ATLAS HSG1-p100B0; A.3.12(18), pp.47--48.
-/
@[expose] public section
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open Data EvenLocalCandidates.SylowCatalogueData
set_option Elab.async false

theorem rep_spec (j : Fin 270) : ∀ p : Fin 100, repPerm j p = dVal j p := by
  by_cases h0 : j.val < 30
  · have h := rep0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := rep1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := rep2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := rep3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := rep4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := rep5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := rep6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := rep7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := rep8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem inverse_spec (j : Fin 270) : ∀ p : Fin 100, dVal j (diVal j p) = p := by
  by_cases h0 : j.val < 30
  · have h := inverse0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := inverse1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := inverse2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := inverse3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := inverse4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := inverse5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := inverse6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := inverse7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := inverse8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem counts_spec (j : Fin 270) : ∀ k, count (if inverseFlag k then diVal j else dVal j) k = countVal j k := by
  by_cases h0 : j.val < 30
  · have h := counts0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := counts1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := counts2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := counts3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := counts4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := counts5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := counts6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := counts7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := counts8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem rejects_spec (j : Fin 270) : ∀ t, rejectTest j t = true := by
  by_cases h0 : j.val < 30
  · have h := rejects0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := rejects1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := rejects2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := rejects3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := rejects4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := rejects5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := rejects6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := rejects7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := rejects8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem bound_spec (j : Fin 270) : (Finset.univ.filter fun t => reject j t = 100).card = bound j := by
  by_cases h0 : j.val < 30
  · have h := bound0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := bound1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := bound2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := bound3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := bound4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := bound5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := bound6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := bound7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := bound8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem generate_spec (j : Fin 270) : kind j = 2 → ∀ p : Fin 100, evalFun (genVal j) (extract0 j) p = OrderCertificate.p0Map p ∧ evalFun (genVal j) (extract1 j) p = OrderCertificate.p1Map p := by
  by_cases h0 : j.val < 30
  · have h := generate0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := generate1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := generate2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := generate3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := generate4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := generate5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := generate6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := generate7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := generate8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem central_spec (j : Fin 270) : kind j = 0 → ∀ p : Fin 100, dVal j (packedMap (eCode 1) p) = packedMap (eCode 1) (dVal j p) := by
  by_cases h0 : j.val < 30
  · have h := central0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := central1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := central2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := central3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := central4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := central5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := central6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := central7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := central8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h

theorem local_spec (j : Fin 270) : kind j = 1 → ∀ p : Fin 100, dVal j (packedMap (eCode 1) p) = packedMap (eCode (localImage j).1) (dVal j p) ∧ dVal j (packedMap (eCode 2) p) = packedMap (eCode (localImage j).2.1) (dVal j p) ∧ dVal j (packedMap (eCode 4) p) = packedMap (eCode (localImage j).2.2) (dVal j p) := by
  by_cases h0 : j.val < 30
  · have h := local0 ⟨j.val-0,by omega⟩
    have he : j.val-0+0 = j.val := by omega
    simpa only [he] using h
  by_cases h1 : j.val < 60
  · have h := local1 ⟨j.val-30,by omega⟩
    have he : j.val-30+30 = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 90
  · have h := local2 ⟨j.val-60,by omega⟩
    have he : j.val-60+60 = j.val := by omega
    simpa only [he] using h
  by_cases h3 : j.val < 120
  · have h := local3 ⟨j.val-90,by omega⟩
    have he : j.val-90+90 = j.val := by omega
    simpa only [he] using h
  by_cases h4 : j.val < 150
  · have h := local4 ⟨j.val-120,by omega⟩
    have he : j.val-120+120 = j.val := by omega
    simpa only [he] using h
  by_cases h5 : j.val < 180
  · have h := local5 ⟨j.val-150,by omega⟩
    have he : j.val-150+150 = j.val := by omega
    simpa only [he] using h
  by_cases h6 : j.val < 210
  · have h := local6 ⟨j.val-180,by omega⟩
    have he : j.val-180+180 = j.val := by omega
    simpa only [he] using h
  by_cases h7 : j.val < 240
  · have h := local7 ⟨j.val-210,by omega⟩
    have he : j.val-210+210 = j.val := by omega
    simpa only [he] using h
  have h := local8 ⟨j.val-240,by omega⟩
  have he : j.val-240+240 = j.val := by omega
  simpa only [he] using h
end Sporadic.LeechRelated.HS.SylowOvergroups
