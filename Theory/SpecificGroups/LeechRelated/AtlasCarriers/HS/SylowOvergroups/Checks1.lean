module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Data
/-!
# Checked Higman--Sims double-coset rows

Bounded kernel checks of invariant counts, intersection rejections, and
actual generation words. Source: ATLAS HSG1-p100B0; A.3.12(18), pp.47--48.
-/
@[expose] public section
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open Data EvenLocalCandidates.SylowCatalogueData
set_option Elab.async false

set_option maxRecDepth 100000 in
theorem rep1 : ∀ i : Fin 30, ∀ p : Fin 100, repPerm ⟨i.val+30,by omega⟩ p = dVal ⟨i.val+30,by omega⟩ p := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem inverse1 : ∀ i : Fin 30, ∀ p : Fin 100, dVal ⟨i.val+30,by omega⟩ (diVal ⟨i.val+30,by omega⟩ p) = p := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem counts1 : ∀ i : Fin 30, ∀ k, count (if inverseFlag k then diVal ⟨i.val+30,by omega⟩ else dVal ⟨i.val+30,by omega⟩) k = countVal ⟨i.val+30,by omega⟩ k := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem rejects1 : ∀ i : Fin 30, ∀ t, rejectTest ⟨i.val+30,by omega⟩ t = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem bound1 : ∀ i : Fin 30, (Finset.univ.filter fun t => reject ⟨i.val+30,by omega⟩ t = 100).card = bound ⟨i.val+30,by omega⟩ := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem generate1 : ∀ i : Fin 30, kind ⟨i.val+30,by omega⟩ = 2 → ∀ p : Fin 100, evalFun (genVal ⟨i.val+30,by omega⟩) (extract0 ⟨i.val+30,by omega⟩) p = OrderCertificate.p0Map p ∧ evalFun (genVal ⟨i.val+30,by omega⟩) (extract1 ⟨i.val+30,by omega⟩) p = OrderCertificate.p1Map p := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem central1 : ∀ i : Fin 30, kind ⟨i.val+30,by omega⟩ = 0 → ∀ p : Fin 100, dVal ⟨i.val+30,by omega⟩ (packedMap (eCode 1) p) = packedMap (eCode 1) (dVal ⟨i.val+30,by omega⟩ p) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem local1 : ∀ i : Fin 30, kind ⟨i.val+30,by omega⟩ = 1 → ∀ p : Fin 100, dVal ⟨i.val+30,by omega⟩ (packedMap (eCode 1) p) = packedMap (eCode (localImage ⟨i.val+30,by omega⟩).1) (dVal ⟨i.val+30,by omega⟩ p) ∧ dVal ⟨i.val+30,by omega⟩ (packedMap (eCode 2) p) = packedMap (eCode (localImage ⟨i.val+30,by omega⟩).2.1) (dVal ⟨i.val+30,by omega⟩ p) ∧ dVal ⟨i.val+30,by omega⟩ (packedMap (eCode 4) p) = packedMap (eCode (localImage ⟨i.val+30,by omega⟩).2.2) (dVal ⟨i.val+30,by omega⟩ p) := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.HS.SylowOvergroups
