module

public import Theory.GroupAction.RankTwoCosetCover.PathTransport
/-!
# Alternating four-edge walks in rank-two coset geometries

An element of each endpoint outside the other yields the literal alternating
walk x, l, b x, b a l, b a b x. Endpoint membership supplies incidence, and
nonmembership gives the three nonbacktracking inequalities. This construction
needs neither a girth bound nor a recognition of the generated group.
-/

@[expose] public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph BasedWalk
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
variable (a b : G) (ha : a ∈ F false) (hb : b ∈ F true)

include ha in
private theorem fixes0 : a • base F false = base F false := by
  change a ∈ stabilizer F (base F false)
  simpa only [stabilizer,base,stabilizer_base] using ha
include hb in
private theorem fixes1 : b • base F true = base F true := by
  change b ∈ stabilizer F (base F true)
  simpa only [stabilizer,base,stabilizer_base] using hb
theorem alternatingFour_adj0 : (graph F).Adj (base F false) (base F true) :=
  ⟨Bool.false_ne_true,incident_base F false true⟩
include hb in
theorem alternatingFour_adj1 : (graph F).Adj (base F true) (b • base F false) := by
  have h := (translationGraphIso F b).toHom.map_adj (alternatingFour_adj0 F).symm
  change (graph F).Adj (b • base F true) (b • base F false) at h
  rwa [fixes1 F b hb] at h
include ha in
theorem alternatingFour_adj2 : (graph F).Adj (b • base F false) ((b*a) • base F true) := by
  have h := (translationGraphIso F (b*a)).toHom.map_adj (alternatingFour_adj0 F)
  change (graph F).Adj ((b*a) • base F false) ((b*a) • base F true) at h
  simpa only [mul_smul,fixes0 F a ha] using h
include hb in
theorem alternatingFour_adj3 : (graph F).Adj ((b*a) • base F true) ((b*a*b) • base F false) := by
  have h := (translationGraphIso F (b*a*b)).toHom.map_adj (alternatingFour_adj0 F).symm
  change (graph F).Adj ((b*a*b) • base F true) ((b*a*b) • base F false) at h
  simpa only [mul_smul,fixes1 F b hb] using h

def alternatingFour : BasedWalk (graph F) 4 (base F false) :=
  ⟨⟨base F true,alternatingFour_adj0 F⟩,⟨⟨b • base F false,alternatingFour_adj1 F b hb⟩,
    ⟨⟨(b*a) • base F true,alternatingFour_adj2 F a b ha⟩,
      ⟨⟨(b*a*b) • base F false,alternatingFour_adj3 F a b hb⟩,PUnit.unit⟩⟩⟩⟩

theorem alternatingFour_endpoint : (alternatingFour F a b ha hb).endpoint =
    (b*a*b) • base F false := rfl

theorem alternatingFour_nonbacktracking (hna : a ∉ F true) (hnb : b ∉ F false) :
    (alternatingFour F a b ha hb).Nonbacktracking := by
  have hnb' : b • base F false ≠ base F false := by
    intro he
    apply hnb
    have hm : b ∈ stabilizer F (base F false) := he
    simpa only [stabilizer,base,stabilizer_base] using hm
  have hna' : a • base F true ≠ base F true := by
    intro he
    apply hna
    have hm : a ∈ stabilizer F (base F true) := he
    simpa only [stabilizer,base,stabilizer_base] using hm
  refine ⟨hnb',?_,?_,trivial⟩
  · intro he
    change (b*a) • base F true = base F true at he
    apply hna'
    have he' := congrArg (fun v : Vertex F => b⁻¹ • v) he
    simpa only [mul_smul,inv_smul_smul,inv_smul_eq_iff.mpr (fixes1 F b hb).symm] using he'
  · intro he
    change (b*a*b) • base F false = b • base F false at he
    apply hnb'
    have he' := congrArg (fun v : Vertex F => a⁻¹ • (b⁻¹ • v)) he
    simpa only [mul_smul,inv_smul_smul,inv_smul_eq_iff.mpr (fixes0 F a ha).symm] using he'
end Subgroup.CosetGeometry.RankTwo
