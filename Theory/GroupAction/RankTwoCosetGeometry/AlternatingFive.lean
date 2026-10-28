module

public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingPaths
/-!
# Five-edge apartment candidates at either marked type

The two specified endpoint elements give a literal nonbacktracking five-walk
from either Boolean root type. Its fixer lies in the intersection of the
initial flag stabilizer and its conjugate by the alternating four-letter
word. No apartment relation, girth or ambient-order premise is used.

Source: the local path calculations in Aschbacher–Smith F.3.3 and F.4.6,
printed pp.270 and 276.
-/
@[expose] public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph BasedWalk
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
variable (i : Bool) (a b : G) (ha : a ∈ F i) (hb : b ∈ F (!i))
include ha in
private theorem fixes_start : a • base F i = base F i := by
  change a ∈ stabilizer F (base F i)
  simpa only [stabilizer,base,stabilizer_base] using ha
include hb in
private theorem fixes_next : b • base F (!i) = base F (!i) := by
  change b ∈ stabilizer F (base F (!i))
  simpa only [stabilizer,base,stabilizer_base] using hb
private theorem edge : (graph F).Adj (base F i) (base F (!i)) :=
  ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
include hb in
private theorem adj1 : (graph F).Adj (base F (!i)) (b • base F i) := by
  have h := (translationGraphIso F b).toHom.map_adj (edge F i).symm
  change (graph F).Adj (b • base F (!i)) (b • base F i) at h
  rwa [fixes_next F i b hb] at h
include ha in
private theorem adj2 : (graph F).Adj (b • base F i) ((b*a) • base F (!i)) := by
  have h := (translationGraphIso F (b*a)).toHom.map_adj (edge F i)
  change (graph F).Adj ((b*a) • base F i) ((b*a) • base F (!i)) at h
  simpa only [mul_smul,fixes_start F i a ha] using h
include hb in
private theorem adj3 : (graph F).Adj ((b*a) • base F (!i)) ((b*a*b) • base F i) := by
  have h := (translationGraphIso F (b*a*b)).toHom.map_adj (edge F i).symm
  change (graph F).Adj ((b*a*b) • base F (!i)) ((b*a*b) • base F i) at h
  simpa only [mul_smul,fixes_next F i b hb] using h
include ha in
private theorem adj4 : (graph F).Adj ((b*a*b) • base F i) ((b*a*b*a) • base F (!i)) := by
  have h := (translationGraphIso F (b*a*b*a)).toHom.map_adj (edge F i)
  change (graph F).Adj ((b*a*b*a) • base F i) ((b*a*b*a) • base F (!i)) at h
  simpa only [mul_smul,fixes_start F i a ha] using h

def alternatingFive : BasedWalk (graph F) 5 (base F i) :=
  ⟨⟨base F (!i),by exact edge F i⟩,⟨⟨b • base F i,by exact adj1 F i b hb⟩,
    ⟨⟨(b*a) • base F (!i),by exact adj2 F i a b ha⟩,
      ⟨⟨(b*a*b) • base F i,by exact adj3 F i a b hb⟩,
        ⟨⟨(b*a*b*a) • base F (!i),by exact adj4 F i a b ha⟩,PUnit.unit⟩⟩⟩⟩⟩

theorem alternatingFive_vertices : (alternatingFive F i a b ha hb).vertices =
    [base F i, base F (!i), b • base F i, (b*a) • base F (!i),
      (b*a*b) • base F i, (b*a*b*a) • base F (!i)] := rfl

theorem alternatingFive_nonbacktracking (hna : a ∉ F (!i)) (hnb : b ∉ F i) :
    (alternatingFive F i a b ha hb).Nonbacktracking := by
  have hnb' : b • base F i ≠ base F i := by
    intro he
    apply hnb
    have hm : b ∈ stabilizer F (base F i) := he
    simpa only [stabilizer,base,stabilizer_base] using hm
  have hna' : a • base F (!i) ≠ base F (!i) := by
    intro he
    apply hna
    have hm : a ∈ stabilizer F (base F (!i)) := he
    simpa only [stabilizer,base,stabilizer_base] using hm
  have hba : (b*a) • base F (!i) ≠ base F (!i) := by
    intro he
    apply hna'
    have he' := congrArg (fun v : Vertex F => b⁻¹ • v) he
    simpa only [mul_smul,inv_smul_smul,inv_smul_eq_iff.mpr (fixes_next F i b hb).symm] using he'
  refine ⟨hnb', hba, ?_, ?_, trivial⟩
  · intro he
    change (b*a*b) • base F i = b • base F i at he
    apply hnb'
    have he' := congrArg (fun v : Vertex F => a⁻¹ • (b⁻¹ • v)) he
    simpa only [mul_smul,inv_smul_smul,inv_smul_eq_iff.mpr (fixes_start F i a ha).symm] using he'
  · intro he
    change (b*a*b*a) • base F (!i) = (b*a) • base F (!i) at he
    apply hba
    apply (MulAction.toPerm (b*a)).injective
    simpa only [MulAction.toPerm_apply, ← mul_smul, mul_assoc] using he

theorem alternatingFive_fixer_le : pathStabilizer F (alternatingFive F i a b ha hb) ≤
    (F i ⊓ F (!i)) ⊓ (F i ⊓ F (!i)).comap (MulAut.conj (b*a*b*a)⁻¹).toMonoidHom := by
  intro g hg
  have h0 := hg (base F i) (by simp [alternatingFive_vertices])
  have h1 := hg (base F (!i)) (by simp [alternatingFive_vertices])
  have h4 := hg ((b*a*b) • base F i) (by simp [alternatingFive_vertices])
  have h5 := hg ((b*a*b*a) • base F (!i)) (by simp [alternatingFive_vertices])
  have h4' : g • ((b*a*b*a) • base F i) = (b*a*b*a) • base F i := by
    simpa only [mul_smul, fixes_start F i a ha] using h4
  have mem_of_fix {j : Bool} {x : G} (hx : x • base F j = base F j) : x ∈ F j := by
    have hh : x ∈ stabilizer F (base F j) := hx
    simpa only [stabilizer,base,stabilizer_base] using hh
  refine ⟨⟨mem_of_fix h0, mem_of_fix h1⟩, ?_⟩
  change (b*a*b*a)⁻¹ * g * ((b*a*b*a)⁻¹)⁻¹ ∈ F i ⊓ F (!i)
  rw [inv_inv]
  constructor
  · apply mem_of_fix
    rw [mul_smul, mul_smul, h4', inv_smul_smul]
  · apply mem_of_fix
    rw [mul_smul, mul_smul, h5, inv_smul_smul]
end Subgroup.CosetGeometry.RankTwo
