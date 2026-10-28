module

public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingFive
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.Walks

/-!
# Seven-edge apartment candidates at either marked type

Two endpoint elements give a literal nonbacktracking seven-walk. Its fixer
lies in the initial Borel and its conjugate by the alternating six-letter word.
This requires neither a braid relation nor a girth assumption.

Source: Aschbacher–Smith F.3.3 and F.4.6, printed pp.270 and 276.
-/

open SimpleGraph SimpleGraph.BasedWalk
@[expose] public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
variable (i : Bool) (a b : G) (ha : a ∈ F i) (hb : b ∈ F (!i))
include ha in
private theorem fix_a : a • base F i = base F i := by
  change a ∈ stabilizer F (base F i)
  simpa only [stabilizer,base,stabilizer_base] using ha
include hb in
private theorem fix_b : b • base F (!i) = base F (!i) := by
  change b ∈ stabilizer F (base F (!i))
  simpa only [stabilizer,base,stabilizer_base] using hb
private theorem edge7 : (graph F).Adj (base F i) (base F (!i)) :=
  ⟨by change i ≠ !i; cases i <;> decide, incident_base F i (!i)⟩
include hb in
private theorem adj5 : (graph F).Adj ((b*a*b*a) • base F (!i))
    ((b*a*b*a*b) • base F i) := by
  have h := (translationGraphIso F (b*a*b*a*b)).toHom.map_adj (edge7 F i).symm
  change (graph F).Adj ((b*a*b*a*b) • base F (!i)) ((b*a*b*a*b) • base F i) at h
  simpa only [mul_smul,fix_b F i b hb] using h
include ha in
private theorem adj6 : (graph F).Adj ((b*a*b*a*b) • base F i)
    ((b*a*b*a*b*a) • base F (!i)) := by
  have h := (translationGraphIso F (b*a*b*a*b*a)).toHom.map_adj (edge7 F i)
  change (graph F).Adj ((b*a*b*a*b*a) • base F i) ((b*a*b*a*b*a) • base F (!i)) at h
  simpa only [mul_smul,fix_a F i a ha] using h

def alternatingSeven : BasedWalk (graph F) 7 (base F i) :=
  ((alternatingFive F i a b ha hb).snoc (z := (b*a*b*a*b) • base F i)
    (by exact adj5 F i a b hb)).snoc (z := (b*a*b*a*b*a) • base F (!i))
      (by exact adj6 F i a b ha)

theorem alternatingSeven_vertices : (alternatingSeven F i a b ha hb).vertices =
    [base F i, base F (!i), b • base F i, (b*a) • base F (!i),
      (b*a*b) • base F i, (b*a*b*a) • base F (!i),
      (b*a*b*a*b) • base F i,(b*a*b*a*b*a) • base F (!i)] := by
  rfl

theorem alternatingSeven_nonbacktracking (hna : a ∉ F (!i)) (hnb : b ∉ F i) :
    (alternatingSeven F i a b ha hb).Nonbacktracking := by
  have hp := alternatingFive_nonbacktracking F i a b ha hb hna hnb
  have hnb' : b • base F i ≠ base F i := hp.1
  have hba : (b*a) • base F (!i) ≠ base F (!i) := hp.2.1
  apply (nonbacktracking_snoc_iff _ _).mpr
  constructor
  · apply (nonbacktracking_snoc_iff _ _).mpr
    refine ⟨hp,?_⟩
    change (b*a*b*a*b) • base F i ≠ (b*a*b) • base F i
    intro he
    apply hnb'
    have hh := (MulAction.injective (b*a*b*a))
      (show (b*a*b*a) • (b • base F i) = (b*a*b*a) • base F i by
        simpa only [mul_smul,fix_a F i a ha] using he)
    exact hh
  · change (b*a*b*a*b*a) • base F (!i) ≠ (b*a*b*a) • base F (!i)
    intro he
    apply hba
    apply MulAction.injective (b*a*b*a)
    simpa only [←mul_smul,mul_assoc] using he

theorem alternatingSeven_fixer_le : pathStabilizer F (alternatingSeven F i a b ha hb) ≤
    (F i ⊓ F (!i)) ⊓ (F i ⊓ F (!i)).comap
      (MulAut.conj (b*a*b*a*b*a)⁻¹).toMonoidHom := by
  intro g hg
  have h0 := hg (base F i) (by simp [alternatingSeven_vertices])
  have h1 := hg (base F (!i)) (by simp [alternatingSeven_vertices])
  have h6 := hg ((b*a*b*a*b) • base F i) (by simp [alternatingSeven_vertices])
  have h7 := hg ((b*a*b*a*b*a) • base F (!i)) (by simp [alternatingSeven_vertices])
  have h6' : g • ((b*a*b*a*b*a) • base F i) = (b*a*b*a*b*a) • base F i := by
    simpa only [mul_smul,fix_a F i a ha] using h6
  have mem_of_fix {j : Bool} {x : G} (hx : x • base F j = base F j) : x ∈ F j := by
    have hh : x ∈ stabilizer F (base F j) := hx
    simpa only [stabilizer,base,stabilizer_base] using hh
  refine ⟨⟨mem_of_fix h0,mem_of_fix h1⟩,?_⟩
  change (b*a*b*a*b*a)⁻¹ * g * ((b*a*b*a*b*a)⁻¹)⁻¹ ∈ F i ⊓ F (!i)
  rw [inv_inv]
  constructor
  · apply mem_of_fix
    rw [mul_smul,mul_smul,h6',inv_smul_smul]
  · apply mem_of_fix
    rw [mul_smul,mul_smul,h7,inv_smul_smul]
end Subgroup.CosetGeometry.RankTwo
