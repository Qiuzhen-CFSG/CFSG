module
public import Theory.GroupAction.CubicTree.TrackConjugation
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackSetup

/-!
# An arbitrary source track through the base edge

Choose the endpoint of the first edge lying in the first vertex class. A
reversal and shift put it first, and the literal coset action conjugates
that ordered edge onto the base edge. The conjugation map carries the new
track fixer onto the original one. This preserves the actual groups used
when Goldschmidt (6.11) applies (5.3) to newly constructed tracks.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup Theory.GroupTheory Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- An arbitrary track can be conjugated onto the literal base edge. The
source-type endpoint is one of the original two vertices, and conjugation
retains its exact pointwise fixer. -/
theorem exists_base_track_conjugate (t : Track (RankTwo.graph F) G) :
    ∃ (u : Track (RankTwo.graph F) G) (g : G) (i : Fin 2),
      u.vertex 0 = RankTwo.base F false ∧ u.vertex 1 = RankTwo.base F true ∧
      g • u.vertex 0 = t.vertex (i : ℤ) ∧
      u.fixer.map (MulAut.conj g).toMonoidHom = t.fixer := by
  have normalize (w : Track (RankTwo.graph F) G) (i : Fin 2)
      (hw0 : (w.vertex 0).type = false) (hwi : w.vertex 0 = t.vertex (i : ℤ))
      (hwQ : w.fixer = t.fixer) :
      ∃ (u : Track (RankTwo.graph F) G) (g : G) (i : Fin 2),
        u.vertex 0 = RankTwo.base F false ∧ u.vertex 1 = RankTwo.base F true ∧
        g • u.vertex 0 = t.vertex (i : ℤ) ∧
        u.fixer.map (MulAut.conj g).toMonoidHom = t.fixer := by
    have hw1 : (w.vertex 1).type = true := by
      have hh := (w.adjacent 0).1
      change (w.vertex 0).type ≠ (w.vertex 1).type at hh
      rw [hw0] at hh
      cases hh1 : (w.vertex 1).type <;> simp_all
    obtain ⟨g,hg0,hg1⟩ := RankTwo.incident_common_translate F (w.adjacent 0).2
    change g • RankTwo.base F (w.vertex 0).type = w.vertex 0 at hg0
    change g • RankTwo.base F (w.vertex 1).type = w.vertex 1 at hg1
    rw [hw0] at hg0
    rw [hw1] at hg1
    let u := w.conjugate trackGraphAction g⁻¹
    refine ⟨u,g,i,?_,?_,?_,?_⟩
    · change g⁻¹ • w.vertex 0 = RankTwo.base F false
      rw [← hg0,inv_smul_smul]
    · change g⁻¹ • w.vertex 1 = RankTwo.base F true
      rw [← hg1,inv_smul_smul]
    · change g • (g⁻¹ • w.vertex 0) = _
      rw [smul_inv_smul,hwi]
    · rw [Track.conjugate_fixer,map_map]
      have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id G := by
        ext x
        change g * (g⁻¹*x*(g⁻¹)⁻¹) * g⁻¹ = x
        group
      rw [he,map_id,hwQ]
  cases ht : (t.vertex 0).type
  · exact normalize t 0 ht rfl rfl
  · let w := t.reverse.shift (-1)
    have hw : (w.vertex 0).type = false := by
      change (t.vertex 1).type = false
      have hh := (t.adjacent 0).1
      change (t.vertex 0).type ≠ (t.vertex 1).type at hh
      rw [ht] at hh
      cases hh1 : (t.vertex 1).type <;> simp_all
    exact normalize w 1 hw rfl (by rw [Track.shift_fixer,Track.reverse_fixer])

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
