module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Inputs
/-!
# Generation transported from the printed edge

Relative conjugate generation commutes with an actual automorphism. Edge
transitivity consequently transports source (2.3)(b) from the one printed
edge to every oriented edge. This discharges the global `Generation`
predicate used in the path argument without adding a source hypothesis.

Source: Meierfrankenfeld--Stellmacher (1993), (2.3)(b), p.857, and the
edge-transitive amalgam action of Section 2.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
open NormalizerTransfer

private theorem rightConjugate_map {G : Type*} [Group G] (A : Subgroup G)
    (g : G) (f : MulAut G) :
    (rightConjugate A g).map f.toMonoidHom = rightConjugate (A.map f.toMonoidHom) (f g) := by
  rw [rightConjugate, rightConjugate, map_map, map_map]
  congr 1
  ext x
  simp

/-- Relative conjugate generation commutes with an actual group automorphism. -/
theorem conjugatesIn_map {G : Type*} [Group G] (A K : Subgroup G) (f : MulAut G) :
    (conjugatesIn A K).map f.toMonoidHom =
      conjugatesIn (A.map f.toMonoidHom) (K.map f.toMonoidHom) := by
  apply le_antisymm
  · rw [conjugatesIn, Subgroup.map_iSup]
    apply iSup_le
    intro g
    rw [rightConjugate_map]
    exact le_iSup_of_le (⟨f g, mem_map_of_mem f.toMonoidHom g.property⟩ : K.map f.toMonoidHom) le_rfl
  · apply iSup_le
    intro g
    obtain ⟨k, hk, hg⟩ := g.property
    have hrel : rightConjugate (A.map f.toMonoidHom) (g : G) =
        (rightConjugate A k).map f.toMonoidHom := by
      rw [rightConjugate_map]
      change f k = (g : G) at hg
      rw [hg]
    rw [hrel]
    exact map_mono (le_iSup_of_le (⟨k, hk⟩ : K) le_rfl)

variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

omit [Finite M] in
/-- The source's generation premise at one oriented edge implies all its
translates. Thus `Generation` adds no hypothesis to printed (b). -/
theorem Generation.of_edge (a t : Vertex R) (ha : color R a = false)
    (hat : Adjacent R a t)
    (hgen : ∀ x ∈ Q R t, x ∉ Q R a →
      conjugatesIn (zpowers x) (stabilizer R a) ⊔ Q R t = stabilizer R a) :
    Generation R := by
  intro d u hd hdu x hx hxQ
  obtain ⟨f, hf | hf⟩ := edge_transitive R hat hdu
  · have hQa : (Q R a).map (MulAut.conj f⁻¹).toMonoidHom = Q R d := by
      rw [← Q_act, hf.1]
    have hQt : (Q R t).map (MulAut.conj f⁻¹).toMonoidHom = Q R u := by
      rw [← Q_act, hf.2]
    have hx' : x ∈ (Q R t).map (MulAut.conj f⁻¹).toMonoidHom := by rwa [hQt]
    obtain ⟨y, hy, rfl⟩ := hx'
    have hyQ : y ∉ Q R a := by
      intro hy'
      apply hxQ
      rw [← hQa]
      exact mem_map_of_mem (MulAut.conj f⁻¹).toMonoidHom hy'
    have h := congrArg (Subgroup.map (MulAut.conj f⁻¹).toMonoidHom) (hgen y hy hyQ)
    rw [Subgroup.map_sup, conjugatesIn_map, MonoidHom.map_zpowers] at h
    simpa only [← stabilizer_act, ← Q_act, hf.1, hf.2] using h
  · have hu : color R u = false := by
      rw [← hf.1, action_preserves_color]
      exact ha
    exact (adjacent_color_ne R hdu (hd.trans hu.symm)).elim

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
