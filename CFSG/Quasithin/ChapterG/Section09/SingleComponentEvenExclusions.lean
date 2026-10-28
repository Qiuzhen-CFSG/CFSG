module
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentSharpExclusions
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.SelfDual
public import Theory.Representation.SL5ExteriorSquare.SelfDual
public import Theory.Representation.Quotient
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Source
public import Theory.Representation.Mathieu.M24DegreeSpectrum

/-!
# Even-degree single-component exclusions

The automorphism rank bound excludes M₂₃. The absolute small-degree spectrum
excludes even-dimensional M₂₄ modules, and the natural and exterior-square
recognition excludes self-dual binary SL₅(2) modules. These statements retain
the actual G.9 component action and its original rank bound.

Source: Aschbacher--Smith G.9 and the model analysis in G.11.7.
-/

open scoped MatrixGroups
open Subgroup Theory.GroupTheory Module Representation
public section
namespace CFSG.Quasithin.ChapterG.Section09
open Sporadic.Mathieu
variable {D V : Type*} [_root_.Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {K : GroupClass} {ρ : Representation (ZMod 2) D V} {L A : Subgroup D} {m : ℕ}
  (h : ComponentHypothesis K ρ A L L m)
include h

theorem ComponentHypothesis.not_m23
    (e : L ≃* M23) : False := by
  have hb := h.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hb
  have hr := m23_automorphism_twoRank_le_four
  have hl := Section07.MathieuRecognition.eleven_le_finrank_of_m23
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e
  omega

theorem ComponentHypothesis.not_m24_of_even_degree
    (heven : Even (finrank (ZMod 2) V)) (e : L ≃* M24) : False := by
  let : _root_.Group.IsPerfect L := h.component.2.toIsPerfect
  let : _root_.Group.IsPerfect M24 := _root_.Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  have hz : center M24 = ⊥ := by
    rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (_root_.Group.IsPerfect.not_isMulCommutative M24 (center_eq_top_iff.mp ht)).elim
  have hb := h.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hb
  have hr := m24_automorphism_rank_le_six hz
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hdeg := Representation.Mathieu.M24DegreeSpectrum.finrank_cases_of_absolute_spectrum σ
    Representation.Mathieu.M24DegreeSpectrum.absoluteSmallSpectrum hf (by omega)
  obtain ⟨a,ha⟩ := heven
  rcases hdeg with hd | hd | hd | hd <;> omega

theorem DefiningCharacteristic.BinaryLinearRecognition.not_five_of_selfDual
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
    (e : L ≃* PSL(5,ZMod 2)) : False := by
  have hb := DefiningCharacteristic.BinaryLinearRecognition.five_degree_parameters h e
  rcases hb.2 with h5 | h10
  · exact Representation.BinaryLinearRecognition.not_natural_degree_of_selfDual
      (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hs (by decide) e h5.1
  · let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
    exact Representation.SL5ExteriorSquare.not_selfDual_of_finrank_ten (ρ.comp L.subtype)
      (e.trans Representation.SL5TenDimensional.projectiveEquiv.symm) h10.1 hs

theorem ComponentHypothesis.not_even_models
    (heven : Even (finrank (ZMod 2) V))
    (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
    (model : Nonempty (L ≃* M23) ∨ Nonempty (L ≃* M24) ∨ Nonempty (L ≃* PSL(5,ZMod 2))) : False := by
  rcases model with h23 | h24 | h5
  · exact h.not_m23 h23.some
  · exact h.not_m24_of_even_degree heven h24.some
  · exact DefiningCharacteristic.BinaryLinearRecognition.not_five_of_selfDual h hs h5.some
end CFSG.Quasithin.ChapterG.Section09
