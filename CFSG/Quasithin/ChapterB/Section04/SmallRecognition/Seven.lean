module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Nontrivial binary A₇ modules of dimension at most eight

Pull the action back along the supplied A₇ marking. Simplicity makes the
nontrivial action faithful. The independently proved binary spectrum is
4, 6, 14 below degree nineteen; the source cutoff excludes fourteen.
Its proof constructs actual absolutely irreducible models and exhausts them
using the odd-order conjugacy-class count, without a classification premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.11, printed p.96.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterB.SmallRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- B.4.11, retaining the actual A₇ isomorphism and nontrivial action. -/
theorem lemma_B_4_11 (e : G ≃* alternatingGroup (Fin 7))
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hρ : ∃ g, ρ g ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 6 := by
  let τ := ρ.comp e.symm.toMonoidHom
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  have hf : Function.Injective τ := by
    rcases (inferInstance : τ.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact τ.ker_eq_bot_iff.mp hk
    · obtain ⟨g, hg⟩ := hρ
      have hm : e g ∈ τ.ker := hk ▸ Subgroup.mem_top _
      exact (hg (by simpa [τ] using hm)).elim
  rcases CFSG.Quasithin.ChapterK.Alternating.sevenSmallDegreeSpectrum τ hf inferInstance
      (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · omega

end CFSG.Quasithin.ChapterB.SmallRecognition
