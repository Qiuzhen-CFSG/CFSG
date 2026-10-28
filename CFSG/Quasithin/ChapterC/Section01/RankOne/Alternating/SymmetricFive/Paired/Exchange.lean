module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Stable
import Mathlib.Tactic
/-!
# The original factor exchanger activates both stable axes

A nonempty stable family has a nontrivial coordinate projection. Transport
by an actual automorphism exchanging the two factors gives the other one.
The paired stable-family theorem therefore yields the transposition product
without assuming either projection is nonempty separately.

Source: Aschbacher–Smith E.2.3(1),(3), pp.216–217.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired

private theorem fst_bot_iff (A : Subgroup (Sym × Sym)) :
    A.map (MonoidHom.fst Sym Sym) = ⊥ ↔ A ≤ (⊥ : Subgroup Sym).prod ⊤ := by
  rw [Subgroup.map_eq_bot_iff]
  have hk : (MonoidHom.fst Sym Sym).ker = (⊥ : Subgroup Sym).prod ⊤ := by ext x; simp
  rw [hk]
private theorem snd_bot_iff (A : Subgroup (Sym × Sym)) :
    A.map (MonoidHom.snd Sym Sym) = ⊥ ↔ A ≤ (⊤ : Subgroup Sym).prod ⊥ := by
  rw [Subgroup.map_eq_bot_iff]
  have hk : (MonoidHom.snd Sym Sym).ker = (⊤ : Subgroup Sym).prod ⊥ := by ext x; simp
  rw [hk]

/-- A source exchanger activates both axes of the same nonempty stable family. -/
theorem active_axes_of_exchange {P : Set (Subgroup (Sym × Sym))}
    (hP : IsStable action P) (τ : MulAut (Sym × Sym))
    (hτ : ∀ A ∈ P, A.map τ.toMonoidHom ∈ P)
    (h₁ : ((⊤ : Subgroup Sym).prod ⊥).map τ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤)
    (h₂ : ((⊥ : Subgroup Sym).prod ⊤).map τ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥) :
    (∃ A ∈ P, A.map (MonoidHom.fst Sym Sym) ≠ ⊥) ∧
      ∃ A ∈ P, A.map (MonoidHom.snd Sym Sym) ≠ ⊥ := by
  obtain ⟨A,hA⟩ := hP.1
  have hne : A ≠ ⊥ := (hP.2.1 A hA).1.1
  have hne' : A.map τ.toMonoidHom ≠ ⊥ :=
    fun h => hne ((map_eq_bot_iff_of_injective A τ.injective).mp h)
  constructor
  · by_cases hf : A.map (MonoidHom.fst Sym Sym) = ⊥
    · refine ⟨A.map τ.toMonoidHom,hτ A hA,fun hz => hne' ?_⟩
      have hl : A.map τ.toMonoidHom ≤ (⊤ : Subgroup Sym).prod ⊥ := by
        rw [←h₂]
        exact map_mono ((fst_bot_iff A).mp hf)
      have hr := (fst_bot_iff _).mp hz
      apply le_bot_iff.mp
      intro x hx
      exact Prod.ext (hr hx).1 (hl hx).2
    · exact ⟨A,hA,hf⟩
  · by_cases hf : A.map (MonoidHom.snd Sym Sym) = ⊥
    · refine ⟨A.map τ.toMonoidHom,hτ A hA,fun hz => hne' ?_⟩
      have hr : A.map τ.toMonoidHom ≤ (⊥ : Subgroup Sym).prod ⊤ := by
        rw [←h₁]
        exact map_mono ((snd_bot_iff A).mp hf)
      have hl := (snd_bot_iff _).mp hz
      apply le_bot_iff.mp
      intro x hx
      exact Prod.ext (hr hx).1 (hl hx).2
    · exact ⟨A,hA,hf⟩

/-- The paired stable-family source calculation uses an actual exchanging
actor, with no separate projection nonemptiness assumptions. -/
theorem stable_generatedBy_of_exchange {P : Set (Subgroup (Sym × Sym))}
    (hP : IsStable action P) (τ : MulAut (Sym × Sym))
    (hτ : ∀ A ∈ P, A.map τ.toMonoidHom ∈ P)
    (h₁ : ((⊤ : Subgroup Sym).prod ⊥).map τ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤)
    (h₂ : ((⊥ : Subgroup Sym).prod ⊤).map τ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥)
    (R S : Subgroup Sym) (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hDR : ChapterB.Offenders.D 5 ≤ R) (hDS : ChapterB.Offenders.D 5 ≤ S) :
    generatedBy P (R.prod S) = (ChapterB.Offenders.D 5).prod (ChapterB.Offenders.D 5) := by
  obtain ⟨hn₁,hn₂⟩ := active_axes_of_exchange hP τ hτ h₁ h₂
  exact stable_generatedBy_product hP hn₁ hn₂ R S hR hS hDR hDS
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
