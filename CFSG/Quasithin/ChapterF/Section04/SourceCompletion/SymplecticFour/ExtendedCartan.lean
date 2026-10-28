module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Cartan
public import Theory.SpecificGroups.SymplecticFour.WeylFrame
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer

/-!
# The Cartan centralizer inside the full symplectic extension Borel

The exact inner intersection makes each marked-middle automorphism preserve
the native Borel. Pointwise fixation of the full native torus makes its
induced torus-quotient action trivial; the proved automorphism classification
then makes it inner. The native Borel centralizer calculation identifies it
as a torus element. Transport through the faithful middle map gives the same
centralizer in every completion, including arbitrary field-extension degree.

This discharges the extended-Borel algebraic step of the Cartan route in
Aschbacher–Smith F.4.10 and F.4.16, printed pp.279,282 of
`refs/quasithin.pdf`. It does not assert that the marked Weyl path closes.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
namespace SourceExtension
variable (E : SourceExtension F)

/-- Every marked-middle automorphism preserves the native Borel. -/
theorem middle_map_borel (a : E.middle) : (borel (F := F)).map a.val.toMonoidHom = borel := by
  apply eq_of_le_of_card_ge
  · rintro x ⟨b,hb,rfl⟩
    have hbi : MulAut.conj b ∈ E.middle ⊓ inner F := E.middle_inner.ge ⟨b,hb,rfl⟩
    have hconj : MulAut.conj (a.val b) = a.val * MulAut.conj b * a.val⁻¹ := by
      ext x
      simp
    have hm : MulAut.conj (a.val b) ∈ E.middle ⊓ inner F := by
      refine ⟨?_,⟨_,rfl⟩⟩
      rw [hconj]
      exact E.middle.mul_mem (E.middle.mul_mem a.property hbi.1) (E.middle.inv_mem a.property)
    obtain ⟨g,hg,he⟩ := E.middle_inner.le hm
    exact inner_injective (F := F) he ▸ hg
  · rw [card_map_of_injective a.val.injective]

/-- An element of the extended Borel centralizing the inner Cartan is itself
an inner Cartan element. Field-automorphism factors are retained and eliminated
by their action on the full torus quotient. -/
theorem middle_centralizer_torus {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (a : E.middle)
    (hc : ∀ p : Fˣ × Fˣ, a.val * MulAut.conj (diagonalTorus p.1 p.2) =
      MulAut.conj (diagonalTorus p.1 p.2) * a.val) :
    ∃ p : Fˣ × Fˣ, a.val = MulAut.conj (diagonalTorus p.1 p.2) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1<2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hfix (p : Fˣ × Fˣ) : a.val (diagonalTorus p.1 p.2) = diagonalTorus p.1 p.2 := by
    apply inner_injective (F := F)
    have he : MulAut.conj (a.val (diagonalTorus p.1 p.2)) =
        a.val * MulAut.conj (diagonalTorus p.1 p.2) * a.val⁻¹ := by
      ext x
      simp
    rw [he,hc p,mul_inv_cancel_right]
  let aU : EvenBorelTorus.ActorReduction.stabilizer (F := F) :=
    ⟨a.val,EvenBorelTorus.FullTorusFixer.map_unipotent_of_map_borel hF a.val (E.middle_map_borel a)⟩
  have ht : EvenBorelTorus.ActorReduction.torusAction hF aU = 1 := by
    apply MulEquiv.ext
    intro x
    rw [←EvenBorelTorus.characters_torusSection x,
      EvenBorelTorus.ActorReduction.torusAction_characters]
    have hb : EvenBorelTorus.ActorReduction.borelAction aU (EvenBorelTorus.torusSection x) =
        EvenBorelTorus.torusSection x := Subtype.ext (hfix (x.1,x.1⁻¹*x.2))
    rw [hb]
    rfl
  obtain ⟨g,hg⟩ := (EvenBorelTorus.ActorReduction.torusAction_eq_one_iff_inner hF hn
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram aU).mp ht
  have hgb : g ∈ borel (F := F) := by
    have hm : MulAut.conj g ∈ E.middle ⊓ inner F := ⟨hg ▸ a.property,⟨g,rfl⟩⟩
    obtain ⟨b,hb,he⟩ := E.middle_inner.le hm
    exact inner_injective (F := F) he ▸ hb
  have hgc : g ∈ centralizer ((CentralRootGeometry.diagonalTorusHom (F := F)).range : Set (Sp F)) := by
    rintro t ⟨p,rfl⟩
    have hh := hfix p
    rw [←hg] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨p,hp⟩ := (WeylFrame.borel_inf_centralizer_torus hq).le ⟨hgb,hgc⟩
  exact ⟨p,hg.symm.trans (congrArg MulAut.conj hp.symm)⟩
end SourceExtension

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)

/-- The full extended overlap has precisely the native torus as its torus centralizer. -/
theorem middle_inf_centralizer_torus {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    c.middle.range ⊓ centralizer (c.torusMap.range : Set M) = c.torusMap.range := by
  apply le_antisymm
  · rintro x ⟨⟨a,rfl⟩,hc⟩
    have hh : ∀p : Fˣ × Fˣ, a.val * MulAut.conj (diagonalTorus p.1 p.2) =
        MulAut.conj (diagonalTorus p.1 p.2) * a.val := by
      intro p
      have he := hc (c.torusMap p) ⟨p,rfl⟩
      have he' : E.borelToMiddle (torusToBorel p) * a = a * E.borelToMiddle (torusToBorel p) := by
        apply c.middle_injective
        simpa only [map_mul,torusMap,borelMap,MonoidHom.comp_apply] using he
      exact (congrArg Subtype.val he').symm
    obtain ⟨p,hp⟩ := E.middle_centralizer_torus hF hn a hh
    exact ⟨p,congrArg c.middle (Subtype.ext hp.symm)⟩
  · refine le_inf ?_ ?_
    · rintro x ⟨p,rfl⟩
      exact ⟨_,rfl⟩
    · rintro x ⟨p,rfl⟩ y ⟨q,rfl⟩
      rw [←map_mul,←map_mul,mul_comm]
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
