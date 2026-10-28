module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Images

/-!
# Generation by both local sections in 13.8.6(4)

The first section generates because U_L = ⟨U_H^L⟩. For the second,
suppose a proper invariant kernel kills U₂. Irreducibility of the first
local section gives U_H ∩ W ≤ V. Then ⟨V₃^{K₂}⟩ ≤ U_H ∩ U₂ lies
in V ∩ U_H = V₃. Interchanging the K₂ and L₂ spans forces U₂ ≤ V,
contrary to U₂ ≠ V. This supplies the missing justification for the
word “similarly” on printed p.948 of Aschbacher–Smith (1 March 2004).

The local irreducible actions are explicit inputs to this generation
calculation. Constructing their natural-module identifications remains
necessary for the source theorem.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

variable {G A X : Type*} [Group G] [Group A] [AddCommGroup X] [Module (ZMod 2) X]

/-- Lift commutator generation across V₁ using the actual source identity
V₁ = [V₃,O₂(L₁)], rather than discarding that line. -/
theorem UH_eq_commutator_of_mod_line (H L₁ V₃ V₁ : Subgroup G)
    (hL₁H : L₁ ≤ H)
    (hmod : Source.UH H V₃ ≤ ⁅Source.UH H V₃, L₁⁆ ⊔ V₁)
    (hline : V₁ = ⁅V₃, L₁.pCoreIn 2⁆) :
    Source.UH H V₃ = ⁅Source.UH H V₃, L₁⁆ := by
  have hline' : V₁ ≤ ⁅Source.UH H V₃, L₁⁆ := by
    rw [hline]
    exact commutator_mono (le_conjugateSpanBy V₃ H) (pCoreIn_le 2 L₁)
  exact le_antisymm (hmod.trans (sup_le le_rfl hline'))
    (le_normalizer_iff_commutator_le_left.mp
      (hL₁H.trans (le_normalizer_conjugateSpanBy V₃ H)))

/-- Killing U₂ while intersecting U_H only inside V contradicts U₂ ≠ V.
The proof uses the two conjugate spans, not rank alone. -/
theorem U2_not_le_of_intersection (H L₂ V V₂ V₃ W : Subgroup G)
    (hgen : V = conjugateSpanBy V₃ L₂)
    (hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G))
    (hinter : V ⊓ Source.UH H V₃ = V₃)
    (hUW : Source.UH H V₃ ⊓ W ≤ V)
    (hne : Source.U2 H V V₂ ≠ V) : ¬ Source.U2 H V V₂ ≤ W := by
  intro hkill
  let D := conjugateSpanBy V₃ (Source.K2 H V₂)
  have hDU : D ≤ Source.UH H V₃ := conjugateSpanBy_mono le_rfl (Source.K2_le H V₂)
  have hDV₃ : D ≤ V₃ := by
    rw [← hinter]
    refine le_inf ?_ hDU
    apply (le_inf hDU ?_).trans hUW
    apply le_trans (conjugateSpanBy_mono ?_ le_rfl) hkill
    exact hgen.symm ▸ le_conjugateSpanBy V₃ L₂
  apply hne
  apply le_antisymm _ (Source.seed_le_U2 H V V₂)
  change conjugateSpanBy V (Source.K2 H V₂) ≤ V
  rw [hgen]
  exact (conjugate_span_le_iterated_span V₃ L₂ (Source.K2 H V₂) hKL).trans
    (conjugateSpanBy_mono hDV₃ le_rfl)

/-- The full actor's span of a local subrepresentation, with its invariance. -/
def fullOrbit (ρ : Representation (ZMod 2) A X) (P : Subgroup A)
    (S : Subrepresentation (ρ.comp P.subtype)) : Subrepresentation ρ where
  toSubmodule := Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S, x = ρ a (s : X)}
  apply_mem_toSubmodule a x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, s, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨a * b, s, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    | zero => simpa only [map_zero] using (Submodule.zero_mem _)
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

theorem le_fullOrbit (ρ : Representation (ZMod 2) A X) (P : Subgroup A)
    (S : Subrepresentation (ρ.comp P.subtype)) :
    S.toSubmodule ≤ (fullOrbit ρ P S).toSubmodule := by
  intro s hs
  exact Submodule.subset_span ⟨1, ⟨s, hs⟩, by simp⟩

variable (B Z : Subgroup G) [(Z.subgroupOf B).Normal]
  [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)]
  (P : Subgroup G) (π : P →* A) (hPB : P ≤ normalizer (B : Set G))
  (ρ : Representation (ZMod 2) A (Additive (B ⧸ Z.subgroupOf B)))
  (hρ : SectionConjugationAlong P B Z π hPB ρ)

/-- Subgroup conjugate generation implies full module generation by its
literal local image. -/
theorem localImage_spans_of_conjugateSpan (D L R : Subgroup G)
    (hRD : R ≤ normalizer (D : Set G)) (hLP : L ≤ P)
    (hB : B = conjugateSpanBy D L) :
    Submodule.span (ZMod 2) {x | ∃ a : A,
      ∃ s : localImage B Z P π hPB ρ hρ R D hRD, x = ρ a (s : _)} = ⊤ := by
  let S := localImage B Z P π hPB ρ hρ R D hRD
  let W := fullOrbit ρ ((R.subgroupOf P).map π) S
  have hDB : D ≤ B := hB.symm ▸ le_conjugateSpanBy D L
  have hD : D ≤ sectionPreimage B Z W.toSubmodule :=
    (sectionImage_le_iff B Z D hDB W.toSubmodule).mp (le_fullOrbit ρ _ S)
  apply (sectionPreimage_eq_iff_top B Z W.toSubmodule).mp
  apply le_antisymm (sectionPreimage_le B Z W.toSubmodule)
  exact hB.le.trans (conjugateSpanBy_le hD
    (hLP.trans (sectionPreimage_normalized B Z P π hPB ρ hρ W)))

/-- If a generating local section is irreducible, its intersection with
any proper full invariant kernel lies in the denominator. -/
theorem intersection_le_denominator (D R : Subgroup G)
    (hDB : D ≤ B) (hRD : R ≤ normalizer (D : Set G))
    [IsIrreducible (localImage B Z P π hPB ρ hρ R D hRD).toRepresentation]
    (hgen : Submodule.span (ZMod 2) {x | ∃ a : A,
      ∃ s : localImage B Z P π hPB ρ hρ R D hRD, x = ρ a (s : _)} = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) :
    D ⊓ sectionPreimage B Z W.toSubmodule ≤ Z := by
  intro d hd
  let b : B := ⟨d, hDB hd.1⟩
  let s : (localImage B Z P π hPB ρ hρ R D hRD).toSubmodule :=
    ⟨Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) b), ⟨b, hd.1, rfl⟩⟩
  have hs : localQuotientMap ρ _ (localImage B Z P π hPB ρ hρ R D hRD) W s = 0 :=
    (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr
      ((mem_sectionPreimage B Z W.toSubmodule b).mp hd.2)
  have hs0 : s = 0 := localQuotientMap_injective ρ _ _ hgen W hW
    (hs.trans (map_zero _).symm)
  exact (QuotientGroup.eq_one_iff b).mp (congrArg Subtype.val hs0)

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
