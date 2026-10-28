module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic

/-!
# The earlier source input for 13.8.12

Lemma 13.3.9 is used universally, with its actual outside-overgroup family,
relative normality, two-perfectness, and centralizer hypothesis. Its barred
subgroups are images of the conjugation action on V, not abstract family tags.
Both exceptional quotient identifications and the equality of barred images
are retained. The §13.8 assembly must supply this earlier theorem and the
standing local data; this file does not assert 13.3.9.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.887
(13.3.9), and p.950 (13.8.12).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The literal barred image in the action of M_V on V. -/
def barImage (M V Y : Subgroup G) : Subgroup (MulAut V) :=
  (Y.subgroupOf (M ⊓ normalizer (V : Set G))).map
    (V.normalizerMonoidHom.comp (inclusion inf_le_right))

/-- Full conclusion of 13.3.9, including the barred equality and both
conditional exceptional identifications. Normalization of V is established
at the start of the source proof, so the barred image is the image of all of Y. -/
def Conclusion1339 (L L₁ L₁plus M V Y : Subgroup G) : Prop :=
  Y = ⊥ ∨ (Y ≤ M ⊓ normalizer (V : Set G) ∧
    barImage M V Y = barImage M V L₁ ∧
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) → Y = L₁) ∧
    (IsTripleCoverSix (L ⧸ pCore 2 L) → Y = L₁plus))

/-- The precise universal earlier theorem used below. In particular, it is
not a contradiction specialized to the residual or to a chosen component. -/
def Source1339 (L L₁ L₁plus T M V V₁ : Subgroup G) : Prop :=
  Nonempty (barImage M V L ≃* alternatingGroup (Fin 6)) →
  ∀ J Y : Subgroup G, J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) →
    Y ≤ J → IsPPerfect 2 Y → (Y.subgroupOf J).Normal →
    (∃ v ∈ V₁, v ∉ V ⊓ centralizer (L : Set G) ∧
      Y ≤ M ⊓ centralizer ({v} : Set G)) →
    Conclusion1339 L L₁ L₁plus M V Y

/-- Selecting the applicable exceptional identification uses the actual
quotient alternatives, supplied by the earlier chapter results. -/
theorem alternative_of_1339 {L L₁ L₁plus M V Y : Subgroup G}
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      IsTripleCoverSix (L ⧸ pCore 2 L))
    (h : Conclusion1339 L L₁ L₁plus M V Y) :
    ResidualAlternative L L₁ L₁plus Y := by
  rcases h with hb | ⟨_, _, ha, hc⟩
  · exact Or.inl hb
  · rcases hmodels with hm | hm
    · exact Or.inr (Or.inl ⟨hm, ha hm⟩)
    · exact Or.inr (Or.inr ⟨hm, hc hm⟩)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
end
