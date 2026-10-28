module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Complete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SymplecticExcluded

/-!
# The three remaining original marked non-FF doubled rows

The original binary natural three-, four- and five-space rows and every
nonbinary symplectic row are excluded by their actual source proofs. The
unchanged chosen seed of a remaining non-FF doubled orbit is therefore a
nonbinary natural three-space, the alternating six-space, or the faithful
four-dimensional alternating-seven row. These are exact remaining source
alternatives, not a complete doubled exclusion.
Source: Aschbacher--Smith 7.1--7.7, 12.1.11 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
/-- The literal nonbinary-linear, alternating-six, and alternating-seven seed rows. -/
@[expose] def NonFFRemainingDoubledRows
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) : Prop :=
    (∃ F : BinaryField, 1 < F.degree ∧
      Nonempty (ActionEquiv ρ
        (linearNatural F 3))) ∨
    Nonempty (ActionEquiv ρ
      (alternatingNatural 6)) ∨
    ∃ σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2),
      Function.Injective σ ∧
      Nonempty (ActionEquiv ρ σ)

private theorem remaining_of_constituent
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W)
    (hc : Chapter3.Section02.ChosenSource325.ConstituentModel ρ)
    (hbinary : ∀ F : BinaryField, F.degree = 1 →
      ¬ Nonempty (ActionEquiv ρ (linearNatural F 3)))
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      ¬ Nonempty (ActionEquiv ρ
        (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    (hlarge : ∀ n, n = 4 ∨ n = 5 →
      ¬ Nonempty (ActionEquiv ρ (linearNatural BinaryField.two n))) :
    NonFFRemainingDoubledRows ρ := by
  rcases hc with ⟨F,hF⟩ | ⟨F,hn,hF⟩ | hF | ⟨n,hn,hF⟩ | ⟨σ,hσ,hF⟩
  · by_cases hn : F.degree = 1
    · exact (hbinary F hn hF).elim
    · exact Or.inl ⟨F,by have := F.degree_pos; omega,hF⟩
  · exact (hsymplectic F hn hF).elim
  · exact Or.inr (Or.inl hF)
  · exact (hlarge n hn hF).elim
  · exact Or.inr (Or.inr ⟨σ,hσ,hF⟩)

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original non-FF marked doubled seed has only these three rows left. -/
theorem sourceOrbit_nonFF_markedDoubled_remaining_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    NonFFRemainingDoubledRows (D.seedRepresentation.comp D.componentImage.subtype) := by
  apply remaining_of_constituent _ hd.2.1
  · intro F hF hm
    exact hnon (D.sourceOrbit_binary_natural_three_ff h hd hmany F hF hm)
  · intro F hF hm
    exact D.sourceOrbit_symplectic_excluded h hd hmany hnon F hF hm
  · intro n hn hm
    exact hnon (D.sourceOrbit_isFF_of_markedDoubled_binaryNatural h hd hn hm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
