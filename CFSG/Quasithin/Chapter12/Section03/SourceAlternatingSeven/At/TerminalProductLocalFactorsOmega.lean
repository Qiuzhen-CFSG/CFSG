module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsOmega
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceSubgroups
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalSelection

/-!
# TerminalProductLocalFactorsOmega at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsOmega`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.LocalAnalysis

variable (D : S.LocalAnalysis)

def naturalCoordinates_at : S.NaturalCoordinates where
  coordinates := D.model.coordinates
  equivariant l v := by
    simpa only [D.component_action] using
      D.model.equivariant ⟨l,S.chosen.normalizes l.property⟩ v

private theorem weight_six_centralizer_at (z : V)
    (_hz : (z : G) ∈ centralizer (T : Set G))
    (hw : weight (D.naturalCoordinates_at.coordinates z).toAdd.val = 6) :
    centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) := by
  apply D.pointCentralizers z _ (Or.inr hw)
  intro h
  have hw' : weight (D.model.coordinates z).toAdd.val = 6 := hw
  rw [h,map_one] at hw'
  have hz : weight (0 : Word) = 0 := by decide
  exact (by decide : (0 : ℕ) ≠ 6) (hz.symm.trans hw')

include D in

theorem thompson_generation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ :=
  D.naturalCoordinates_at.thompson_generation_of_weight_six_at structural escape
    D.weight_six_centralizer_at

private theorem source_permutation_eq_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (n : normalizer (V : Set G)) :
    (D.naturalCoordinates_at.sourceNormalizerModel_at structural).permutation n =
      D.model.permutation n := by
  have hs : ((D.naturalCoordinates_at.sourceNormalizerModel_at structural).permutation n).symm =
      (D.model.permutation n).symm := by
    apply Equiv.ext
    intro i
    apply coordinates_separated
    intro w hw
    let v : V := D.model.coordinates.symm
      (Multiplicative.ofAdd (⟨w,simplexCode_le_evenWords hw⟩ : EvenWord))
    have h₁ := (D.naturalCoordinates_at.sourceNormalizerModel_at structural).equivariant n v
    have h₂ := D.model.equivariant n v
    have h := h₁.symm.trans h₂
    change evenRepresentation
      ((D.naturalCoordinates_at.sourceNormalizerModel_at structural).permutation n)
        (D.model.coordinates v).toAdd =
      evenRepresentation (D.model.permutation n) (D.model.coordinates v).toAdd at h
    have he := congrArg (fun x : EvenWord => x.val i) h
    simpa only [v,D.model.coordinates.apply_symm_apply,toAdd_ofAdd,
      evenRepresentation_apply] using he
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hs

theorem permutation_range_eq_top_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : D.model.permutation.range = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro a
  obtain ⟨n,hn⟩ := D.naturalCoordinates_at.permutation_surjective_of_thompson_generation_at
    structural (D.thompson_generation_at structural escape) a
  exact ⟨n,(D.source_permutation_eq_at structural n).symm.trans hn⟩

include D in

theorem omega_split_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    omegaCenterIn (T : Subgroup G) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔
        (omegaCenterIn (T : Subgroup G) ⊓ V) := by
  have hT : (T : Subgroup G).pCoreIn 2 = (T : Subgroup G) :=
    le_antisymm (pCoreIn_le 2 _) (le_pCoreIn_of_normalizes T.isPGroup' le_rfl
      (T : Subgroup G).le_normalizer)
  have h := (D.naturalCoordinates_at.subjoin_core_omega_decomposition_of_weight_six_at
    structural escape D.weight_six_centralizer_at ⊥ bot_le).1
  simp only [bot_sup_eq,hT] at h
  have hfix : V ⊓ centralizer ((T : Subgroup G) : Set G) = omegaCenterIn (T : Subgroup G) ⊓ V := by
    ext x
    constructor
    · intro hx
      let := S.chosen.elementary
      exact ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow hx.1,hx.2,
        elemPow_eq_one_of_isElementaryAbelian x hx.1⟩,hx.1⟩
    · intro hx
      exact ⟨hx.2,((mem_omegaCenterIn_iff _ _).mp hx.1).2.1⟩
  rw [hfix,sup_comm] at h
  exact h

end Setup.LocalAnalysis

namespace TerminalPoint

variable {D : S.LocalAnalysis} (P : TerminalPoint S D)

theorem omega_split_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    P.Z = (P.Z ⊓ centralizer (L : Set G)) ⊔ (P.Z ⊓ V) :=
  D.omega_split_at structural escape

theorem local_factor_omega_and_action_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    P.Z = (P.Z ⊓ centralizer (L : Set G)) ⊔ (P.Z ⊓ V) ∧
      D.model.permutation.range = ⊤ :=
  ⟨P.omega_split_at structural escape,D.permutation_range_eq_top_at structural escape⟩

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

