module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductFactors
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSubgroups

/-!
# The literal omega-center and full action for the terminal local factors

Restrict the supplied LocalAnalysis to its original natural L-coordinates.
Its weight-six centralizer bound discharges the point premise of source
12.3.7. Coordinate separation shows that the resulting normalizer action
is exactly the supplied permutation map, so its image is all of S₇.

Specializing the core-omega decomposition to the trivial subcomponent gives
Ω₁Z(T)=C_{Ω₁Z(T)}(L)∨(Ω₁Z(T)∩V). The final application supplies these two
fields of TerminalPoint.LocalFactorAnalysis. Construction of the residual
factors and the marked product remains with qt-d-1231-terminal-product.
Source: Aschbacher--Smith, 12.3.7(1) and completion of 12.3.1, pp.809,811--812.
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

/-- The existing literal coordinates, restricted to the original L-action. -/
def naturalCoordinates : S.NaturalCoordinates where
  coordinates := D.model.coordinates
  equivariant l v := by
    simpa only [D.component_action] using
      D.model.equivariant ⟨l,S.chosen.normalizes l.property⟩ v

private theorem weight_six_centralizer (z : V)
    (_hz : (z : G) ∈ centralizer (T : Set G))
    (hw : weight (D.naturalCoordinates.coordinates z).toAdd.val = 6) :
    centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) := by
  apply D.pointCentralizers z _ (Or.inr hw)
  intro h
  have hw' : weight (D.model.coordinates z).toAdd.val = 6 := hw
  rw [h,map_one] at hw'
  have hz : weight (0 : Word) = 0 := by decide
  exact (by decide : (0 : ℕ) ≠ 6) (hz.symm.trans hw')

include D in
/-- Transport of source 12.3.7 to the supplied local analysis. -/
theorem thompson_generation
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ :=
  D.naturalCoordinates.thompson_generation_of_weight_six structural escape
    D.weight_six_centralizer

private theorem source_permutation_eq
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (n : normalizer (V : Set G)) :
    (D.naturalCoordinates.sourceNormalizerModel structural).permutation n =
      D.model.permutation n := by
  have hs : ((D.naturalCoordinates.sourceNormalizerModel structural).permutation n).symm =
      (D.model.permutation n).symm := by
    apply Equiv.ext
    intro i
    apply coordinates_separated
    intro w hw
    let v : V := D.model.coordinates.symm
      (Multiplicative.ofAdd (⟨w,simplexCode_le_evenWords hw⟩ : EvenWord))
    have h₁ := (D.naturalCoordinates.sourceNormalizerModel structural).equivariant n v
    have h₂ := D.model.equivariant n v
    have h := h₁.symm.trans h₂
    change evenRepresentation
      ((D.naturalCoordinates.sourceNormalizerModel structural).permutation n)
        (D.model.coordinates v).toAdd =
      evenRepresentation (D.model.permutation n) (D.model.coordinates v).toAdd at h
    have he := congrArg (fun x : EvenWord => x.val i) h
    simpa only [v,D.model.coordinates.apply_symm_apply,toAdd_ofAdd,
      evenRepresentation_apply] using he
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hs

/-- The supplied permutation map has the full S₇ image, not just an
abstractly isomorphic image. -/
theorem permutation_range_eq_top
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : D.model.permutation.range = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro a
  obtain ⟨n,hn⟩ := D.naturalCoordinates.permutation_surjective_of_thompson_generation
    structural (D.thompson_generation structural escape) a
  exact ⟨n,(D.source_permutation_eq structural n).symm.trans hn⟩

include D in
/-- The central omega seed splits in the original Sylow group. -/
theorem omega_split
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    omegaCenterIn (T : Subgroup G) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔
        (omegaCenterIn (T : Subgroup G) ⊓ V) := by
  have hT : (T : Subgroup G).pCoreIn 2 = (T : Subgroup G) :=
    le_antisymm (pCoreIn_le 2 _) (le_pCoreIn_of_normalizes T.isPGroup' le_rfl
      (T : Subgroup G).le_normalizer)
  have h := (D.naturalCoordinates.subjoin_core_omega_decomposition_of_weight_six
    structural escape D.weight_six_centralizer ⊥ bot_le).1
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

/-- The omega-center field of the literal local-factor analysis. -/
theorem omega_split
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    P.Z = (P.Z ⊓ centralizer (L : Set G)) ⊔ (P.Z ⊓ V) :=
  D.omega_split structural escape

/-- Both 12.3.7 inputs to the literal terminal local-factor construction. -/
theorem local_factor_omega_and_action
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    P.Z = (P.Z ⊓ centralizer (L : Set G)) ⊔ (P.Z ⊓ V) ∧
      D.model.permutation.range = ⊤ :=
  ⟨P.omega_split structural escape,D.permutation_range_eq_top structural escape⟩
end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
