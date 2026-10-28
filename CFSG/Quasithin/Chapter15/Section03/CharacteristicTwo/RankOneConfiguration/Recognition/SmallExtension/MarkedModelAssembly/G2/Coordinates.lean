module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Marking

/-!
# Coordinates for the classified G₂ block

The classified six-dimensional representation is specified by a surjection
from trace-zero octonions whose kernel is precisely the scalar identity line.
The first isomorphism theorem identifies it equivariantly with the actual
`Atlas.G2.Natural.derivedAction`. Composing only the coefficient isomorphism
preserves the quotient actor and the full `blockFixed` kernel.

Source: Aschbacher–Smith, C.1.7 and C.1.30, printed pp.123 and 135,
and the proof of 15.3.31, printed p.1132 (PDF p.1149).
The imported octonion action follows the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Representation
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly.G2Coordinates
open CentralCover CentralCover.BlockModels

/-- The quotient universal property identifies the two coefficient spaces. -/
noncomputable def coefficientEquiv
    (pi : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hs : Function.Surjective pi) (hk : pi.ker = octonionScalarLine) :
    G2.Coefficients ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ hk.symm).trans (pi.quotKerEquivOfSurjective hs)

@[simp] theorem coefficientEquiv_mk
    (pi : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hs : Function.Surjective pi) (hk : pi.ker = octonionScalarLine)
    (x : octonionTraceZero) :
    coefficientEquiv pi hs hk (Atlas.G2.Natural.mk (ZMod 2) x) = pi x := rfl

/-- Transport to the actual natural action, retaining the original quotient actor
and the literal blockFixed central kernel. -/
noncomputable def actualModel {L : Type*} [Group L]
    (rho : G2.Actor →* MulAut (Multiplicative (Fin 6 → ZMod 2)))
    (m : ChapterC.BlockModuleModel L rho)
    (pi : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hs : Function.Surjective pi) (hk : pi.ker = octonionScalarLine)
    (he : ∀ (g : G2.Actor) (x y : octonionTraceZero),
      y.val = g.val.val x.val → pi y = (rho g (Multiplicative.ofAdd (pi x))).toAdd) :
    ChapterC.BlockModuleModel L (multiplicativeAction G2.action) where
  quotientIso := m.quotientIso
  moduleIso := m.moduleIso.trans (coefficientEquiv pi hs hk).symm.toAddEquiv.toMultiplicative
  intertwining l u := by
    change Multiplicative.ofAdd ((coefficientEquiv pi hs hk).symm
      (m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L)
        (ChapterC.blockConjugate L l u))).toAdd) = _
    rw [m.intertwining]
    apply Multiplicative.toAdd.injective
    apply (coefficientEquiv pi hs hk).injective
    simp only [toAdd_ofAdd, LinearEquiv.apply_symm_apply]
    change (rho (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l))
      (m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u))).toAdd = _
    let v := (m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u)).toAdd
    obtain ⟨x, hx⟩ := hs v
    change (rho _ (Multiplicative.ofAdd v)).toAdd =
      coefficientEquiv pi hs hk (G2.action _ ((coefficientEquiv pi hs hk).symm v))
    rw [← hx, ← coefficientEquiv_mk pi hs hk x, LinearEquiv.symm_apply_apply]
    exact (he _ x (Atlas.G2.Natural.traceZeroAction (ZMod 2) _ x) rfl).symm


/-- Every classified G₂ block has a genuine model on the fixed natural carrier. -/
theorem exists_actualModel {L : Type*} [Group L] (h : IsG2TwoBlock L) :
    Nonempty (ChapterC.BlockModuleModel L (multiplicativeAction G2.action)) := by
  obtain ⟨_, rho, ⟨m⟩, pi, hs, hk, he⟩ := h
  exact ⟨actualModel rho m pi hs hk he⟩

/-- Compatible changes of actor and coefficient coordinates preserve the complete
block model, including its original central quotient. -/
noncomputable def recoordinate {L : Type*} [Group L]
    (m : ChapterC.BlockModuleModel L (multiplicativeAction G2.action))
    (f : G2.Actor ≃* G2.Actor) (e : G2.Coefficients ≃ₗ[ZMod 2] G2.Coefficients)
    (he : ∀ a v, e (G2.action a v) = G2.action (f a) (e v)) :
    ChapterC.BlockModuleModel L (multiplicativeAction G2.action) where
  quotientIso := m.quotientIso.trans f
  moduleIso := m.moduleIso.trans e.toAddEquiv.toMultiplicative
  intertwining l u := by
    change Multiplicative.ofAdd (e
      (m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L)
        (ChapterC.blockConjugate L l u))).toAdd) = _
    rw [m.intertwining]
    exact congrArg Multiplicative.ofAdd (he _ _)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly.G2Coordinates

end
