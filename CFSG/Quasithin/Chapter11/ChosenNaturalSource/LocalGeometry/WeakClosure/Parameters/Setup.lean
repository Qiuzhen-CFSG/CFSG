module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Contracts

/-!
# The E.6.1 setup on the original natural seed

Uniqueness over LT implies the precise uniqueness clause of E.6.1:
LT normalizes V and its two-core C_T(V). All other structural clauses
come from the original chosen input. Only the preceding TI conclusion
of 11.0.3(4) remains explicit, with its original preliminary owner.

Source: Aschbacher--Smith, 11.0.3(4), p.760, and E.6.1, pp.244--245.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- All E.6.1 premises except the preceding TI theorem are discharged on V;
in particular neither a rank bound nor centralizer control is assumed. -/
theorem hypothesisE61_of_ti
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) :
    HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  have hmax := hu.normalizer_maximal
  rw [he] at hmax
  refine ⟨S.source.simpleQTKE, hmax, D.sylow_normalizes_component,
    D.ne_bot, D.elementary, D.le_sylow,
    (normal_subgroupOf_iff_le_normalizer D.le_sylow).mpr S.sylow_normalizes,
    hti, ?_⟩
  intro N hN hle
  rw [← he]
  apply hu.normalizer_unique N hN
  apply le_trans ?_ hle
  refine le_inf (le_inf (sup_le L.le_normalizer D.sylow_normalizes_component)
    (sup_le D.normalizes S.sylow_normalizes)) ?_
  change L ⊔ (T : Subgroup G) ≤ normalizer
    (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)
  rw [seed_sylow_centralizer D S]
  exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
