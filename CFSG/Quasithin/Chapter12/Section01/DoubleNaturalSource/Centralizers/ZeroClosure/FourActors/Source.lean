module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.FourActors.Coordinate
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Source

/-!
# The finite actor obstruction in the original degree-four action

The intrinsic two-rank bound for Aut(PSL₄(2)) makes every elementary actor
of binary rank at least four have order sixteen. The constructed H.9 model
preserves the natural summand, the actual layer, fixed spaces, and the
corank-three generated core. Transport to the genuine three-class catalogue
therefore gives the forbidden-containment theorem with no extra premise.

The application uses the literal automizer model of the chosen doubled
orbit. It discharges the actor hypothesis in the zeroth-closure reduction;
only the independently owned mutual-normalization argument remains explicit,
along with the original source model and centralizer hypotheses.

Source: Aschbacher--Smith, H.9.3, printed pp.391--392 (PDF pp.402--403),
and12.1.7, printed p.792 (PDF p.809).
-/

public noncomputable section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryNaturalDual.ModelOrbits
open Theory.GroupTheory
open CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.FourActors

variable {M E : Type*} [Group M] [Finite M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E)

/-- The intrinsic H.9.3 obstruction on the original marked natural summand. -/
theorem source_obstruction (I : Subgroup M) (hI : IsElementaryAbelian 2 I)
    (hr : 4 ≤ Representation.BinaryOffender.rank I) :
    ¬ S.natural ⊓ generatedCore (S.representation.comp I.subtype) 3 ≤
      S.fixed (I ⊓ componentLayer M) := by
  let : Finite (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :=
    Finite.of_equiv M S.projective.toEquiv
  have hb : primeRank 2 M ≤ 4 :=
    (primeRank_equiv 2 S.projective).trans_le BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hc : Nat.card I = 16 := le_antisymm
    ((primeRank_le_iff_elementary_card_le M).mp hb I hI)
    (Nat.pow_le_of_le_log Nat.card_pos.ne' hr)
  let A := I.map S.model.group.toMonoidHom
  let : IsElementaryAbelian 2 A := hI.map S.model.group.toMonoidHom
  have hA : Nat.card A = 16 :=
    (Subgroup.card_map_of_injective S.model.group.injective).trans hc
  have hn : S.natural.map S.model.coordinates.toLinearMap = naturalSummand := by
    ext v
    obtain ⟨x,rfl⟩ := S.model.coordinates.surjective v
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_naturalSummand]
    exact MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates
      S.naturalCoordinates S.model.natural_marking x
  intro h
  have ht := Submodule.map_mono (f := S.model.coordinates.toLinearMap) h
  rw [Submodule.map_inf _ S.model.coordinates.injective, hn, S.core_map,
    S.fixed_map, Subgroup.map_inf _ _ _ S.model.group.injective, S.layer_map] at ht
  exact coordinate_obstruction (AutomorphismModel.coordinateAction S.degree) A hA ht

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.FourActors


open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- H.9.3 discharges the large-actor premise in the literal degree-four W₀
application. The independent mutual-normalization implication remains explicit. -/
theorem doubledFour_zeroClosure_of_pair_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hpair : ∀ g : G,
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T →
      componentOrbit V (T : Subgroup G) ≤ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G) →
      ⁅componentOrbit V (T : Subgroup G),
        (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers → B.PureIntersectionCentralizes →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro S hc hp
  apply D.doubledFour_zeroClosure_of_pair_of_actors_of_many h hmany B hpair S hc hp
  dsimp only
  intro I hI hr
  exact ZeroClosure.FourActors.source_obstruction
    (S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)).setup I hI hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
