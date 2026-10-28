module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry.FirstActors
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.FirstStage

/-!
# The actual degree-four high-rank first-stage profile

The compatible model transports the surviving A₂ fixed-plane and core
calculations to the original automizer. E.3.32 puts its six-dimensional
corank-two core in the actual reverse normalizer, so that normalizer has
corank at most two. The source pure-intersection premise, the original
conjugate, and its literal action image are retained throughout.
This supplies the high-rank input for the reverse-action contradiction
still owned by qt-d-double-natural-weak-closure.
Source: Aschbacher--Smith, 12.1.8, printed p.793 (PDF810).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
variable {M E : Type*} [Group M] [Finite M] [AddCommGroup E] [Module (ZMod 2) E]

/-- On the original source module, the pure-core restriction leaves a
fixed plane and a six-dimensional core for every large elementary actor. -/
theorem source_first_parameters (S : SourceSetup 4 M E) (I : Subgroup M)
    [IsElementaryAbelian 2 I] (hr : 4 ≤ rank I)
    (h : S.natural ⊓ generatedCore (S.representation.comp I.subtype) 2 ≤
      S.fixed (I ⊓ componentLayer M)) :
    Module.finrank (ZMod 2) (S.fixed I) = 2 ∧
      Module.finrank (ZMod 2) (generatedCore (S.representation.comp I.subtype) 2) = 6 := by
  let : Finite (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :=
    Finite.of_equiv M S.projective.toEquiv
  have hb : primeRank 2 M ≤ 4 :=
    (primeRank_equiv 2 S.projective).trans_le BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hc : Nat.card I = 16 := le_antisymm
    ((primeRank_le_iff_elementary_card_le M).mp hb I inferInstance)
    (Nat.pow_le_of_le_log Nat.card_pos.ne' hr)
  let A := I.map S.model.group.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map S.model.group.toMonoidHom
  have hA : Nat.card A = 16 :=
    (Subgroup.card_map_of_injective S.model.group.injective).trans hc
  have hn : S.natural.map S.model.coordinates.toLinearMap = BinaryNaturalDual.FourActors.naturalSummand := by
    ext v
    obtain ⟨x,rfl⟩ := S.model.coordinates.surjective v
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, BinaryNaturalDual.FourActors.mem_naturalSummand]
    exact ModelOrbits.MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates
      S.naturalCoordinates S.model.natural_marking x
  have ht := Submodule.map_mono (f := S.model.coordinates.toLinearMap) h
  rw [Submodule.map_inf _ S.model.coordinates.injective, hn, S.core_map,
    S.fixed_map, Subgroup.map_inf _ _ _ S.model.group.injective, S.layer_map] at ht
  have hp := coordinate_first_parameters
    (ModelOrbits.AutomorphismModel.coordinateAction S.degree) A hA ht
  constructor
  · rw [S.fixed_finrank]
    exact hp.1
  · have hd := (Submodule.equivMapOfInjective S.model.coordinates.toLinearMap
      S.model.coordinates.injective (generatedCore (S.representation.comp I.subtype) 2)).finrank_eq
    rw [S.core_map] at hd
    exact hd.trans hp.2

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (B : DoubledBranch T L V 4)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The large first-stage offender has a fixed plane on the actual orbit,
and E.3.32 gives reverse-normalizer corank at most two. -/
theorem four_first_high_rank_profile (M : B.MarkedAutomizerModel)
    (hp : B.PureIntersectionCentralizes) {g : G}
    (C : ConjugateConfiguration (componentOrbit V (T : Subgroup G)) g 1 4)
    (hr : 4 ≤ rank (inducedAutomizer (componentOrbit V (T : Subgroup G))
      (offenderNormalizer (componentOrbit V (T : Subgroup G)) g))) :
    Module.finrank (ZMod 2) (M.setup.fixed
      (inducedAutomizer (componentOrbit V (T : Subgroup G))
        (offenderNormalizer (componentOrbit V (T : Subgroup G)) g))) = 2 ∧
    subgroupCorank (componentOrbit V (T : Subgroup G))
      ((componentOrbit V (T : Subgroup G)) ⊓ normalizer
        ((componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom : Set G)) ≤ 2 := by
  let W := componentOrbit V (T : Subgroup G)
  let I := inducedAutomizer W (offenderNormalizer W g)
  let := offender_inducedAutomizer_elementary W g
  have hp' := FourGeometry.source_first_parameters M.setup I hr
    (LowRank.first_core_restrictions B M hp C).1
  refine ⟨hp'.1,?_⟩
  let U := generatedCore ((automizerRepresentation W).comp I.subtype) 2
  have hdim : Module.finrank (ZMod 2) U = 6 := by
    change Module.finrank (ZMod 2) (generatedCore ((automizerRepresentation W).comp I.subtype) 2) = 6
    rw [← M.representation_eq]
    exact hp'.2
  let e : U ≃ automizerDualCore W I 2 := {
    toFun := fun u => ⟨u.val.toMul, (ZeroClosure.mem_core_iff I 2 u.val).mpr u.property⟩
    invFun := fun u => ⟨Additive.ofMul ⟨u.val, automizerDualCore_le W I 2 u.property⟩,
      (ZeroClosure.mem_core_iff I 2 _).mp u.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card (automizerDualCore W I 2) = 2 ^ 6 := by
    rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,hdim]
  have hdimW : Module.finrank (ZMod 2) (Additive W) = 8 := by
    rw [M.setup.model.coordinates.finrank_eq]
    norm_num [CoordinateSpace, BinaryNaturalDual.Space, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
  have hcardW : Nat.card W = 2 ^ 8 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_congr (Additive.toMul : Additive W ≃ W), hdimW, Nat.card_zmod] at hh
    exact hh
  have hs := offender_corank_add
    (bot_le : (⊥ : Subgroup G) ≤ automizerDualCore W I 2) (automizerDualCore_le W I 2)
  simp only [subgroupCorank, Subgroup.relIndex_bot_left, hcard, hcardW,
    Nat.log_pow (by decide : 1 < 2)] at hs
  have hsum := offender_corank_add (C.core_le 2 (by decide))
    (show W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) ≤ W from inf_le_left)
  have hc2 : subgroupCorank W (automizerDualCore W I 2) = 2 := by
    unfold subgroupCorank
    omega
  rw [hc2] at hsum
  change subgroupCorank W _ ≤ 2
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
