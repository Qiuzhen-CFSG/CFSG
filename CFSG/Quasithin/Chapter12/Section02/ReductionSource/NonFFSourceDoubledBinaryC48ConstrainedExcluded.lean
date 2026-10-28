module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedFiveFlag
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedResidualOrder
public import Theory.Representation.SL5ExteriorSquare.RadicalFixed.PerfectExclusion

/-!
# Excluding the actual constrained component of the binary-three witness

The original six-space is fixed by the actual component radical in the
irreducible exterior ten-space. The native fixed-space theorem makes its
normalizer a hyperplane parabolic. The original residual star image is a
nontrivial perfect normal subgroup of that full normalizer, so its order has
a factor five. Its actual SL3(2) two-core quotient gives the contradiction.
All component placement, radical, source-module and normalizer facts are
produced from the original witness. No parabolic or module premise is added.
Source: Aschbacher--Smith C.4.8 and 12.1.11, pp.154,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation.SL5ExteriorSquare Representation.SL5TenDimensional

private theorem exterior_fixed_six_obstruction
    {C W Z : Type*} [_root_.Group C] [Finite C]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) Z]
    (ρ : Representation (ZMod 2) C W) (P : Subgroup C) (hP : P.IsPRadical 2)
    (B : Subgroup (normalizer (P : Set C))) [B.Normal] [Group.IsPerfect B]
    (hB : B ≠ ⊥) (hfive : Nat.Coprime 5 (Nat.card B))
    (actor : C ≃* SL(5,ZMod 2)) (E : W ≃ₗ[ZMod 2] ExteriorModule 2)
    (he : ∀ g v, E (ρ g v) = exteriorAction 2 (actor g) (E v))
    (i : Z →ₗ[ZMod 2] W) (hi : Function.Injective i)
    (hfix : i.range ≤ fixedSpace ρ P) (hdim : Module.finrank (ZMod 2) Z = 6) : False := by
  let Q := P.map actor.toMonoidHom
  let f := E.toLinearMap.comp i
  have hf : f.range ≤ fixedSpace (exteriorAction 2) Q := by
    rintro _ ⟨v,rfl⟩ ⟨_,x,hx,rfl⟩
    change exteriorAction 2 (actor x) (E (i v)) = E (i v)
    rw [←he]
    exact congrArg E (hfix ⟨v,rfl⟩ ⟨x,hx⟩)
  let j := f.codRestrict (fixedSpace (exteriorAction 2) Q) (fun v => hf ⟨v,rfl⟩)
  have hj : Function.Injective j := by
    intro v w h
    exact hi (E.injective (congrArg Subtype.val h))
  have hdimQ := LinearMap.finrank_le_finrank_of_injective hj
  rw [hdim] at hdimQ
  let eN : normalizer (P : Set C) ≃* normalizer (Q : Set SL(5,ZMod 2)) :=
    (actor.subgroupMap (normalizer (P : Set C))).trans
      (MulEquiv.subgroupCongr (map_equiv_normalizer_eq P actor))
  let B' := B.map eN.toMonoidHom
  let eb : B ≃* B' := B.equivMapOfInjective eN.toMonoidHom eN.injective
  let : B'.Normal := Normal.map inferInstance eN.toMonoidHom eN.surjective
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective (f := eb.toMonoidHom) eb.surjective
  have hB' : B' ≠ ⊥ := fun hz => hB
    ((B.map_eq_bot_iff_of_injective (f := eN.toMonoidHom) eN.injective).mp hz)
  have hdiv := five_dvd_card_of_normal_perfect_radical_normalizer Q (hP.map_equiv actor)
    hdimQ B' hB'
  rw [←Nat.card_congr eb.toEquiv] at hdiv
  exact (by decide : ¬ 5 ∣ 1) (hfive.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdiv)

universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual constrained component cannot occur in the original binary-three
witness; all source module and parabolic inputs have been discharged. -/
theorem sourceOrbit_binary_witness_no_constrained_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨hCO,c,i,_hiambient,hdata,_hs,_mark,actor,E,_,_,he⟩ :=
    D.sourceOrbit_binary_witness_constrained_exterior_coordinates
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let O := offenderSubgroup (starRepresentation Kg R)
  let C := starImage Kg R Kg
  let P := (starImage Kg R R).subgroupOf C
  let eC : C ≃* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm
  let e : C ≃* SL(5,ZMod 2) := eC.trans actor
  let σ := c.sectionData.space.toRepresentation.comp
    ((C.subgroupOf O).subtype.comp eC.toMonoidHom)
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let B := (LH.subgroupOf Kg).map (toStarImage Kg R)
  let N := normalizer (P : Set C)
  let B₀ := B.subgroupOf N
  obtain ⟨hP,_,hBN,hBn,hBperfect,h168,_⟩ := D.sourceOrbit_binary_witness_constrained_five_flag
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK e
  let := hBn
  let := hBperfect
  let eb : B₀ ≃* B := subgroupOfEquivOfLe hBN
  let : Group.IsPerfect B₀ := Group.IsPerfect.ofSurjective (f := eb.symm.toMonoidHom) eb.symm.surjective
  have hB₀ : B₀ ≠ ⊥ := by
    intro hz
    have hc : Nat.card B = 1 := by rw [←Nat.card_congr eb.toEquiv,hz]; simp
    rw [hc] at h168
    norm_num at h168
  have hfive := (D.sourceOrbit_binary_witness_residual_star_five_free h hd F hF hmodel hw K).2
  have hfive₀ : Nat.Coprime 5 (Nat.card B₀) := by
    rw [Nat.card_congr eb.toEquiv]
    exact hfive
  apply exterior_fixed_six_obstruction σ P hP B₀ hB₀ hfive₀ e E
    (fun g v => he (eC g) v) i hdata.1 _ (D.sourceOrbit_binary_dimension h hd F hF hmodel)
  rintro _ ⟨v,rfl⟩ x
  exact hdata.2.1 ⟨v,rfl⟩ ⟨⟨x.val.val,hCO x.val.property⟩,x.property⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
