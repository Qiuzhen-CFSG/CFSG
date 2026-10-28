module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixConstrainedMoved
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OffenderRadical
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.RadicalFixedBound

/-!
# Excluding the actual A₆ constrained A₈ star

The full original eight-space survives the central projection of the literal
K-moved module. Natural and orthogonal central quotients have smaller
dimension. The whole-actor natural-plus-dual row has radical fixed dimension
at most four, while the actual orbit gives eight fixed dimensions. Repeated
natural rows cannot contain the original two inequivalent simple four-spaces.
These are all rows for the actual A₈=SL₄(2) actor.

This excludes constrained components at the original reciprocal witness.
The ordinary reciprocal and outside-component Hall alternatives are separate
source obligations.
Source: Aschbacher--Smith B.5.1, C.4.5--8 and 7.3.4, pp.99,152--154,699,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem moved_intertwines_original
    {W LH Kg R : Subgroup G} [IsElementaryAbelian 2 W]
    (hLW : LH ≤ normalizer (W : Set G)) (hLKg : LH ≤ Kg)
    {O : Subgroup (StarQuotient Kg R)} (hCO : starImage Kg R Kg ≤ O)
    (s : MovedSection ((starRepresentation Kg R).comp O.subtype)
      ((starImage Kg R Kg).subgroupOf O))
    (i : Additive W →ₗ[ZMod 2] s.space.toSubmodule)
    (hiambient : ∀ v, (((i v).val.toMul : (Kg ⊔ R : Subgroup G)) : G) = v.toMul) :
    let q : LH →* (starImage Kg R Kg).subgroupOf O :=
      (subgroupOfEquivOfLe hCO).symm.toMonoidHom.comp
        ((toStarImage Kg R).comp (inclusion hLKg))
    ∀ l v, i (doubledSeedAction LH W hLW l v) = s.space.toRepresentation (q l) (i v) := by
  intro q l v
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [hiambient]
  change _ = (((starRepresentation Kg R
    (QuotientGroup.mk' (starKernel Kg R) ⟨l,mem_sup_left (hLKg l.property)⟩)
    (i v).val).toMul : (Kg ⊔ R : Subgroup G)) : G)
  rw [starRepresentation_apply]
  change (l : G) * (v.toMul : G) * (l : G)⁻¹ =
    (l : G) * (((i v).val.toMul : (Kg ⊔ R : Subgroup G)) : G) * (l : G)⁻¹
  rw [hiambient]

private theorem no_repeated_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∀ (_hCO : C ≤ O)
      (s : MovedSection (ρ.comp O.subtype) (C.subgroupOf O))
      (i : Additive D.sourceOrbit →ₗ[ZMod 2] s.space.toSubmodule),
      (∀ v, (((i v).val.toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) = v.toMul) →
      Function.Injective i → ∀ r,
        ¬ IsRepeatedLinearNatural (s.space.toRepresentation.comp (C.subgroupOf O).subtype)
          BinaryField.two 4 r := by
  intro ρ O C hCO s i hiambient hi r hrep
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  have hLHH : LH ≤ H := hc.component_le.trans hc.local_le
  obtain ⟨_,hLK⟩ := D.sourceOrbit_six_witness_constrained_placement
    h hd hmodel hw hWJ hJC K hK hq hout hfK
  have hLKg : LH ≤ Kg := by
    have hh := map_mono (f := H.subtype) hLK
    rwa [map_subgroupOf_eq_of_le hLHH] at hh
  let q : LH →* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm.toMonoidHom.comp
    ((toStarImage Kg R).comp (inclusion hLKg))
  have hie := moved_intertwines_original (hLH.trans D.sourceOrbit_component_normalizes)
    hLKg hCO s i hiambient
  obtain ⟨a⟩ := hrep
  let b := a.groupEquiv.toMonoidHom.comp q
  let σ : Representation (ZMod 2) LH (Fin 4 → BinaryField.two.Carrier) :=
    (linearNatural BinaryField.two 4).comp b
  let τ : Representation (ZMod 2) LH (Fin r → Fin 4 → BinaryField.two.Carrier) :=
    (repeated (linearNatural BinaryField.two 4) r).comp b
  apply D.sourceOrbit_six_witness_no_small_repeated h hd hmodel hw σ τ
    (fun _ _ _ => rfl) (by
      change Module.finrank (ZMod 2) (Fin 4 → ZMod 2) < 8
      simp) (a.linearEquiv.toLinearMap.comp i) (a.linearEquiv.injective.comp hi)
  intro l v
  change a.linearEquiv (i (doubledSeedAction LH D.sourceOrbit _ l v)) = _
  rw [hie]
  exact a.intertwines (q l) (i v)

private theorem no_natural_dual_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let Kg := K.map H.subtype
    let R := J.pCoreIn 2
    let ρ := starRepresentation Kg R
    let O := offenderSubgroup ρ
    let C := starImage Kg R Kg
    C ≤ O →
    ∀ (s : MovedSection (ρ.comp O.subtype) (C.subgroupOf O))
      (i : Additive D.sourceOrbit →ₗ[ZMod 2] s.space.toSubmodule),
      EightSpaceMovedEmbedding s ((starImage Kg R R).subgroupOf O) i →
      C.subgroupOf O = ⊤ → ¬ IsNaturalPlusDual (s.space.toRepresentation.comp (C.subgroupOf O).subtype) 4 := by
  intro Kg R ρ O C hCO s i hi hwhole hnat
  let P := (starImage Kg R R).subgroupOf C
  let eC : C ≃* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm
  let P' := P.map eC.toMonoidHom
  let σ := s.space.toRepresentation.comp (C.subgroupOf O).subtype
  have hc := D.sourceOrbit_six_witness_hypothesisC28 h hd hmodel hw hWJ hJC
  have hP := ChapterC.C27Source.star_intersection_radical_of_whole_offender_from_source
    (hc.constrained_source_input K hK hq hout hfK) hwhole
  have hfix : i.range ≤ fixedSpace σ P' := by
    rintro _ ⟨v,rfl⟩ ⟨_,x,hx,rfl⟩
    exact hi.2.1 ⟨v,rfl⟩ ⟨⟨x.val,hCO x.property⟩,hx⟩
  let f := i.codRestrict (fixedSpace σ P') (fun v => hfix ⟨v,rfl⟩)
  have hf : Function.Injective f := by
    intro v w he
    exact hi.1 (congrArg Subtype.val he)
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  rw [D.sourceOrbit_six_dimension h hd hmodel] at hdim
  have hbound := NaturalDualCentralizer.finrank_radical_fixed_le σ P'
    (hP.map_equiv eC) (by decide : 0 < 4) hnat
  omega

private theorem no_four_actor_with_eight_space
    {E Y : Type*} [Group E] [Finite E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y] {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) (hc : BinaryActor.ActionCase ρ C s 4)
    (hdim : 8 ≤ Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule))
    (hdual : C = ⊤ → ¬ IsNaturalPlusDual (s.space.toRepresentation.comp C.subtype) 4)
    (hrep : ∀ r, ¬ IsRepeatedLinearNatural (s.space.toRepresentation.comp C.subtype)
      BinaryField.two 4 r) : False := by
  cases hc with
  | naturalDual hw hd => exact hdual hw hd
  | repeatedNatural r _ _ _ hr => exact hrep r hr
  | irreducible _ _ _ hs _ =>
    cases hs with
    | natural _ e _ =>
      have hh := e.linearEquiv.finrank_eq
      change Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) =
        Module.finrank (ZMod 2) (Fin 4 → ZMod 2) at hh
      simp at hh
      omega
    | orthogonal _ _ _ e _ _ =>
      have hh := e.linearEquiv.finrank_eq
      rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide)] at hh
      norm_num at hh
      omega
    | symmetricEight _ _ e _ =>
      have hh := e.action.linearEquiv.finrank_eq
      rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide)] at hh
      norm_num at hh
      omega
    | exterior hd _ _ _ _ _ _ => omega

/-- Every constrained component in the original A₆ reciprocal witness is
impossible. The actual A₈ marking and every moved-module exclusion are proved. -/
theorem sourceOrbit_six_witness_not_constrained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨_,⟨e8⟩⟩ := D.sourceOrbit_six_witness_constrained_eight h hmodel hw K hK hq hout hfK
  obtain ⟨hCO,c,i,hiambient,hi⟩ := D.sourceOrbit_six_witness_constrained_classified_embedding
    h hd hmodel hw hWJ hJC K hK hq hout hfK
  let e4 := (subgroupOfEquivOfLe hCO).trans (e8.trans
    (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm.trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))))
  have hcase := BinaryActor.actionCase _ (Or.inl rfl : 4 = 4 ∨ 4 = 5) e4 c.clause_one
  apply no_four_actor_with_eight_space c.sectionData hcase hi.2.2.2.2.2
  · intro hwhole hdual
    exact D.no_natural_dual_source h hd hmodel hw hWJ hJC K hK hq hout hfK
      hCO c.sectionData i hi hwhole hdual
  · intro r hr
    exact D.no_repeated_source h hd hmodel hw hWJ hJC K hK hq hout hfK
      hCO c.sectionData i hiambient hi.1 r hr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
