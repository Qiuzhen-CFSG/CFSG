module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedMoved
public import Theory.Representation.BinaryNaturalDual.SmallRepeatedEmbedding

/-!
# Excluding every repeated-natural row in the original constrained moved module

The literal original residual lies in K. The retained ambient embedding therefore
intertwines its original natural-plus-dual action with the actual K-moved action.
No sum of repeated modules of dimension four or five can contain the two
inequivalent original simple three-spaces. This applies to every multiplicity
and to the same classified section and embedding, without a parabolic marking.
Source: Aschbacher--Smith B.5.1, C.4.8 and 12.1.11, pp.99,154,794.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- No repetition of a natural module of degree four or five occurs on the
specified actual moved section, for any multiplicity. -/
@[expose] def NoSmallRepeatedMoved
    {E Y : Type*} [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) : Prop :=
  ∀ n, (n = 4 ∨ n = 5) → ∀ r,
    ¬ IsRepeatedLinearNatural (s.space.toRepresentation.comp C.subtype)
      BinaryField.two n r

omit [Finite G] in
private theorem no_repeated_star_embedding
    {W LH Kg R : Subgroup G} [IsElementaryAbelian 2 W]
    (hLW : LH ≤ normalizer (W : Set G)) (hLKg : LH ≤ Kg)
    {O : Subgroup (StarQuotient Kg R)} (hCO : starImage Kg R Kg ≤ O)
    (s : MovedSection ((starRepresentation Kg R).comp O.subtype)
      ((starImage Kg R Kg).subgroupOf O))
    (i : Additive W →ₗ[ZMod 2] s.space.toSubmodule)
    (hiambient : ∀ v, (((i v).val.toMul : (Kg ⊔ R : Subgroup G)) : G) = v.toMul)
    (hi : Function.Injective i)
    (p : LH →* LinearGroup 3) (hp : Function.Surjective p)
    (E : Additive W ≃ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 3)
    (he : ∀ (l : LH) (v : BinaryNaturalDual.CoordinateSpace 3),
      E.symm (BinaryNaturalDual.naturalDualRepresentation (p l) v) =
        doubledSeedAction LH W hLW l (E.symm v)) :
    NoSmallRepeatedMoved s := by
  intro n hn r hnatrep
  let q : LH →* (starImage Kg R Kg).subgroupOf O := (subgroupOfEquivOfLe hCO).symm.toMonoidHom.comp
    ((toStarImage Kg R).comp (inclusion hLKg))
  have hie (l : LH) (v : Additive W) :
      i (doubledSeedAction LH W
        hLW l v) =
      s.space.toRepresentation (q l) (i v) := by
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
  obtain ⟨a⟩ := hnatrep
  let b := a.groupEquiv.toMonoidHom.comp q
  let σ : Representation (ZMod 2) LH (Fin n → BinaryField.two.Carrier) :=
    (linearNatural BinaryField.two n).comp b
  let τ : Representation (ZMod 2) LH (Fin r → Fin n → BinaryField.two.Carrier) :=
    (repeated (linearNatural BinaryField.two n) r).comp b
  apply BinaryNaturalDual.no_small_repeated_embedding (by decide : 3 ≤ 3)
    p hp σ τ (fun _ _ _ => rfl) (by
      change Module.finrank (ZMod 2) (Fin n → ZMod 2) < 2*3
      simpa using (show n < 6 by omega))
    ((a.linearEquiv.toLinearMap.comp i).comp E.symm.toLinearMap)
    (a.linearEquiv.injective.comp (hi.comp E.symm.injective))
  intro l v
  change a.linearEquiv (i (E.symm _)) = _
  rw [he,hie]
  exact a.intertwines (q l) (i (E.symm v))


/-- No repeated-natural marking of degree four or five is compatible with
the actual original six-space in the same moved section, for any multiplicity. -/
theorem sourceOrbit_binary_witness_constrained_not_repeated_embedding
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (hstar : Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
        alternatingGroup (Fin 8)) ∨
      Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2))) :
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∀ (_hCO : C ≤ O)
      (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp O.subtype) (C.subgroupOf O))
      (i : Additive D.sourceOrbit →ₗ[ZMod 2] c.sectionData.space.toSubmodule),
      (∀ v, (((i v).val.toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) = v.toMul) →
      Function.Injective i →
      NoSmallRepeatedMoved c.sectionData := by
  intro ρ O C hCO c i hiambient hi
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  have hLHH : LH ≤ H := hc.component_le.trans hc.local_le
  obtain ⟨_,hLK⟩ := D.sourceOrbit_binary_witness_constrained_linear_placement
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK hstar
  have hLKg : LH ≤ Kg := by
    have hh := map_mono (f := H.subtype) hLK
    rwa [map_subgroupOf_eq_of_le hLHH] at hh
  obtain ⟨_,_,_,_,_,_,e,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let p₀ : LH →* BinaryLinearThree.Group :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  let p : LH →* LinearGroup 3 := (slEquivLinear 3).toMonoidHom.comp p₀
  have hp : Function.Surjective p := (slEquivLinear 3).surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have he (l : LH) (v : BinaryNaturalDual.CoordinateSpace 3) :
      E.symm (BinaryNaturalDual.naturalDualRepresentation (p l) v) =
      doubledSeedAction LH D.sourceOrbit
        (hLH.trans D.sourceOrbit_component_normalizes) l (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
    exact LinearMap.congr_fun
      (BinaryLinearThree.NaturalDual.naturalDualRepresentation_slEquivLinear (p₀ l)) v
  exact no_repeated_star_embedding (hLH.trans D.sourceOrbit_component_normalizes)
    hLKg hCO c.sectionData i hiambient hi p hp E he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
