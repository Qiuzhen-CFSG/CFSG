module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitDecomposable
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TwoPlaneRecognition
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitSingletonRatio
public import Theory.SpecificGroups.OrthogonalFourBinary.WreathAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
/-!
# The decomposable branch of the original cubic-ratio reduction

Each literal factor satisfies the cyclic D.2.17 hypotheses. Its cubic ratio
is one or two, and ratio one forces dimension two by D.2.24. The uniform
prime and dimension markings then make both factors natural S₃ actions.
Recognition of the transitive pair gives full O₄⁺(2) coordinates, lifted
through the original conjugation image to the natural action on V(M).
Otherwise the exact factor embeddings transfer cubic ratio two to M̄.

This supplies the decomposable branch of 15.1.8 before the orthogonal
alternative is excluded by the counterexample hypothesis. No counterexample
or additional normalizer classification is assumed.

Source: Aschbacher--Smith D.2.24, 15.1.2(3), and 15.1.7--8,
printed pp.1086--1088.
-/
public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
/-- Lift full isometry coordinates through the original conjugation image. -/
theorem naturalOrthogonalAction_of_image_coordinates
    (M V : Subgroup G) (hn : M ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V]
    (a : Additive V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
    (e : internalActionImage M V hn ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (ha : ∀ g v, a (imageRepresentation M V hn g v) = (e g).val (a v)) :
    Nonempty (NaturalOrthogonalAction M V) := by
  obtain ⟨bG,bV,hb⟩ := OrthogonalFourBinary.isometry_equiv_natural_wreath
  let c : V ≃* Multiplicative OrthogonalFourBinary.Space := a.toAddEquiv.toMultiplicativeRight
  let f := (actionHom M V hn).rangeRestrict
  refine ⟨⟨hn,c.trans bV,bG.toMonoidHom.comp (e.toMonoidHom.comp f),
    bG.surjective.comp (e.surjective.comp (actionHom M V hn).rangeRestrict_surjective),?_⟩⟩
  intro m v
  have he : c (V.normalizerMonoidHom ⟨m,hn m.property⟩ v) =
      OrthogonalFourBinary.TerminalLines.vectorAction (e (f m)) (c v) := by
    exact congrArg Multiplicative.ofAdd (ha (f m) (Additive.ofMul v))
  apply funext
  intro i
  change bV (c (V.normalizerMonoidHom ⟨m,hn m.property⟩ v)) i = _
  rw [he]
  exact hb (e (f m)) (c v) i


/-- The original decomposable action has cubic ratio two or the full natural
orthogonal action on the same local module. -/
theorem source_localAction_full_orbit_decomposable_ratio
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull → U = ⊤ →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      cubicRatio ρ = 2 ∨ Nonempty (NaturalOrthogonalAction M V) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd hU π hp hs ht hmore
  obtain ⟨hcount,p,m,hpm,hmarks,i,j,hij,hall,hgen,hdis,hcom,hcompl,hswap⟩ :=
    source_localAction_full_orbit_decomposable hG T hempty hM hmany hJ
      U c d hd hU π hp hs ht hmore
  let F := d.factor i
  let f := (Jhat ρ).subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := f) ((Jhat ρ).subtype_injective.comp F.embedding.group_injective)
  have hqF : cubicRatio F.action ≤ 2 := by
    rw [F.embedding.ratio,c.ratio]
    exact source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  have hcyc := source_localAction_transitive_factor_cyclic hG T hempty hM hmany hJ
    U c d hd π hp ht hmore i
  have h : CyclicSource.Hypotheses F.action :=
    ⟨⟨F.faithful,hqF,F.generated,generalizedFitting_eq_fitting_of_solvable F.Carrier,
      c.factor_twoCore d (source_localAction_twoCore hG T hM) i,
      fun A hA => CyclicSource.rank_one_of_cyclic F.action hA (hcyc A hA)⟩,
      F.indecomposable,hd i⟩
  have hr : cubicRatio F.action = cubicRatio ρ := F.embedding.ratio.trans c.ratio
  rcases h.toCoreHypotheses.ratio_one_or_two with hq | hq
  · obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff F.action).mpr hqF
    obtain ⟨_,_,_,h₂⟩ := CyclicSource.ratio_one_full_support F.action h hq hA
    obtain ⟨l,hl⟩ := hmarks i
    have hm : m = 1 := by have hh := hl.dimension; change Module.finrank (ZMod 2) F.Space = 2 * m at hh; omega
    have hp3 : p = 3 := by
      rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with hh | hh <;> omega
    have hcards (k : d.Index) : Nat.card (d.factor k).Carrier = 6 := by
      obtain ⟨l,hl⟩ := hmarks k
      obtain ⟨e⟩ := hl.dihedral
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card,hp3]
    have hdims (k : d.Index) : Module.finrank (ZMod 2) (d.factor k).Space = 2 := by
      obtain ⟨l,hl⟩ := hmarks k
      simpa only [hm,mul_one] using hl.dimension
    obtain ⟨a,e,ha⟩ := c.two_plane_isometry_coordinates d
      (imageRepresentation_injective M V (le_normalizer_conjugateSpanBy _ _))
      hU hcount hcards hdims π hp hs ht
    exact Or.inr (naturalOrthogonalAction_of_image_coordinates M V
      (le_normalizer_conjugateSpanBy _ _) a e ha)
  · exact Or.inl (hr.symm.trans hq)
end CFSG.Quasithin.Chapter15.Section01
