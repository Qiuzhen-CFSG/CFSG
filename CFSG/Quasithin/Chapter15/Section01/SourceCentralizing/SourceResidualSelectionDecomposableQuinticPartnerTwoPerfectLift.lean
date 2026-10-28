module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCanonicalThompson
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.ConjugateSpanNormalClosure
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# The actual perfect central lift of the canonical offender closure

Take the solvable residual of the normal closure of V inside Mc. It is
perfect, normal in Mc, and centralizes the literal denominator D. Its
image on the supplied F/D section is exactly the solvable residual of
the normal closure of the original V-image. If that image closure is
nonsolvable, perfectness and the original moving-span theorem force
[F,L]=F. No component is assumed or lifted through an arbitrary kernel.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v
variable {G : Type u} [Group G] [Finite G]

private theorem residual_image {X Y : Type*} [Group X] [Group Y] [Finite X]
    (N : Subgroup X) (f : X→*Y) :
    ((solvableResidual N).map N.subtype).map f=
      (solvableResidual (N.map f)).map (N.map f).subtype := by
  have he := congrArg (map (N.map f).subtype)
    (map_solvableResidual_eq (f.subgroupMap N) (f.subgroupMap_surjective N))
  have hc : (N.map f).subtype.comp (f.subgroupMap N)=f.comp N.subtype := by
    ext x
    rfl
  simpa only [map_map,hc] using he

/-- The literal canonical action either has solvable original offender
closure or has the actual full-moved perfect lift centralizing D. -/
theorem PreparedChosenModule.decomposable_five_canonical_perfect_lift
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ¬V≤Mc.pCoreIn 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let F := conjugateSpanBy E C
      let D := (((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      ∀ {W:Type v} [AddCommGroup W] [Module (ZMod 2) W]
        (ρ:Representation (ZMod 2) Mc W), BinaryConjugationSection Mc F D ρ →
      let A := actionSubgroup ρ (V.subgroupOf Mc)
      let R := normalClosure (A:Set (Representation.BinaryOffender.actionImage ρ))
      let N := normalClosure (V.subgroupOf Mc:Set Mc)
      let L := ((solvableResidual N).map N.subtype).map Mc.subtype
      Group.IsSolvable R ∨
        (Group.IsPerfect L ∧ Mc≤normalizer (L:Set G) ∧
          L≤conjugateSpanBy V Mc ∧ L≤centralizer (D:Set G) ∧
          ⁅F,L⁆=F ∧ F≤L ∧
          actionSubgroup ρ (L.subgroupOf Mc)=(solvableResidual R).map R.subtype) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hVQ
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let F := conjugateSpanBy E C
  let D := (((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  dsimp only
  intro W _ _ ρ dF
  let f := Representation.BinaryOffender.actionHom ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let R := normalClosure (A:Set (Representation.BinaryOffender.actionImage ρ))
  let N := normalClosure (V.subgroupOf Mc:Set Mc)
  let L₀ := (solvableResidual N).map N.subtype
  let L := L₀.map Mc.subtype
  by_cases hsolv : Group.IsSolvable R
  · exact Or.inl hsolv
  right
  rcases h.decomposable_five_core_or_maximal_reduced_section
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with
    hcore | ⟨_,_,hDC,hnD,_,_,_,_,_,_⟩
  · exact (hVQ hcore).elim
  have hUE := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVMc : V≤Mc := (V.le_centralizer.trans
    (centralizer_le (hUE.trans inf_le_left))).trans (localModule_centralizer_le_partner T Mc hu)
  have hNmap : N.map Mc.subtype=conjugateSpanBy V Mc := by
    rw [map_normalClosure_eq_conjugateSpanBy_range,
      map_subgroupOf_eq_of_le hVMc,range_subtype]
  have hNimage : N.map f=R := by
    change (normalClosure (V.subgroupOf Mc:Set Mc)).map f=normalClosure (A:Set _)
    rw [map_normalClosure _ f ρ.asGroupHom.rangeRestrict_surjective]
    rfl
  let : Group.IsPerfect L₀ := Group.IsPerfect.map N.subtype
  let : Group.IsPerfect L := Group.IsPerfect.map Mc.subtype
  have hLN : L≤conjugateSpanBy V Mc :=
    (map_mono (map_subtype_le (solvableResidual N))).trans_eq hNmap
  have hLC : L≤centralizer (D:Set G) := hLN.trans
    (conjugateSpanBy_le (le_centralizer_iff.mp hDC)
      (hnD.trans (normalizer_le_normalizer_centralizer D)))
  have hNtop : normalizer (N:Set Mc)=⊤ := normalizer_eq_top N
  let : L₀.Normal := normalizer_eq_top_iff.mp (top_unique (by
    have hh := normalizer_le_normalizer_characteristic_image N (solvableResidual N)
    rwa [hNtop] at hh))
  have hnL : Mc≤normalizer (L:Set G) := by
    apply le_normalizer_iff.mpr
    rintro m hm _ ⟨l,hl,rfl⟩
    exact mem_map_of_mem Mc.subtype ((inferInstance:L₀.Normal).conj_mem l hl ⟨m,hm⟩)
  have hLMc : L≤Mc := map_subtype_le L₀
  have hLsub : L.subgroupOf Mc=L₀ := comap_map_eq_self_of_injective Mc.subtype_injective L₀
  have himage : actionSubgroup ρ (L.subgroupOf Mc)=(solvableResidual R).map R.subtype := by
    change (L.subgroupOf Mc).map f=_
    rw [hLsub,residual_image,hNimage]
  have hnLF : ¬L≤centralizer (F:Set G) := by
    intro hLF
    have hz : actionSubgroup ρ (L.subgroupOf Mc)=⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro l hl
      rw [actionHom_ker_eq]
      apply (dF.action_mem_ker_iff l).mpr
      intro x hx
      exact (show (⊥:Subgroup G)≤D from bot_le)
        ((commutator_eq_bot_iff_le_centralizer.mpr hLF).le
        (commutator_mem_commutator hl hx))
    have hr : solvableResidual R=⊥ := by
      apply map_injective R.subtype_injective
      simpa only [Subgroup.map_bot] using himage.symm.trans hz
    obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G:=R)
    exact hsolv ⟨n,hn.trans hr⟩
  let H := ⁅F,L⁆
  have hHF : H≤F := le_normalizer_iff_commutator_le_left.mp (hLMc.trans dF.normalized)
  have hnH : Mc≤normalizer (H:Set G) := by
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ⁅F,L⁆.map (MulAut.conj m).toMonoidHom=⁅F,L⁆
    have hmF : F.map (MulAut.conj m).toMonoidHom=F :=
      mem_normalizer_iff_map_conj_eq.mp (dF.normalized hm)
    have hmL : L.map (MulAut.conj m).toMonoidHom=L :=
      mem_normalizer_iff_map_conj_eq.mp (hnL hm)
    rw [map_commutator,hmF,hmL]
  have hHV : ¬H≤centralizer (V:Set G) := by
    intro hHC
    have hHD : H≤D := by
      intro x hx
      refine ⟨⟨x,dF.section_le (hHF hx)⟩,?_,rfl⟩
      intro m
      have hx' := le_normalizer_iff.mp hnH m m.property x hx
      exact ⟨hHF hx',hHC hx'⟩
    have hz₂ : ⁅⁅F,L⁆,L⁆=⊥ := le_bot_iff.mp
      ((commutator_mono hHD le_rfl).trans
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hLC)).le)
    have hz := commutator_eq_bot_of_iterated_eq_bot F L hz₂
    exact hnLF (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  have hwhole : ⁅F,L⁆=F := (h.decomposable_five_moving_normal_span
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
      H hHF hnH hHV).2
  have hFL : F≤L := hwhole.symm.le.trans
    (le_normalizer_iff_commutator_le_right.mp (dF.section_le.trans hnL))
  exact ⟨inferInstance,hnL,hLN,hLC,hwhole,hFL,himage⟩

end CFSG.Quasithin.Chapter15.Section01
