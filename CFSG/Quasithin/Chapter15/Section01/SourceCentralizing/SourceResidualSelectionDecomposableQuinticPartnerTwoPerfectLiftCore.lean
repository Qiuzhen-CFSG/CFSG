module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLiftKernel
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The two-core of the literal full-F perfect-lift action

The canonical lift acts on F and on its original section F/D. The latter
factors through the former. Its kernel is the full-F image of K intersect L,
already a two-group, and its image is the exact embedded solvable residual
of the original offender closure. This image is normal in the core-free
section actor. Thus the full-F action has exactly that kernel as its two-core,
and its core quotient is the specified original perfect section image.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem core_of_factor_action
    {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : X →* Z) (hfg : f.ker ≤ g.ker)
    (hp : IsPGroup 2 (g.ker.map f)) (hc : pCore 2 g.range = ⊥) :
    ∃ q : f.range →* Z,
      q.comp f.rangeRestrict = g ∧ q.range = g.range ∧
      q.ker = pCore 2 f.range ∧
      f.range.pCoreIn 2 = g.ker.map f ∧
      Nonempty (f.range ⧸ pCore 2 f.range ≃* g.range) := by
  have hkr : f.rangeRestrict.ker ≤ g.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let q : f.range →* Z :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨g,hkr⟩
  have hq (x : X) : q (f.rangeRestrict x) = g x :=
    f.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x
  have hcomp : q.comp f.rangeRestrict = g := MonoidHom.ext hq
  have hr : q.range = g.range := by
    rw [←hcomp,MonoidHom.range_comp,
      f.rangeRestrict.range_eq_top_of_surjective f.rangeRestrict_surjective,
      MonoidHom.range_eq_map]
  have hkm : q.ker.map f.range.subtype = g.ker.map f := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨a,rfl⟩ := f.rangeRestrict_surjective x
      exact ⟨a,(hq a).symm.trans hx,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨f.rangeRestrict a,(hq a).trans ha,rfl⟩
  have hpk : IsPGroup 2 q.ker :=
    (hkm.symm ▸ hp).of_equiv
      (q.ker.equivMapOfInjective f.range.subtype f.range.subtype_injective).symm
  have hcore : q.ker = pCore 2 f.range :=
    q.ker_eq_pCore_of_range_core_eq_bot 2 hpk (hr.symm ▸ hc)
  refine ⟨q,hcomp,hr,hcore,?_,?_⟩
  · change (pCore 2 f.range).map f.range.subtype = _
    rw [←hcore]
    exact hkm
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      ((QuotientGroup.quotientKerEquivRange q).trans (MulEquiv.subgroupCongr hr))⟩

/-- The full-F conjugation image of the same canonical perfect lift has
two-core exactly the image of its literal section kernel, and its core
quotient is the exact residual of the original offender closure. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_perfect_lift_core
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
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let R := normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ))
          let R₀ := (solvableResidual R).map R.subtype
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
          let φ : L →* MulAut F :=
            F.normalizerMonoidHom.comp (Subgroup.inclusion (hLMc.trans dF.normalized))
          let ψ : L →* Representation.BinaryOffender.actionImage ρ :=
            (Representation.BinaryOffender.actionHom ρ).comp (Subgroup.inclusion hLMc)
          Group.IsPerfect L ∧ Mc ≤ normalizer (L : Set G) ∧
            L ≤ conjugateSpanBy V Mc ∧ L ≤ centralizer (D : Set G) ∧
            ⁅F,L⁆ = F ∧ F ≤ L ∧
            actionSubgroup ρ (L.subgroupOf Mc) = R₀ ∧
            Group.IsPerfect φ.range ∧ pCore 2 R₀ = ⊥ ∧
            ∃ q : φ.range →* Representation.BinaryOffender.actionImage ρ,
              q.comp φ.rangeRestrict = ψ ∧ q.range = R₀ ∧
              q.ker = pCore 2 φ.range ∧
              φ.range.pCoreIn 2 = ((K ⊓ L).subgroupOf L).map φ ∧
              Nonempty (φ.range ⧸ pCore 2 φ.range ≃* R₀) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  rcases h.decomposable_five_partner_two_three_perfect_lift_kernel
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | hlift
  · exact Or.inl hcore
  right
  intro W _ _ ρ dF hdim
  obtain ⟨hperfect,hnL,hLN,hLD,hFL,hFLle,himage,_,htwo⟩ := hlift ρ dF hdim
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let R := normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ))
  let R₀ := (solvableResidual R).map R.subtype
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let J := K ⊓ L
  have hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
  let φ : L →* MulAut F :=
    F.normalizerMonoidHom.comp (Subgroup.inclusion (hLMc.trans dF.normalized))
  let ψ : L →* Representation.BinaryOffender.actionImage ρ :=
    (Representation.BinaryOffender.actionHom ρ).comp (Subgroup.inclusion hLMc)
  have hnD : Mc ≤ normalizer (D : Set G) := by
    let D₀ := ((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore
    change Mc ≤ normalizer (D₀.map Mc.subtype : Set G)
    intro m hm
    exact le_normalizer_map Mc.subtype
      (mem_map_of_mem Mc.subtype (show (⟨m,hm⟩ : Mc) ∈ normalizer (D₀ : Set Mc) from
        normalizer_eq_top D₀ ▸ mem_top _))
  have hkm : (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype = K := by
    rw [actionHom_ker_eq]
    exact dF.action_kernel_map hnD
  have hkMc : (Representation.BinaryOffender.actionHom ρ).ker = K.subgroupOf Mc := by
    rw [←hkm]
    exact (comap_map_eq_self_of_injective Mc.subtype_injective _).symm
  have hkψ : ψ.ker = J.subgroupOf L := by
    change ((Representation.BinaryOffender.actionHom ρ).comp (Subgroup.inclusion hLMc)).ker = _
    rw [←MonoidHom.comap_ker,hkMc]
    ext l
    change (l : G) ∈ K ↔ (l : G) ∈ K ⊓ L
    exact ⟨fun hl => ⟨hl,l.property⟩,fun hl => hl.1⟩
  have hfg : φ.ker ≤ ψ.ker := by
    intro l hl
    have hc : (l : G) ∈ centralizer (F : Set G) := by
      change Subgroup.inclusion (hLMc.trans dF.normalized) l ∈ F.normalizerMonoidHom.ker at hl
      rwa [normalizerMonoidHom_ker] at hl
    change Subgroup.inclusion hLMc l ∈ (Representation.BinaryOffender.actionHom ρ).ker
    rw [actionHom_ker_eq]
    apply (dF.action_mem_ker_iff _).mpr
    intro f hf
    change ⁅(l : G),f⁆ ∈ D
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc f hf).symm]
    exact D.one_mem
  have hpker : IsPGroup 2 (ψ.ker.map φ) := by
    let hn : J ≤ normalizer (F : Set G) :=
      (inf_le_left.trans (commutatorPreimage_le Mc F D)).trans dF.normalized
    let φJ := F.normalizerMonoidHom.comp (Subgroup.inclusion hn)
    have hcomp : φ.comp (Subgroup.inclusion (show J ≤ L from inf_le_right)) = φJ := by
      ext j
      rfl
    have he : ψ.ker.map φ = φJ.range := by
      rw [←hcomp,MonoidHom.range_comp,Subgroup.inclusion_range,hkψ]
    exact he.symm ▸ htwo
  have hr : ψ.range = actionSubgroup ρ (L.subgroupOf Mc) := by
    rw [MonoidHom.range_comp,Subgroup.inclusion_range]
    rfl
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  have hdimW : 0 < Module.finrank (ZMod 2) W :=
    lt_of_lt_of_le (by decide : 0 < 3)
      (hdim ▸ Submodule.finrank_le (dF.imageSpace E))
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  have hcore : pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ :=
    actionImage_twoCore_eq_bot ρ hirr
  let : (L.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hnL
  have hnorm : (actionSubgroup ρ (L.subgroupOf Mc)).Normal :=
    Subgroup.Normal.map inferInstance (Representation.BinaryOffender.actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective
  let : ψ.range.Normal := hr.symm ▸ hnorm
  have hcr : pCore 2 ψ.range = ⊥ := by
    rw [pCore_eq_comap_of_normal,hcore]
    exact ψ.range.subtype.ker_eq_bot ψ.range.subtype_injective
  obtain ⟨q,hq,hqr,hqk,hqc,hquot⟩ := core_of_factor_action φ ψ hfg hpker hcr
  have hr₀ : ψ.range = R₀ := hr.trans himage
  let : Group.IsPerfect L := hperfect
  have hpfull : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  refine ⟨hperfect,hnL,hLN,hLD,hFL,hFLle,himage,hpfull,?_,q,hq,?_,hqk,?_,?_⟩
  · change pCore 2 R₀ = ⊥
    rw [←hr₀]
    exact hcr
  · exact hqr.trans hr₀
  · simpa only [hkψ] using hqc
  · change Nonempty (φ.range ⧸ pCore 2 φ.range ≃* R₀)
    exact ⟨hquot.some.trans (MulEquiv.subgroupCongr hr₀)⟩

end CFSG.Quasithin.Chapter15.Section01
