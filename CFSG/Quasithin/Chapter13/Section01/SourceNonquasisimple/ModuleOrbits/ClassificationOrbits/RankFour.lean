module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.LinearThreeExtensions
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Sections
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Actions
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.Normalizer

/-!
# Rank-four natural central covers in the original normalizer action

A normalizer operator on the original U normalizes its represented component.
Rigidity of a fully moved natural SL₃(2) cover makes that operator an element
of the same represented SL₃(2). Thus the full original normalizer has a
compatible quotient, surjective on L. Rank-nullity constructs the unique
nonzero kernel vector after transporting the entire cover to four-space.
The resulting orbit marking supplies the orbit, core and quaternion-action
conclusions on the original U and odd Frattini quotient.

The last theorem applies this to the actual reduced moved section, retaining
its original projection and component containment. The source classification
must supply that section; a dimension-four record alone is not used as a cover.
Source: Aschbacher--Smith 13.1.10(4), 13.1.12, pp.871--874; B.4.8(2).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 SourceCentralizerStructure.Elimination
open ChapterB.QuasisimpleSource Representation.OneCohomology
open Representation.OneCohomology.SLThreeCentralExtension
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}
variable [IsElementaryAbelian 2 (normalizerMoved L)]

omit [Finite G] in
/-- The entire original normalizer acts through the same natural central cover. -/
theorem coverNormalizerQuotient
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (p : σ.IntertwiningMap BinaryLinearThree.W) (hp : IsCover p)
    (a : ActionEquiv (componentRepresentation (L := L)) σ) :
    ∃ q : normalizer (L : Set G) →* BinaryLinearThree.Group,
      Function.Surjective (q.comp (inclusion L.le_normalizer)) ∧
      ∀ m v, a.linearEquiv (Additive.ofMul (action L m v)) =
        σ (q m) (a.linearEquiv (Additive.ofMul v)) := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let e := a.linearEquiv
  let ρ := Representation.elementaryRepresentation (p := 2) (action L)
  let ν : Representation (ZMod 2) M V := e.conjRingEquiv.toMonoidHom.comp ρ
  let k := a.groupEquiv.toMonoidHom.comp (componentAction L).rangeRestrict
  have hk : Function.Surjective k :=
    a.groupEquiv.surjective.comp (componentAction L).rangeRestrict_surjective
  have he (m : M) (v : normalizerMoved L) :
      e (Additive.ofMul (action L m v)) = ν m (e (Additive.ofMul v)) := by
    change e _ = e (ρ m (e.symm (e (Additive.ofMul v))))
    rw [e.symm_apply_apply]
    rfl
  have hcomp (l : L) : ν.asGroupHom (inclusion L.le_normalizer l) = σ.asGroupHom (k l) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := e.surjective v
    exact (he (inclusion L.le_normalizer l) w.toMul).symm.trans
      (a.intertwines ((componentAction L).rangeRestrict l) w)
  have hrange : A.map ν.asGroupHom = actionImage σ := by
    have hc : ν.asGroupHom.comp (inclusion L.le_normalizer) =
        σ.asGroupHom.comp k := MonoidHom.ext hcomp
    rw [show A = (inclusion L.le_normalizer).range from (inclusion_range L.le_normalizer).symm,
      ← MonoidHom.range_comp,hc,MonoidHom.range_comp,k.range_eq_top_of_surjective hk,
      ← MonoidHom.range_eq_map]
    rfl
  have hn (m : M) : ν.asGroupHom m ∈ linearNormalizer σ := by
    let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
    have hm : m ∈ normalizer (A : Set M) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    have hh := (Subgroup.le_normalizer_map ν.asGroupHom)
      (show ν.asGroupHom m ∈ (normalizer (A : Set M)).map ν.asGroupHom from ⟨m,hm,rfl⟩)
    rwa [hrange] at hh
  have hs : Function.Injective σ.asGroupHom := fun _ _ h => cover_faithful σ p hp
    (congrArg Units.val h)
  let E : BinaryLinearThree.Group ≃* actionImage σ := MonoidHom.ofInjective hs
  have hr (m : M) : ν.asGroupHom m ∈ actionImage σ :=
    (cover_linearNormalizer_eq σ p hp).le (hn m)
  let q : M →* BinaryLinearThree.Group := E.symm.toMonoidHom.comp
    (ν.asGroupHom.codRestrict (actionImage σ) hr)
  have hq (m : M) : σ.asGroupHom (q m) = ν.asGroupHom m :=
    congrArg Subtype.val (E.apply_symm_apply ⟨ν.asGroupHom m,hr m⟩)
  refine ⟨q,?_,?_⟩
  · intro g
    obtain ⟨l,hl⟩ := hk g
    refine ⟨l,hs ?_⟩
    rw [MonoidHom.comp_apply,hq,hcomp,hl]
  · intro m v
    exact (he m v).trans (LinearMap.congr_fun (congrArg Units.val (hq m))
      (e (Additive.ofMul v))).symm

omit [Finite G] in
/-- Transport a fully moved natural central cover into the literal orbit marking. -/
theorem rankFourOrbitMarking
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (p : σ.IntertwiningMap BinaryLinearThree.W) (hp : IsCover p)
    (hd : Module.finrank (ZMod 2) V = 4)
    (a : ActionEquiv (componentRepresentation (L := L)) σ) :
    Nonempty (LinearThree.RankFourMarking L) := by
  let b : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) := LinearEquiv.ofFinrankEq _ _
    (hd.trans (Module.finrank_fin_fun (ZMod 2)).symm)
  let τ : Representation (ZMod 2) BinaryLinearThree.Group (Fin 4 → ZMod 2) :=
    b.conjRingEquiv.toMonoidHom.comp σ
  have hb (g : BinaryLinearThree.Group) (v : V) : τ g (b v) = b (σ g v) := by
    change b (σ g (b.symm (b v))) = _
    rw [b.symm_apply_apply]
  let p' : τ.IntertwiningMap BinaryLinearThree.W :=
    (p.toLinearMap.comp b.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      obtain ⟨w,rfl⟩ := b.surjective v
      rw [hb]
      change p (b.symm (b (σ g w))) = BinaryLinearThree.W g (p (b.symm (b w)))
      rw [b.symm_apply_apply,b.symm_apply_apply,p.isIntertwining])
  have hp' : Function.Surjective p' := hp.1.comp b.symm.surjective
  have hf' : p'.toLinearMap.ker ≤ OneCohomology.fixed τ := by
    intro v hv g
    obtain ⟨w,rfl⟩ := b.surjective v
    have hw : p w = 0 := by
      change p (b.symm (b w)) = 0 at hv
      rwa [b.symm_apply_apply] at hv
    rw [hb,hp.2.1 hw g]
  have hm' : Coinvariants.ker τ = ⊤ := by
    have hm : Coinvariants.ker σ ≤ (Coinvariants.ker τ).comap b.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      change b (σ g v - v) ∈ Coinvariants.ker τ
      rw [map_sub,← hb]
      exact Coinvariants.sub_mem_ker g (b v)
    apply top_unique
    intro v _
    obtain ⟨w,rfl⟩ := b.surjective v
    exact hm (hp.2.2 ▸ Submodule.mem_top)
  have hkdim : Module.finrank (ZMod 2) p'.toLinearMap.ker = 1 := by
    have hh := p'.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp', finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at hh
    omega
  have hkcard : Nat.card p'.toLinearMap.ker = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hkdim]
    rfl
  obtain ⟨z,hz,hu⟩ := (Nat.card_eq_two_iff' (0 : p'.toLinearMap.ker)).mp hkcard
  obtain ⟨q,hq,he⟩ := coverNormalizerQuotient σ p hp a
  refine ⟨{ quotient := q
            component_surjective := hq
            coordinates := (a.linearEquiv.trans b).toAddEquiv.toMultiplicative
            representation := τ
            projection := p'
            projection_surjective := hp'
            kernel_vector := z
            kernel_vector_ne_zero := fun he => hz (Subtype.ext he)
            kernel_eq := ?_
            kernel_fixed := fun g => hf' z.property g
            fully_moved := hm'
            equivariant := ?_ }⟩
  · intro x
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr (congrArg Subtype.val (hu ⟨x,hx⟩
          (fun he => hx0 (congrArg Subtype.val he))))
    · rintro (rfl | rfl)
      · exact map_zero _
      · exact z.property
  · intro m v
    change b (a.linearEquiv (Additive.ofMul (action L m v))) =
      τ (q m) (b (a.linearEquiv (Additive.ofMul v)))
    rw [he,hb]

/-- The genuine central cover discharges both original centralizer interfaces. -/
theorem centralizer_inputs_of_rankFourCover
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (π : σ.IntertwiningMap BinaryLinearThree.W) (hπ : IsCover π)
    (hd : Module.finrank (ZMod 2) V = 4)
    (a : ActionEquiv (componentRepresentation (L := L)) σ)
    {p : ℕ} [Fact p.Prime] (h : Context T L p) :
    OrbitFacts T L p ∧ SieveActions h := by
  obtain ⟨d⟩ := rankFourOrbitMarking σ π hπ hd a
  exact ⟨d.orbitFacts h,d.sieveActions h⟩

/-- Relabel the component on its original moved space, retaining every vector. -/
def threeCoverComponentEquiv
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K)
    (a : ActionEquiv (s.action.comp K.subtype) (linearNatural BinaryField.two 3)) :
    ActionEquiv (s.space.toRepresentation.comp K.subtype) (threeCoverAction s a) where
  groupEquiv := a.groupEquiv
  linearEquiv := LinearEquiv.refl _ _
  intertwines g v := by
    exact ((threeCoverAction_apply s a (a.groupEquiv g) v).trans
      (congrArg (fun k : K => s.space.toRepresentation k v)
        (a.groupEquiv.symm_apply_apply g))).symm

/-- Apply a genuine natural quotient on the original moved section to both
centralizer consumers. The component containment retains its actual subgroup. -/
theorem centralizer_inputs_of_central_three_section
    {p : ℕ} [Fact p.Prime] (h : Context T L p)
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H))
    (hi : IsIrrPlus ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H) s.space.toSubmodule)
    (hz : s.central.toSubmodule ≠ ⊥)
    (a : ActionEquiv (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf H).subtype)
      (linearNatural BinaryField.two 3)) : OrbitFacts T L p ∧ SieveActions h := by
  let c := componentSectionEquiv h.hypothesis h.many h.maximal h.nonquasisimple hCH s
  exact centralizer_inputs_of_rankFourCover (threeCoverAction s a) (threeCoverProjection s a)
    (threeCoverProjection_isCover s a hi) (threeCover_dimension_four s a hi hz)
    (composeAction c (threeCoverComponentEquiv s a)) h

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
