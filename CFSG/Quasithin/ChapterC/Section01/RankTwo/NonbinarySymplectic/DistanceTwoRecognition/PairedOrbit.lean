module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SeedDisjoint
public import Theory.Representation.SymplecticFourOrthogonalCover.InvariantRefinement
public import Theory.SpecificGroups.SymplecticFour.QuadraticRefinementObstruction
/-!
# The paired-orbit contradiction and the whole intrinsic core

The secondary quotient is fully moved and is a central cover of the original
natural symplectic module. A quadratic actor of order q cubed cannot preserve
a quadratic refinement. Thus it moves the entire fixed kernel, which places
the full fixed preimage in [A,A'] Z. Paired Frattini disjointness makes that
preimage elementary; its previously proved centrality and natural-vector
transitivity then make A elementary.

The exact factorization Q_a = A (Q_a intersect Q_z) now gives [Y,Q_a] = 1.
Its normal closure A centralizes Q_a and lies in the central omega layer,
contradicting escape of the whole intrinsic core. The resulting Frattini bound
supplies shortness and the actual natural block model for the original K,
through the existing replacement transport. Every field degree and fixed
attachment is retained. The degree restriction in (3.7) remains separate.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed pp.870--872;
Aschbacher--Smith C.1.30--32, printed pp.135--136.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource Sp4Four.CoreReconstruction

private theorem fully_moved_fixed_le_displacement
    {J V : Type*} [Group J] [Finite J]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) J V) (C : Subgroup J) [C.Normal]
    (n : ℕ) (hn : 1 < n)
    (hfull : subspaceCommutator σ ⊤ C = ⊤)
    (hnat : NaturalMovedSectionAtDegree σ C n)
    (B : Subgroup J) (hBC : B ≤ C) (hcard : Nat.card B = (2^n)^3)
    (hquad : IsQuadratic σ B) :
    fixedSpace σ C ≤ subspaceCommutator σ ⊤ B := by
  let s := MovedSection.ofNormal σ C
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hfull
  obtain ⟨_,hi,E,hE,⟨e₀⟩⟩ := hnat
  have hFc : Nat.card E.Carrier = 2^n := E.card_eq.trans (congrArg (2^·) hE)
  have hF : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
  let e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)) :=
    Sp4Four.derivedNaturalActionEquiv hF (s.action.comp C.subtype) e₀
  let p := MovedSection.coverProjection s e
  have hp : IsCover p := MovedSection.coverProjection_isCover s hi e
  let f : C →* L (K := E.Carrier) := e.groupEquiv.toMonoidHom
  let A := (B.subgroupOf C).map f
  have hAc : Nat.card A = Nat.card B := by
    rw [Subgroup.card_map_of_injective e.groupEquiv.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv
  have hquadA : ∀ a ∈ A, ∀ b ∈ A, ∀ v,
      binaryNatural a (binaryNatural b v-v)=binaryNatural b v-v := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    obtain ⟨w,rfl⟩ := hp.1 v
    have heq : MovedSection.coverAction s e (f a)
        (MovedSection.coverAction s e (f b) w-w) =
        MovedSection.coverAction s e (f b) w-w := by
      apply Subtype.ext
      change σ (e.groupEquiv.symm (e.groupEquiv a)).val
        (σ (e.groupEquiv.symm (e.groupEquiv b)).val w.val-w.val) =
        σ (e.groupEquiv.symm (e.groupEquiv b)).val w.val-w.val
      simpa only [e.groupEquiv.symm_apply_apply] using hquad a.val ha b.val hb w.val
    have hpq := congrArg p heq
    simpa only [map_sub,p.isIntertwining] using hpq
  have hk : p.toLinearMap.ker ≤ Coinvariants.ker ((MovedSection.coverAction s e).comp A.subtype) := by
    by_contra hh
    obtain ⟨c,hc⟩ := cover_preserves_refinement_of_kernel_escape p hp A hh
    let B' := A.map (commutator (Sp E.Carrier)).subtype
    have hBc : Nat.card E.Carrier^2 ≤ Nat.card B' := by
      rw [Subgroup.card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective,
        hAc,hFc,hcard]
      exact Nat.pow_le_pow_right (by positivity) (by decide)
    have hBq : ∀ a ∈ B', ∀ b ∈ B', ∀ v : Vector E.Carrier,
        a • (b • v-v)=b • v-v := by
      rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
      exact hquadA a ha b hb v
    apply no_refinement_of_large_quadratic hF B' hBc hBq
    refine ⟨c,?_⟩
    rintro ⟨b,hb⟩ v
    obtain ⟨a,ha,rfl⟩ := hb
    exact hc ⟨a,ha⟩ v
  have hm : Coinvariants.ker ((MovedSection.coverAction s e).comp A.subtype) ≤
      (subspaceCommutator σ ⊤ B).comap s.space.toSubmodule.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨b,hb,he⟩ := a.property
    change ((MovedSection.coverAction s e a.val w-w) : s.space.toSubmodule).val ∈ subspaceCommutator σ ⊤ B
    rw [←he]
    change σ (e.groupEquiv.symm (e.groupEquiv b)).val w.val-w.val ∈ subspaceCommutator σ ⊤ B
    rw [e.groupEquiv.symm_apply_apply]
    exact Submodule.subset_span ⟨b.val,hb,w.val,Submodule.mem_top,rfl⟩
  intro v hv
  let w : s.space.toSubmodule := ⟨v,hs.symm ▸ Submodule.mem_top⟩
  have hw : w ∈ p.toLinearMap.ker := by
    change e.linearEquiv (s.central.toSubmodule.mkQ w)=0
    rw [←e.linearEquiv.map_zero,e.linearEquiv.injective.eq_iff]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [s.central_eq]
    intro a
    exact Subtype.ext (hv a)
  exact hm (hk hw)
private theorem full_secondary_quotient_section
    {G J V : Type*} [Group G] [Group J]
    [AddCommGroup V] [Module (ZMod 2) V]
    (S A Z L₀ : Subgroup G) (hLS : L₀ ≤ S)
    (hZN : S ≤ normalizer Z)
    (σ : Representation (ZMod 2) J V) (C : Subgroup J) [C.Normal]
    (κ : S →* J) (hL : (L₀.subgroupOf S).map κ = C)
    (c : BinaryConjugationSection S A Z (σ.comp κ))
    (hfull : subspaceCommutator σ ⊤ C = ⊤) :
    let s := MovedSection.ofNormal σ C
    Nonempty (BinaryConjugationSection S A (commutatorPreimage A L₀ Z) (s.action.comp κ)) := by
  let s := MovedSection.ofNormal σ C
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hfull
  let l : V →ₗ[ZMod 2] s.space.toSubmodule := {
    toFun v := ⟨v,hs.symm ▸ Submodule.mem_top⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let q := s.central.toSubmodule.mkQ.comp l
  let ν := q.toAddMonoidHom.toMultiplicative.comp c.coordinates
  let D := commutatorPreimage A L₀ Z
  have hDA : D ≤ A := commutatorPreimage_le _ _ _
  have hZD : Z ≤ D := le_commutatorPreimage c.kernel_le
    (le_normalizer_iff_commutator_le_left.mp (hLS.trans hZN))
  have him : c.imageSpace D = fixedSpace σ C := by
    rw [c.fixed_image_eq L₀ hLS (c.section_le.trans hZN),fixedSpace_comp_map,hL]
  have hqker (v : V) : q v = 0 ↔ v ∈ fixedSpace σ C := by
    change (Submodule.Quotient.mk (l v) : s.space.toSubmodule ⧸ s.central.toSubmodule)=0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero,s.central_eq]
    constructor
    · intro hv a
      exact congrArg Subtype.val (hv a)
    · intro hv a
      exact Subtype.ext (hv a)
  refine ⟨{
    section_le := c.section_le
    kernel_le := hDA
    normalized := c.normalized
    coordinates := ν
    onto := ?_
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · intro v
    obtain ⟨w,hw⟩ := s.central.toSubmodule.mkQ_surjective v.toAdd
    obtain ⟨a,ha⟩ := c.onto (Multiplicative.ofAdd w.val)
    refine ⟨a,?_⟩
    apply Multiplicative.toAdd.injective
    change s.central.toSubmodule.mkQ (l (c.coordinates a).toAdd)=v.toAdd
    rw [ha]
    exact hw
  · ext a
    change q (c.coordinates a).toAdd=0 ↔ a.val ∈ D
    rw [hqker,←him,c.coordinates_mem_imageSpace_iff D hDA a,sup_of_le_left hZD]
  · intro u a
    change q (c.coordinates _).toAdd = (MovedSection.action σ s) (κ u) (q (c.coordinates a).toAdd)
    rw [c.equivariant]
    rfl

private theorem seed_not_le_kernel_of_nonzero
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (S Y D : Subgroup G) (ρ : Representation (ZMod 2) S V)
    (c : BinaryConjugationSection S (conjugatesIn Y S) D ρ)
    (v₀ : V) (hv₀ : v₀ ≠ 0) : ¬ Y ≤ D := by
  have hYA : Y ≤ conjugatesIn Y S := by
    rw [Sp4Four.conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy _ _
  intro hYD
  have hAD : conjugatesIn Y S ≤ D := by
    apply iSup_le
    intro u
    rintro _ ⟨y,hy,rfl⟩
    let v : conjugatesIn Y S := ⟨y,hYA hy⟩
    have hv : c.coordinates v = 1 := (c.coordinates_eq_one_iff v).mpr (hYD hy)
    have hh := c.equivariant u⁻¹ v
    rw [hv] at hh
    have hz : c.coordinates ⟨(u⁻¹:G)*v*(u⁻¹:G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized u⁻¹.property) v).mp v.property⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hh
    exact (c.coordinates_eq_one_iff _).mp hz
  obtain ⟨v,hv⟩ := c.onto (Multiplicative.ofAdd v₀)
  have hz := (c.coordinates_eq_one_iff v).mpr (hAD v.property)
  exact hv₀ (congrArg Multiplicative.toAdd (hv.symm.trans hz))

private theorem elementary_span_of_natural_section
    {G J V : Type*} [Group G] [Group J]
    [AddCommGroup V] [Module (ZMod 2) V]
    (S Y D L₀ : Subgroup G) (C : Subgroup J)
    (κ : S →* J) (hL : (L₀.subgroupOf S).map κ = C)
    (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection S (conjugatesIn Y S) D (σ.comp κ))
    (E : BinaryField) (e : ActionEquiv (σ.comp C.subtype) (binarySymplectic E))
    [IsElementaryAbelian 2 D] [IsElementaryAbelian 2 Y]
    (hcentral : D ≤ centralizer (conjugatesIn Y S : Set G)) :
    IsElementaryAbelian 2 (conjugatesIn Y S) := by
  have hYA : Y ≤ conjugatesIn Y S := by
    rw [Sp4Four.conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy _ _
  have hYD : ¬ Y ≤ D := by
    apply seed_not_le_kernel_of_nonzero S Y D (σ.comp κ) c
      (e.linearEquiv.symm (Theory.SpecificGroups.SymplecticFour.e 0))
    intro hz
    have he : Theory.SpecificGroups.SymplecticFour.e (F := E.Carrier) 0 = 0 := by
      simpa only [e.linearEquiv.apply_symm_apply,map_zero] using congrArg e.linearEquiv hz
    have hh := congrFun he (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at hh
  apply c.elementary_of_transitive hcentral
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx)
  · obtain ⟨y,hy,hyn⟩ := SetLike.not_le_iff_exists.mp hYD
    refine ⟨⟨y,hYA hy⟩,Subtype.ext (elemPow_eq_one_of_isElementaryAbelian y hy),?_⟩
    exact fun hh => hyn ((c.coordinates_eq_one_iff _).mp hh)
  · intro u v hu hv
    have hu' : e.linearEquiv u ≠ 0 := fun he => hu (e.linearEquiv.injective
      (he.trans e.linearEquiv.map_zero.symm))
    have hv' : e.linearEquiv v ≠ 0 := fun he => hv (e.linearEquiv.injective
      (he.trans e.linearEquiv.map_zero.symm))
    obtain ⟨b,hb⟩ := TwoLocalCover.nonzero_vector_transitive hu' hv'
    let k : C := e.groupEquiv.symm b
    obtain ⟨l,hl,he⟩ := (hL.symm ▸ k.property : k.val ∈ (L₀.subgroupOf S).map κ)
    refine ⟨l,?_⟩
    apply e.linearEquiv.injective
    change e.linearEquiv (σ (κ l) u) = e.linearEquiv v
    rw [he]
    change e.linearEquiv ((σ.comp C.subtype) k u)=e.linearEquiv v
    rw [e.intertwines]
    change binarySymplectic E (e.groupEquiv (e.groupEquiv.symm b)) (e.linearEquiv u)=e.linearEquiv v
    rw [e.groupEquiv.apply_symm_apply]
    exact hb

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The entire fixed preimage of the secondary component action lies in the
paired commutator times Z, at the original field degree. -/
theorem replacement_secondary_fixed_preimage_le_paired
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    commutatorPreimage A (Ltilde d.radical a) (Z d.radical a) ≤
      ⁅A,A'⁆ ⊔ Z d.radical a := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let D := commutatorPreimage A (Ltilde d.radical a) (Z d.radical a)
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  let := replacementComponent_normal h d
  obtain ⟨κ,hκ,hk,hL,σ,c,_,hquad,_,hnat⟩ :=
    replacement_secondary_natural_section h d path hb hat hzt hlarge
  let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
  let : Finite (stabilizer d.radical a) := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  have hfull := replacement_secondary_fully_moved h d path hb hat hzt hlarge κ hL σ c
  have hcard : Nat.card B = (2^n)^3 :=
    (replacement_secondary_actor_image h d path hb hat hzt hlarge κ hk).2.trans
      (replacement_paired_secondary_orders h d path hb hat hzt hlarge).2
  have hBC : B ≤ replacementComponent d :=
    replacement_secondary_actor_le_component h d path hb hat hzt hlarge κ
      (replacementComponent d) hk hL
  have hbound := fully_moved_fixed_le_displacement σ (replacementComponent d) n h.nonbinary
    hfull hnat B hBC hcard hquad
  have hD : c.imageSpace D = fixedSpace σ (replacementComponent d) := by
    rw [c.fixed_image_eq (Ltilde d.radical a) (Ltilde_le_stabilizer a)
      (c.section_le.trans (Z_normalized d.radical a)),fixedSpace_comp_map,hL]
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g
        (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
          (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
        a path.start_color (by
          rw [g.distance_constant a path.start_color]
          change 0 < g.b d.radical
          omega) z path.end_color path.critical }
  have hl : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge)) path.end_color
  have hA'S : A' ≤ stabilizer d.radical a :=
    (replacement_secondary_orbit_bounds h d rev hb hzt hat hl).1.trans
      (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by
        rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color]
        exact hb))
  have him : c.imageSpace A = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    exact (c.mem_imageSpace_iff A v).mpr ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hcomm : c.imageSpace ⁅A,A'⁆ = subspaceCommutator σ ⊤ B := by
    rw [commutator_comm,c.imageSpace_commutator _ _ hA'S le_rfl,
      him,subspaceCommutator_comp_map]
  have hcommA : ⁅A,A'⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp
    (hA'S.trans c.normalized)
  change D ≤ ⁅A,A'⁆ ⊔ Z d.radical a
  intro x hx
  let u : A := ⟨x,(commutatorPreimage_le _ _ _) hx⟩
  have hu : (c.coordinates u).toAdd ∈ c.imageSpace D :=
    (c.mem_imageSpace_iff D _).mpr ⟨u,hx,rfl⟩
  have hv : (c.coordinates u).toAdd ∈ c.imageSpace ⁅A,A'⁆ :=
    hcomm.symm ▸ hbound (hD ▸ hu)
  exact (c.coordinates_mem_imageSpace_iff _ hcommA u).mp hv

/-- The paired Frattini calculation makes the entire fixed preimage
 elementary abelian, without discarding its central Z-layer. -/
theorem replacement_secondary_fixed_preimage_elementary
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    IsElementaryAbelian 2 (commutatorPreimage A (Ltilde d.radical a) (Z d.radical a)) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g
        (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
          (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
        a path.start_color (by
          rw [g.distance_constant a path.start_color]
          change 0 < g.b d.radical
          omega) z path.end_color path.critical }
  have hl : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge)) path.end_color
  have hAQ := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  have hA'Q := (replacement_secondary_orbit_bounds h d rev hb hzt hat hl).1
  have hd : (cosetGraph d.radical).dist a z = 2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  have hAS' : A ≤ stabilizer d.radical z := hAQ.trans
    (Q_le_stabilizer_of_dist_two d.radical a z path.start_color hd)
  have hA'S : A' ≤ stabilizer d.radical a := hA'Q.trans
    (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by rwa [SimpleGraph.dist_comm]))
  let : Finite (stabilizer d.radical a) := finite_stabilizer _ _
  let : Finite (stabilizer d.radical z) := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion hAS') (inclusion_injective _)
  let : Finite A' := Finite.of_injective (inclusion hA'S) (inclusion_injective _)
  have hCA : ⁅A,A'⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp
    (hA'S.trans (conjugatesIn_normalized _ _))
  have hCA' : ⁅A,A'⁆ ≤ A' := le_normalizer_iff_commutator_le_right.mp
    (hAS'.trans (conjugatesIn_normalized _ _))
  let : IsElementaryAbelian 2 (⁅A,A'⁆ : Subgroup (FreeAmalgam d.radical)) :=
    finite_common_subgroup_elementary_of_disjoint_frattini
      ((Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d)
        a path.start_color).of_injective (inclusion hAQ) (inclusion_injective _))
      ((Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d)
        z path.end_color).of_injective (inclusion hA'Q) (inclusion_injective _))
      hCA hCA' (replacement_paired_frattini_disjoint h d path hb hat hzt hlarge)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hZ : Z d.radical a ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)).trans
      (centralizer_le hAQ)
  let : IsElementaryAbelian 2 (⁅A,A'⁆ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    IsElementaryAbelian.sup_of_le_centralizer (hZ.trans (centralizer_le hCA))
  exact IsElementaryAbelian.of_le
    (replacement_secondary_fixed_preimage_le_paired h d path hb hat hzt hlarge)

/-- Natural-vector transitivity forces the actual secondary orbit to be
 elementary; both its cover kernel and its original Z-layer are retained. -/
theorem replacement_secondary_elementary
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    IsElementaryAbelian 2
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let D := commutatorPreimage A (Ltilde d.radical a) (Z d.radical a)
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  let := replacementComponent_normal h d
  obtain ⟨κ,_,hk,hL,σ,c,_,_,_,hnat⟩ :=
    replacement_secondary_natural_section h d path hb hat hzt hlarge
  let C := replacementComponent d
  let s := MovedSection.ofNormal σ C
  obtain ⟨c'⟩ := full_secondary_quotient_section (stabilizer d.radical a) A (Z d.radical a)
    (Ltilde d.radical a) (Ltilde_le_stabilizer a) (Z_normalized d.radical a)
    σ C κ hL c (replacement_secondary_fully_moved h d path hb hat hzt hlarge κ hL σ c)
  obtain ⟨_,_,E,hE,⟨e⟩⟩ := hnat
  let : IsElementaryAbelian 2 D :=
    replacement_secondary_fixed_preimage_elementary h d path hb hat hzt hlarge
  let : IsElementaryAbelian 2 Y :=
    Sp4Four.secondarySeed_elementary d.radical g path.end_color (by omega)
  exact elementary_span_of_natural_section (stabilizer d.radical a) Y D (Ltilde d.radical a)
    C κ hL (MovedSection.action σ s) c' E e
    (replacement_secondary_fixed_preimage_centralizes h d path hb hat hzt hlarge)

/-- The paired-orbit calculation contradicts escape of the whole intrinsic
core from the Frattini and omega layers. -/
theorem replacement_core_frattini_bound_of_path
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a := by
  by_contra hlarge
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let : IsElementaryAbelian 2 A := replacement_secondary_elementary h d path hb hat hzt hlarge
  have hYA : Y ≤ A := by
    change Y ≤ conjugatesIn Y (stabilizer d.radical a)
    rw [Sp4Four.conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy _ _
  have hYQ : ⁅Y,Q d.radical a⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    rw [replacement_kernel_eq_secondary_sup_intersection h d path hb hat hzt hlarge]
    apply sup_le
    · exact A.le_centralizer.trans (centralizer_le hYA)
    · exact inf_le_right.trans
        ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical z path.end_color))).trans
          (centralizer_le (Sp4Four.secondarySeed_le d.radical a t z)))
  have hAQ : A ≤ Q d.radical a := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  have hAC : A ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [(replacement_secondary_commutator_eq_seed h d path hb hat hzt hlarge).1]
    exact hYQ
  have hAX : A ≤ X d.radical a := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hAQ hx,elemPow_eq_one_of_isElementaryAbelian x hx,hAC hx⟩
  exact hlarge ((replacement_core_le_secondary_orbit h d path hb hat hzt hlarge).trans
    (hAX.trans le_sup_right))

/-- The whole intrinsic replacement core is Frattini-small at distance two. -/
theorem replacement_graph_core_frattini_bound
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  exact replacement_core_frattini_bound_of_path h d path hb hat hzt

/-- Source (3.6) gives every short-group clause and the actual natural block
model for the original component, with its original field degree. -/
theorem short_and_natural_of_distance_two
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    IsShort K ∧ ∃ E : BinaryField, E.degree = n ∧
      IsLinearBlockModel K (binarySymplectic E) :=
  short_and_natural_of_replacement_graph_frattini_small h d
    (replacement_graph_core_frattini_bound h d g hb)

/-- With source (3.7)'s degree restriction supplied, distance two gives the
block for the original component, without any whole-core premise. -/
theorem block_of_degree_two_distance_two
    (g : Geometry d.radical) (hb : g.b d.radical = 2) (hn : n = 2) :
    IsSp4FourBlock K :=
  block_of_degree_two_replacement_graph_frattini_small h d hn
    (replacement_graph_core_frattini_bound h d g hb)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
