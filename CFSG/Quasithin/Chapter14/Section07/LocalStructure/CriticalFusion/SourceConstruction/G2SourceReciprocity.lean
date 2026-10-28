module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceFullActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender

/-!
# Reciprocal critical actors and their common ambient family

For a full pencil actor, the original reciprocal core has index eight.
The geometric reverse path interchanges this index with the actor order,
so it satisfies the same rank selection. Original duality excludes the
flag point from the first partner. Transporting that fact constructs the
reverse full actor and then excludes the reciprocal point from U. This
is the critical-path symmetry of 14.7.61(5), with both actual U-markings
and point markings, rather than the earlier vertex interchange of 14.7.58.

An element of a full critical actor belongs to its derived half exactly
when its ambient commutator has order at most four. Thus the existing
common-family identity identifies the same four-subgroups after reversal:
no matching of the two families or additional symmetry is assumed.
The final theorem applies the original natural/Weyl recognition to construct
the module identification, both actor markings and this family equality
in the branch where the reciprocal point is outside U.

The case Zα ≤ U still requires the original 14.7.60 parabolic argument,
and the final quotient four-cycle construction remains unfinished.
The faithful action, generalized-Fitting identity, original core-commutator
identity and structural input retain their earlier source producers and
final discharge by qt-d-14775-source. No later Data is used.

Source: Aschbacher--Smith, 14.7.61--62 and formulas (d),(a′), printed
pp.1067--1069, with the critical-path reversal of F.9.17 and 14.7.39.
Concrete natural/Weyl calculations retain the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source Subgroup.CosetGeometry.RankTwo
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3}

open Representation Representation.BinaryOffender
open G2Exclusion.MarkedGeometry G2Exclusion.MarkedGeometry.MarkedPencil.Actors
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
include c

/-- Equal ranks give the actual reciprocal path and a full marking on both
orientations. Neither point noncontainment is assumed. -/
theorem source_full_actor_reciprocity
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ path.Zα ≤ F.U) ∧
    ∃ r : SourceReversal.Geometry path, r.path.RankSelection ∧
      r.path.Uα ≤ F.Ri L 1 ∧
      (F.U ⊓ r.path.Qα).relIndex F.U = 8 ∧ Nat.card (star F r.path.Uα) = 8 ∧
      ∃ q : Atlas.G2.SingularPoints (ZMod 2),
        (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  obtain ⟨hD,hidx,hcard⟩ := source_full_actor_core_and_orders c h hab path hAH m E i hi he p hA
  have hpoint := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    path hplace selection m E i hi he p hA
  obtain ⟨r⟩ := LocalReduction.exists_reversal_of_star_ne_bot h structural path hAH
    (path.star_ne_bot selection)
  have hrplace := LocalReduction.critical_le_Ri h structural r.path
  have hrH : r.path.Uα ≤ F.H := hrplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hridx : (F.U ⊓ r.path.Qα).relIndex F.U = 8 :=
    (r.reverse_index_of_placement hAH).trans hcard
  have hrcard : Nat.card (star F r.path.Uα) = 8 :=
    (r.reverse_star_of_placement hrH).trans hidx
  have hrs : r.path.RankSelection := {
    positive := by rw [hridx]; decide
    comparison := by rw [hridx,hrcard] }
  have hrpoint : ¬ r.path.Zα ≤ F.U := by
    intro hh
    apply hpoint
    have hh' := map_mono (f := (MulAut.conj r.conjugator⁻¹).toMonoidHom) hh
    change conjugate r.path.Zα r.conjugator ≤ conjugate F.U r.conjugator at hh'
    rwa [r.tip_point,r.base_U] at hh'
  obtain ⟨q,hq⟩ := source_full_critical_actor_of_point_not_le c h hab r.path hrplace hrs hrpoint
    m E i hi he
  have hrnot := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    r.path hrplace hrs m E i hi he q hq
  refine ⟨hpoint,?_,r,hrs,hrplace,hridx,hrcard,q,hq⟩
  intro hh
  apply hrnot
  apply (map_le_map_iff_of_injective (f := (MulAut.conj r.conjugator⁻¹).toMonoidHom)
    (MulAut.conj r.conjugator⁻¹).injective).mp
  change conjugate (F.Vi 1) r.conjugator ≤ conjugate r.path.Uα r.conjugator
  rwa [r.base_point,r.tip_U]

omit c in
/-- The involutions outside the derived pencil four-group have displacement
three in either recognized module. -/
private theorem model_outer_actor_fixedCodim (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) (a : Atlas.G2.Model (ZMod 2))
    (ha : a ∈ fullCentralizer m.singularMap m.action p)
    (hout : a ∉ commutator (Atlas.G2.Model (ZMod 2))) :
    fixedCodim m.action (zpowers a) = 3 := by
  have spaces (b : Atlas.G2.Model (ZMod 2))
      (hb : b ∈ fullCentralizer m.singularMap m.action p)
      (hbd : b ∉ derivedCentralizer m.singularMap m.action p) :
      fixedSpace m.action (zpowers b) =
        fixedSpace m.action (derivedCentralizer m.singularMap m.action p) := by
    cases m with
    | natural => exact (natural_full_spaces p b hb hbd).2.1
    | weyl => exact (weyl_full_spaces p b hb hbd).2.1
  have hfix : fixedSpace m.action (fullCentralizer m.singularMap m.action p) =
      fixedSpace m.action (derivedCentralizer m.singularMap m.action p) := by
    apply le_antisymm
    · intro v hv b
      exact hv ⟨b,b.property.1⟩
    · intro v hv b
      by_cases hb : (b : Atlas.G2.Model (ZMod 2)) ∈
          derivedCentralizer m.singularMap m.action p
      · exact hv ⟨b,hb⟩
      · have hh : v ∈ fixedSpace m.action (zpowers (b : Atlas.G2.Model (ZMod 2))) :=
          (spaces b b.property hb).symm ▸ hv
        exact (mem_fixedSpace_zpowers_iff m.action (b : Atlas.G2.Model (ZMod 2)) v).mp hh
  have he := spaces a ha (fun hh => hout hh.2)
  have hc := model_fullCentralizer_fixedCodim m p
  unfold fixedCodim at hc ⊢
  rwa [he,←hfix]

/-- Small original commutators detect the derived half of the same full
critical actor. This criterion is preserved by the actual reversal. -/
private theorem source_mem_derivedActorLift_of_small_commutator
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p)
    (b : G) (hb : b ∈ path.Uα)
    (hsmall : Nat.card (⁅F.U,zpowers b⁆ : Subgroup G) ≤ 4) :
    b ∈ derivedActorLift (i.comp (starMap F)) path.Uα := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let a : F.H := ⟨b,hAH hb⟩
  have ha : i (starMap F a) ∈ fullCentralizer m.singularMap m.action p :=
    hA ▸ mem_map_of_mem i (mem_map_of_mem (starMap F) hb)
  have hderived : i (starMap F a) ∈ commutator (Atlas.G2.Model (ZMod 2)) := by
    by_contra hout
    have hc := model_outer_actor_fixedCodim m p (i (starMap F a)) ha hout
    have hd := c.displacement_rank_le_of_commutator_bound (zpowers b) ⁅F.U,zpowers b⁆
      ⊥ bot_le (by rw [commutator_comm]) 2 (by simpa using hsmall) a (mem_zpowers b)
    have ht := fixedCodim_map_equivariant (σ.comp (starMap F)) m.action
      (i.comp (starMap F)) E.symm
      (fun a v => by
        change E.symm (σ (starMap F a) v) = m.action (i (starMap F a)) (E.symm v)
        apply E.injective
        rw [E.apply_symm_apply,he,E.apply_symm_apply]) (zpowers a)
    rw [MonoidHom.map_zpowers,MonoidHom.comp_apply] at ht
    rw [←ht,fixedCodim_zpowers_eq_displacement_rank] at hc
    change Module.finrank (ZMod 2) ((σ.comp (starMap F)) a - LinearMap.id).range ≤ 2 at hd
    omega
  exact ⟨a,⟨hb,hderived⟩,rfl⟩

/-- In the full-actor case the derived lift is intrinsic: it consists exactly
of partner elements whose original commutator has order at most four. -/
theorem source_derivedActorLift_iff_small_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα) (b : G) :
    b ∈ derivedActorLift (i.comp (starMap F)) path.Uα ↔
      b ∈ path.Uα ∧ Nat.card (⁅F.U,zpowers b⁆ : Subgroup G) ≤ 4 := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  constructor
  · intro hb
    refine ⟨derivedActorLift_le _ _ hb,?_⟩
    by_cases hz : ⁅F.U,zpowers b⁆ = ⊥
    · simp only [hz,Subgroup.card_bot]; decide
    have hA' : (path.Uα.subgroupOf F.H).map (i.comp (starMap F)) =
        fullCentralizer m.singularMap m.action p := by
      rw [←map_map]; exact hA
    obtain ⟨l,_,_,hc⟩ := source_commutator_line c h path hplace m E
      (i.comp (starMap F)) (fun a v => he (starMap F a) v) p
      (derivedActorLift (i.comp (starMap F)) path.Uα) (derivedActorLift_le _ _)
      hpoint (derivedActorLift_image _ m p _ hA') b hb hz
    exact hc.le
  · rintro ⟨hb,hsmall⟩
    exact source_mem_derivedActorLift_of_small_commutator c path hAH m E i he p hA b hb hsmall

/-- The original common family is contained in the family of the reverse
marked actor, transported by the actual reversal conjugator. This uses the
literal order-four commutators to detect the reverse derived four-group. -/
private theorem source_family_le_reverse_family
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (r : SourceReversal.Geometry path) (hrplace : r.path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p q : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p)
    (hAr : (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα) :
    ∀ C : Subgroup G,
      C ≠ ⊥ → (∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
        C = ⁅F.U,zpowers b⁆) →
      ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator := by
  have hfam := (source_common_family_of_critical_marking c h path hplace m E i
    (fun a v => he (starMap F a) v) p hpoint hA).1
  intro C hne hC
  have hmem : C ∈ {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
      C = ⁅F.U,zpowers b⁆} := ⟨hne,hC⟩
  rw [hfam] at hmem
  obtain ⟨_,w,hw,hCw⟩ := hmem
  obtain ⟨b,hb,rfl⟩ := hC
  have hsmall := ((source_derivedActorLift_iff_small_commutator c h path hplace m E i he p
    hA hpoint b).mp hb).2
  let f := (MulAut.conj r.conjugator).toMonoidHom
  let w' := f w
  have hU : F.U.map f = r.path.Uα := by
    rw [←r.tip_U]
    exact conjBy_inv' _ _
  have hAback : path.Uα.map f = F.U := by
    rw [←r.base_U]
    exact conjBy_inv' _ _
  have hw' : w' ∈ r.path.Uα := hU ▸ mem_map_of_mem f (polarLift_le c m E p hw)
  have hcomm : (⁅F.U,zpowers b⁆).map f = ⁅F.U,zpowers w'⁆ := by
    rw [hCw,map_commutator,hAback,MonoidHom.map_zpowers]
  have hsmall' : Nat.card (⁅F.U,zpowers w'⁆ : Subgroup G) ≤ 4 := by
    rw [←hcomm,card_map_of_injective (MulAut.conj r.conjugator).injective]
    exact hsmall
  have hrH : r.path.Uα ≤ F.H := hrplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  refine ⟨w',source_mem_derivedActorLift_of_small_commutator c r.path hrH m E i he q hAr
    w' hw' hsmall',?_⟩
  rw [←hcomm]
  change _ = ((⁅F.U,zpowers b⁆).conjBy r.conjugator).conjBy r.conjugator⁻¹
  exact (conjBy_inv _ _).symm

/-- The same ambient family is obtained from both critical orientations.
The derived actor in each orientation is detected by the order of its
actual commutator, so no family-matching premise is imposed. -/
theorem source_family_eq_reverse_family
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (r : SourceReversal.Geometry path) (hrplace : r.path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (p q : Atlas.G2.SingularPoints (ZMod 2))
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p)
    (hAr : (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα) (hrpoint : ¬ F.Vi 1 ≤ r.path.Uα) :
    {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
      C = ⁅F.U,zpowers b⁆} =
    {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
      C = conjugate ⁅F.U,zpowers b⁆ r.conjugator} := by
  let s : SourceReversal.Geometry r.path := {
    path := path
    conjugator := r.conjugator⁻¹
    conjugator_mem := (GeometryGroup T L F).inv_mem r.conjugator_mem
    base_U := by
      rw [←r.tip_U]
      simp only [conjugate,inv_inv]
      exact conjBy_inv' _ _
    tip_U := by
      rw [←r.base_U]
      simp only [conjugate,inv_inv]
      exact conjBy_inv' _ _
    base_point := by
      rw [←r.tip_point]
      simp only [conjugate,inv_inv]
      exact conjBy_inv' _ _
    tip_point := by
      rw [←r.base_point]
      simp only [conjugate,inv_inv]
      exact conjBy_inv' _ _ }
  ext C
  constructor
  · rintro ⟨hne,hC⟩
    exact ⟨hne,source_family_le_reverse_family c h path hplace r hrplace m E i he p q
      hA hAr hpoint C hne hC⟩
  · rintro ⟨hne,b,hb,rfl⟩
    have hbne : ⁅F.U,zpowers b⁆ ≠ ⊥ := by
      intro hz
      apply hne
      rw [hz]
      exact Subgroup.map_bot _
    obtain ⟨a,ha,heq⟩ := source_family_le_reverse_family c h r.path hrplace s hplace m E i he q p
      hAr hA hrpoint _ hbne ⟨b,hb,rfl⟩
    refine ⟨hne,a,ha,?_⟩
    rw [heq]
    change ((⁅F.U,zpowers a⁆).conjBy (r.conjugator⁻¹)⁻¹).conjBy r.conjugator⁻¹ = _
    rw [inv_inv]
    exact conjBy_inv _ _

/-- In the noncontainment branch the original hypotheses construct both
critical markings and the same literal commutator family in the reverse
orientation. No actor marking, reversal or family identity is assumed. -/
theorem source_reciprocal_family_of_partner_point_not_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v)) :
    ∃ (p : Atlas.G2.SingularPoints (ZMod 2)) (r : SourceReversal.Geometry path)
      (q : Atlas.G2.SingularPoints (ZMod 2)),
      (star F path.Uα).map i = fullCentralizer m.singularMap m.action p ∧
      r.path.RankSelection ∧ r.path.Uα ≤ F.Ri L 1 ∧
      (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q ∧
      (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ F.Vi 1 ≤ r.path.Uα) ∧
      ({C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
        C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}) := by
  obtain ⟨p,hA⟩ := source_full_critical_actor_of_point_not_le c h hab path hplace selection
    hZU m E i hi he
  obtain ⟨hpoint,_,r,hrs,hrplace,_,_,q,hAr⟩ :=
    source_full_actor_reciprocity c h hab hcomponent hfit eK structural hf hcomm
      path hplace selection m E i hi he p hA
  have hrpoint := source_marked_point_noncontainment c h hab hcomponent hfit eK hf hcomm
    r.path hrplace hrs m E i hi he q hAr
  exact ⟨p,r,q,hA,hrs,hrplace,hAr,hpoint,hrpoint,
    source_family_eq_reverse_family c h path hplace r hrplace m E i he p q hA hAr hpoint hrpoint⟩


open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

/-- Recognition and the original source hypotheses construct the reciprocal
critical markings and common family in the noncontainment branch. In particular
the quadratic action and rank bound are derived from the actual critical
actor, and no equivariant natural/Weyl identification remains as an input. -/
theorem source_recognized_reciprocal_family
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hZU : ¬ path.Zα ≤ F.U) :
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      (∀ a v, E (m.action (i a) v) = σ a (E v)) ∧
    ∃ (p : Atlas.G2.SingularPoints (ZMod 2)) (r : SourceReversal.Geometry path)
      (q : Atlas.G2.SingularPoints (ZMod 2)),
      (star F path.Uα).map i = fullCentralizer m.singularMap m.action p ∧
      r.path.RankSelection ∧ r.path.Uα ≤ F.Ri L 1 ∧
      (star F r.path.Uα).map i = fullCentralizer m.singularMap m.action q ∧
      (¬ F.Vi 1 ≤ path.Uα) ∧ (¬ F.Vi 1 ≤ r.path.Uα) ∧
      ({C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) path.Uα,
        C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ b ∈ derivedActorLift (i.comp (starMap F)) r.path.Uα,
        C = conjugate ⁅F.U,zpowers b⁆ r.conjugator}) := by
  have hquad : IsQuadratic σ (star F path.Uα) := by
    rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ v
    exact LocalReduction.critical_quadratic h hab c path a ha b hb v
  have hbound : fixedCodim σ (star F path.Uα) ≤ 2 * rank (star F path.Uα) := by
    have hh := (source_critical_offender_of_point_not_le c h hab path hplace selection hZU).2
    omega
  obtain ⟨i,hi,hJ,hmodels⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
    P hP orbit path hplace selection hquad hbound
  have hm : ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      ∀ a v, E (m.action (i a) v) = σ a (E v) := by
    rcases hmodels with ⟨E,he⟩ | ⟨E,he⟩
    · exact ⟨.natural,E,he⟩
    · exact ⟨.weyl,E,he⟩
  obtain ⟨m,E,he⟩ := hm
  exact ⟨i,hi,hJ,m,E,he,
    source_reciprocal_family_of_partner_point_not_le c h hab hcomponent hfit eK structural
      hf hcomm path hplace selection hZU m E i hi he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
