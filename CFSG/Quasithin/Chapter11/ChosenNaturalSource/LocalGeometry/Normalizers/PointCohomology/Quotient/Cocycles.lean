module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Center
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# The literal corrected quotient in commutator coordinates

Conjugating an element of Q by L displaces it in V. Projection to V/C_V(L)
therefore gives a crossed homomorphism for the original marked action.
Centralization of V by Q makes this assignment multiplicative. Two-perfection
of the block kills a displacement in C_V(L), so its kernel is exactly C_T(L).
Consequently the literal Q/C_T(L) embeds in crossed homomorphisms; no elementary
structure or embedding of that quotient is assumed.

Source: Aschbacher–Smith C.1.13(a,b), printed pp.124–125, used in 11.1.5,
printed pp.765–766. The finite-dimensional model comparison is a separate step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) {F : BinaryField} (c : Coordinates D F)

/-- The original V/C_V(L) coordinates form a section for the literal L-action. -/
def seedSection : BinaryConjugationSection L V (V ⊓ centralizer (L : Set G))
    ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) where
  section_le := D.le_component
  kernel_le := inf_le_left
  normalized := D.normalizes
  coordinates := c.projection
  onto := c.projection_surjective
  kernel_eq := by
    ext v
    exact (c.projection_eq_one_iff v).trans ⟨fun h => ⟨v.property,h⟩, fun h => h.2⟩
  equivariant l v := c.projection_component_conjugation l v

omit [Finite G] in
private theorem core_le_sylow :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

include D in
/-- The original core is displaced into the chosen seed by the component. -/
theorem core_displacement (hb : ChapterC.IsShort L) :
    ⁅L,(L ⊔ (T : Subgroup G)).pCoreIn 2⁆ ≤ V := by
  rw [commutator_comm, core_commutator_eq_seed D hb]

/-- The commutator cocycle of an original core element, in the natural quotient. -/
def coreCocycle (hb : ChapterC.IsShort L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    cocycles ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) := by
  exact (seedSection D c).commutatorCocycle c.quotientMap _ (core_displacement D hb) q

/-- Q centralizes V, hence the crossed-homomorphism assignment is a group map. -/
def coreCocycleHom (hb : ChapterC.IsShort L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 →*
      Multiplicative (cocycles ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)) where
  toFun q := Multiplicative.ofAdd (coreCocycle D c hb q)
  map_one' := by
    apply Subtype.ext
    funext l
    change (c.projection ⟨⁅(l : G), (1 : G)⁆,_⟩).toAdd = 0
    simp only [commutatorElement_one_right]
    exact congrArg Multiplicative.toAdd c.projection.map_one
  map_mul' q r := by
    apply Subtype.ext
    funext l
    let cq : V := ⟨⁅(l : G),(q : G)⁆,
      core_displacement D hb (commutator_mem_commutator l.property q.property)⟩
    let cr : V := ⟨⁅(l : G),(r : G)⁆,
      core_displacement D hb (commutator_mem_commutator l.property r.property)⟩
    have hc : (q : G) * (cr : G) = (cr : G) * q :=
      (D.core_centralizes q.property cr cr.property).symm
    have he : (⟨⁅(l : G), ((q*r : (L ⊔ (T : Subgroup G)).pCoreIn 2) : G)⁆,
        core_displacement D hb (commutator_mem_commutator l.property (q*r).property)⟩ : V) = cq*cr := by
      apply Subtype.ext
      change ⁅(l : G), (q : G)*(r : G)⁆ = (cq : G)*(cr : G)
      rw [commutatorElement_mul_right_eq_mul_conj]
      change (cq : G)*(q : G)*(cr : G)*(q : G)⁻¹ = _
      rw [mul_assoc (cq : G), hc, ← mul_assoc, mul_inv_cancel_right]
    change (c.projection _).toAdd = (c.projection cq).toAdd + (c.projection cr).toAdd
    rw [he, map_mul]
    rfl

include D in
private theorem centralizes_of_displacement_fixed (hb : ChapterC.IsShort L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hfix : ∀ l : L, ⁅(l : G),(q : G)⁆ ∈ centralizer (L : Set G)) :
    (q : G) ∈ centralizer (L : Set G) := by
  let := D.elementary
  let d : L →* V := {
    toFun l := ⟨⁅(l : G),(q : G)⁆,
      core_displacement D hb (commutator_mem_commutator l.property q.property)⟩
    map_one' := by apply Subtype.ext; exact commutatorElement_one_left _
    map_mul' l m := by
      apply Subtype.ext
      change ⁅(l : G)*(m : G),(q : G)⁆ = ⁅(l : G),(q : G)⁆ * ⁅(m : G),(q : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul, hfix m l l.property,
        mul_inv_cancel_right]
      exact congrArg (fun v : V => (v : G)) (mul_comm
        (⟨⁅(m : G),(q : G)⁆,core_displacement D hb
          (commutator_mem_commutator m.property q.property)⟩ : V)
        (⟨⁅(l : G),(q : G)⁆,core_displacement D hb
          (commutator_mem_commutator l.property q.property)⟩ : V)) }
  have hd := hb.twoPerfect.hom_eq_one_of_isPGroup (IsElementaryAbelian.isPGroup 2 V) d
  intro l hl
  have he : ⁅l,(q : G)⁆ = 1 := congrArg (fun f : L →* V => (f ⟨l,hl⟩ : G)) hd
  exact commutatorElement_eq_one_iff_mul_comm.mp he

/-- The kernel is exactly the original C_T(L), as a subgroup of Q. -/
theorem coreCocycleHom_ker (hb : ChapterC.IsShort L) :
    (coreCocycleHom D c hb).ker =
      (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
  ext q
  constructor
  · intro h
    refine ⟨core_le_sylow q.property, centralizes_of_displacement_fixed D hb q ?_⟩
    intro l
    apply (c.projection_eq_one_iff ⟨⁅(l : G),(q : G)⁆,
      core_displacement D hb (commutator_mem_commutator l.property q.property)⟩).mp
    have he := congrArg (fun z : Multiplicative (cocycles
      ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)) => z.toAdd.val l) h
    exact Multiplicative.toAdd.injective he
  · intro h
    apply Subtype.ext
    funext l
    change (c.projection ⟨⁅(l : G),(q : G)⁆,_⟩).toAdd = 0
    have he : ⁅(l : G),(q : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (h.2 l l.property)
    simp only [he]
    exact congrArg Multiplicative.toAdd c.projection.map_one

omit [Finite G] in
/-- Relative normality of C_T(L), for the literal quotient used below. -/
theorem componentCentralizer_normal_core (D : ChosenModule T L V) :
    ((((T : Subgroup G) ⊓ centralizer (L : Set G))).subgroupOf
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le _ _).trans (join_normalizes_componentCentralizer D))

/-- The corrected literal quotient embeds in crossed homomorphisms of the original action. -/
def coreQuotientCocycle (hb : ChapterC.IsShort L) :
    letI := componentCentralizer_normal_core D
    (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2))) →*
      Multiplicative (cocycles ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)) := by
  let := componentCentralizer_normal_core D
  exact QuotientGroup.lift _ (coreCocycleHom D c hb) (coreCocycleHom_ker D c hb).ge

/-- No injectivity premise is imposed on Q/C_T(L). -/
theorem coreQuotientCocycle_injective (hb : ChapterC.IsShort L) :
    Function.Injective (coreQuotientCocycle D c hb) := by
  let := componentCentralizer_normal_core D
  exact (QuotientGroup.injective_lift_iff _ _ (coreCocycleHom_ker D c hb).ge).mpr (coreCocycleHom_ker D c hb).symm

/-- The embedding uses the original quotient projection, on every q. -/
theorem coreQuotientCocycle_mk (hb : ChapterC.IsShort L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    coreQuotientCocycle D c hb (QuotientGroup.mk q) = coreCocycleHom D c hb q := rfl

include c in
/-- The actual corrected quotient is elementary abelian, as required in C.1.13(a). -/
theorem coreQuotient_elementary (hb : ChapterC.IsShort L) :
    letI := componentCentralizer_normal_core D
    IsElementaryAbelian 2 (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2))) := by
  let := componentCentralizer_normal_core D
  let Qbar := (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
    (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)))
  have hp (q : Qbar) : q^2 = 1 := by
    apply coreQuotientCocycle_injective D c hb
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    change 2 • (coreQuotientCocycle D c hb q).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

/-- On V the actual displacement map is the principal-cocycle map. -/
theorem coreCocycle_on_seed (hb : ChapterC.IsShort L) (v : V) :
    coreCocycle D c hb (inclusion D.le_core v) =
      principal ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) (c.projection v).toAdd := by
  apply Subtype.ext
  funext l
  have he : (⟨⁅(l : G),(v : G)⁆,core_displacement D hb
      (commutator_mem_commutator l.property (D.le_core v.property))⟩ : V) =
      V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹ := rfl
  change (c.projection ⟨⁅(l : G),(v : G)⁆,core_displacement D hb
    (commutator_mem_commutator l.property (D.le_core v.property))⟩).toAdd =
      c.modelAction (c.quotientMap l) (c.projection v).toAdd -
    (c.projection v).toAdd
  rw [he, map_mul, map_inv]
  change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd +
    -(c.projection v).toAdd = _
  rw [c.projection_component_conjugation,sub_eq_add_neg]

/-- Principal cocycles detect exactly VC_T(L), with the original denominator. -/
theorem coreCocycle_principal_iff (hb : ChapterC.IsShort L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    coreCocycle D c hb q ∈ (principal ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap)).range ↔
      (q : G) ∈ cohomologyDenominator T L V := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    let vQ := inclusion D.le_core v
    have he : coreCocycleHom D c hb q = coreCocycleHom D c hb vQ := by
      apply Multiplicative.toAdd.injective
      change coreCocycle D c hb q = coreCocycle D c hb (inclusion D.le_core v)
      rw [coreCocycle_on_seed D c hb v, hv]
      exact hw.symm
    have hk : q*vQ⁻¹ ∈ (coreCocycleHom D c hb).ker := by
      change coreCocycleHom D c hb (q*vQ⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [coreCocycleHom_ker] at hk
    have hm := (cohomologyDenominator T L V).mul_mem
      (show ((q*vQ⁻¹ : (L ⊔ (T : Subgroup G)).pCoreIn 2) : G) ∈
        cohomologyDenominator T L V from mem_sup_right hk)
      (show (v : G) ∈ cohomologyDenominator T L V from mem_sup_left v.property)
    change (q : G) * (v : G)⁻¹ * (v : G) ∈ cohomologyDenominator T L V at hm
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm
  · intro hq
    obtain ⟨v,hv,z,hz,he⟩ := denominator_factor D hq
    have hzQ : z ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      have h := ((L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
        (((L ⊔ (T : Subgroup G)).pCoreIn 2).inv_mem (D.le_core hv)) q.property
      rw [←he,inv_mul_cancel_left] at h
      exact h
    let v' : V := ⟨v,hv⟩
    let z' : (L ⊔ (T : Subgroup G)).pCoreIn 2 := ⟨z,hzQ⟩
    have hzker : z' ∈ (coreCocycleHom D c hb).ker := by
      rw [coreCocycleHom_ker]
      exact hz
    refine ⟨(c.projection v').toAdd, ?_⟩
    rw [←coreCocycle_on_seed D c hb v']
    have hqeq : q = inclusion D.le_core v' * z' := Subtype.ext he.symm
    have hm : coreCocycleHom D c hb q = coreCocycleHom D c hb (inclusion D.le_core v') := by
      rw [hqeq,map_mul,MonoidHom.mem_ker.mp hzker,mul_one]
    exact (congrArg Multiplicative.toAdd hm).symm


/-- Conjugation of the original Q by an element of L. -/
def componentConjugateCore (l : L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) : (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  ⟨l * (q : G) * (l : G)⁻¹,
    le_normalizer_iff.mp
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
      l (mem_sup_left l.property) q q.property⟩

/-- Equivariance for literal L-conjugation and the universal cocycle action. -/
theorem coreCocycle_equivariant (hb : ChapterC.IsShort L) (l : L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    coreCocycle D c hb (componentConjugateCore l q) =
      universalAction ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) l (coreCocycle D c hb q) := by
  let v : V := ⟨⁅(l : G),(q : G)⁆,
    core_displacement D hb (commutator_mem_commutator l.property q.property)⟩
  have he : componentConjugateCore l q = inclusion D.le_core v * q := by
    apply Subtype.ext
    change (l : G)*(q : G)*(l : G)⁻¹ = ⁅(l : G),(q : G)⁆*(q : G)
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  calc
    coreCocycle D c hb (componentConjugateCore l q) =
        coreCocycle D c hb (inclusion D.le_core v) + coreCocycle D c hb q := by
      rw [he]
      exact congrArg Multiplicative.toAdd
        ((coreCocycleHom D c hb).map_mul (inclusion D.le_core v) q)
    _ = principal ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) (c.projection v).toAdd +
        coreCocycle D c hb q := by rw [coreCocycle_on_seed D c hb v]
    _ = coreCocycle D c hb q +
        principal ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) (c.projection v).toAdd := add_comm _ _
    _ = universalAction ((restrictScalars (k := ZMod 2) c.modelAction).comp c.quotientMap) l (coreCocycle D c hb q) := rfl


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
