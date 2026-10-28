module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.RadicalAction.Centralization
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores

/-!
# The full shear image of the original SL₃ plane radical

The scalar-centralizer argument makes the actual LT action semilinear,
using the original surjective marking of L onto the full SL₃ group. Fixing
V₂ removes the field twist; two-power order in characteristic two makes the
remaining quotient scalar one. Every radical operator is therefore a shear.
The original L₂ core maps onto every such shear, giving equality of images.

The common published alignment is retained in both the vector coordinates
and the action. The final comparison is with Coordinates.sylowAction itself,
through the original quotient projection. The internal surjective variant
of the semilinear argument adapts SL3OddNaturalNormalizer.centralizer_scalar.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770.
-/

@[expose] public noncomputable section


open Subgroup Representation Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction.Model
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

private theorem normalizer_semilinear_of_surjective (L : Subgroup H) [L.Normal]
    (e : L →* Matrix.SpecialLinearGroup (Fin 3) F)
    (he : Function.Surjective e)
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (h : H) : ∃ σ : F ≃+* F, ∀ (c : F) (v : Fin 3 → F),
      ρ h (c • v) = σ c • ρ h v := by
  let f (c : F) : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => ρ h (c • ρ h⁻¹ v)
      map_zero' := by simp
      map_add' := by intro v w; simp [smul_add] }
  have hf (c : F) : ∃ d : F, ∀ v, f c v = d • v := by
    apply SL3OddNaturalNormalizer.centralizer_scalar
    intro g v
    obtain ⟨x,hxg⟩ := he g
    let y : L := ⟨h⁻¹ * (x : H) * h, (inferInstance : L.Normal).conj_mem' x x.property h⟩
    have hx (v : Fin 3 → F) : g.val.mulVec v = ρ (x : H) v := by
      rw [hnat]
      rw [hxg]
    have hy (c : F) (v : Fin 3 → F) : ρ (y : H) (c • v) = c • ρ (y : H) v := by
      simp only [hnat, Matrix.mulVec_smul]
    have hy₁ (v : Fin 3 → F) : ρ h⁻¹ (ρ (x : H) v) = ρ (y : H) (ρ h⁻¹ v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel, mul_one]
    have hy₂ (v : Fin 3 → F) : ρ h (ρ (y : H) v) = ρ (x : H) (ρ h v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel_left]
    change ρ h (c • ρ h⁻¹ (g.val.mulVec v)) = g.val.mulVec (ρ h (c • ρ h⁻¹ v))
    rw [hx, hx, hy₁, ← hy, hy₂]
  let φ : F → F := fun c => (f c (Pi.single 0 1)) 0
  have hφ (c : F) (v : Fin 3 → F) : f c v = φ c • v := by
    obtain ⟨d, hd⟩ := hf c
    have he : φ c = d := by simp [φ, hd]
    exact he ▸ hd v
  have hcancel (v : Fin 3 → F) : ρ h (ρ h⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hcancel' (v : Fin 3 → F) : ρ h⁻¹ (ρ h v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hmul (a b : F) (v : Fin 3 → F) : f (a * b) v = f a (f b v) := by
    simp [f, hcancel', mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, f, hcancel]
      map_mul' := by
        intro a b
        change (f (a * b) (Pi.single 0 1)) 0 = φ a * φ b
        rw [hmul, hφ, hφ]
        simp
      map_zero' := by simp [φ, f]
      map_add' := by intro a b; simp [φ, f, add_smul] }
  have hbij : Function.Bijective φhom :=
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩
  refine ⟨RingEquiv.ofBijective φhom hbij, fun c v => ?_⟩
  have he := hφ c (ρ h v)
  simpa only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hcancel',
    RingEquiv.ofBijective_apply, φhom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using he

variable [CharP F 2]

omit [Finite F] in
private theorem shear_of_fixed_plane
    (f : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F))
    (σ : F ≃+* F) (hσ : ∀ c v, f (c • v) = σ c • f v)
    (hfix : ∀ v : Fin 3 → F, v 2 = 0 → f v = v)
    (k : ℕ) (hpow : f ^ (2 ^ k) = 1) :
    ∃ a b : F, ∀ v, f v = ![v 0 + a * v 2, v 1 + b * v 2, v 2] := by
  have hs (c : F) : σ c = c := by
    have hh := hσ c ![1,0,0]
    rw [hfix _ (by simp),hfix _ (by simp)] at hh
    simpa using (congrFun hh 0).symm
  have hlin (c : F) (v : Fin 3 → F) : f (c • v) = c • f v := by
    rw [hσ,hs]
  let z := f ![0,0,1]
  have hform (v : Fin 3 → F) :
      f v = ![v 0 + z 0 * v 2, v 1 + z 1 * v 2, z 2 * v 2] := by
    have hv : v = v 0 • ![1,0,0] + v 1 • ![0,1,0] + v 2 • ![0,0,1] := by
      ext i
      fin_cases i <;> simp
    rw [hv,map_add,map_add,hlin,hlin,hlin,hfix _ (by simp),hfix _ (by simp)]
    ext i
    fin_cases i <;> simp [z,mul_comm]
  have hlast (n : ℕ) (v : Fin 3 → F) : ((f ^ n) v) 2 = (z 2)^n * v 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',LinearEquiv.mul_apply,hform]
      change z 2 * ((f ^ n) v) 2 = (z 2)^(n+1) * v 2
      rw [ih,pow_succ]
      ring
  have hd : (z 2)^(2^k) = 1 := by
    simpa [hpow] using (hlast (2^k) ![0,0,1]).symm
  have hd1 : z 2 = 1 := by
    have hh : (z 2 - 1)^(2^k) = 0 := by
      rw [sub_pow_char_pow,hd,one_pow,sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (by decide))).mp hh)
  exact ⟨z 0,z 1,fun v => by simpa [hd1] using hform v⟩

open Matrix.PSL3.LinearThree

private def shear (a b : F) : lineLocalSL F :=
  affineToLine F (SemidirectProduct.inl (Multiplicative.ofAdd ![a,b]))

omit [Algebra (ZMod 2) F] in
private theorem shear_mem_core (a b : F) : shear a b ∈ pCore 2 (lineLocalSL F) := by
  rw [lineLocalSL_twoCore_eq,mem_lineRadicalSL_iff]
  exact ⟨rfl,rfl,rfl,rfl⟩

omit [Finite F] [Algebra (ZMod 2) F] [CharP F 2] in
private theorem shear_apply (a b : F) (v : Fin 3 → F) :
    specialLinearNatural 3 (shear a b).val v = ![v 0+a*v 2,v 1+b*v 2,v 2] := by
  change (shear a b).val.val.mulVec v = _
  ext i
  fin_cases i <;> simp [shear,affineToLine,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction.Model



set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction
open PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

def ambientJoin (_D : ChosenModule T L V) : Subgroup G := L ⊔ (T : Subgroup G)

omit [Finite G] in
theorem ambientJoin_normalizes_component : ambientJoin D ≤ normalizer (L : Set G) :=
  sup_le L.le_normalizer D.sylow_normalizes_component

include S in
theorem ambientJoin_normalizes_seed : ambientJoin D ≤ normalizer (V : Set G) :=
  sup_le D.normalizes S.sylow_normalizes

def ambientAction : Representation (ZMod 2) (ambientJoin D) (Fin 3 → S.field.Carrier) :=
  (coordinates D S m).conjugationAction
    (ambientJoin_normalizes_component D) (ambientJoin_normalizes_seed D S)

def basis : (Fin 3 → S.field.Carrier) ≃ₗ[ZMod 2] (Fin 3 → S.field.Carrier) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → S.field.Carrier)
    ((restrictScalars (k := ZMod 2) (specialLinearNatural (k := S.field.Carrier) 3)).asGroupHom
      (alignment D S m)⁻¹)

/-- Coordinates on all of the original V, after the common Sylow alignment. -/
def vectorEquiv : V ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
  (naturalEquiv D S m).trans (basis D S m).toAddEquiv.toMultiplicative

/-- The actual L T action in the common flag coordinates. -/
def alignedAction : Representation (ZMod 2) (ambientJoin D) (Fin 3 → S.field.Carrier) where
  toFun g := ((basis D S m).toLinearMap.comp (ambientAction D S m g)).comp
    (basis D S m).symm.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    change basis D S m (ambientAction D S m 1 ((basis D S m).symm v)) = v
    rw [map_one,Module.End.one_apply,LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, map_mul,Module.End.mul_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem alignedAction_projection (g : ambientJoin D) (v : V) :
    (vectorEquiv D S m (V.normalizerMonoidHom
      (inclusion (ambientJoin_normalizes_seed D S) g) v)).toAdd =
      alignedAction D S m g (vectorEquiv D S m v).toAdd := by
  change basis D S m ((coordinates D S m).projection
      (V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed D S) g) v)).toAdd =
    basis D S m (ambientAction D S m g
      ((basis D S m).symm (basis D S m ((coordinates D S m).projection v).toAdd)))
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (basis D S m) ((coordinates D S m).conjugationAction_projection
    (ambientJoin_normalizes_component D) (ambientJoin_normalizes_seed D S) g v).symm

theorem vectorEquiv_mem_plane (v : V) :
    (v : G) ∈ (flag D S m).Vi 1 ↔ (vectorEquiv D S m v).toAdd 2 = 0 :=
  ((coordinates D S m).mem_preimage _ v).trans
    (mem_flagFor_iff (alignment D S m) 1 _)

private theorem ambientAction_component (l : L) (w : Fin 3 → S.field.Carrier) :
    ambientAction D S m (inclusion le_sup_left l) w =
      specialLinearNatural 3 ((coordinates D S m).quotientMap l) w := by
  obtain ⟨v,hv⟩ := (coordinates D S m).projection_surjective (Multiplicative.ofAdd w)
  have he : ((coordinates D S m).projection v).toAdd = w := congrArg Multiplicative.toAdd hv
  rw [← he]
  change (coordinates D S m).conjugationAction _ _ _ _ = _
  rw [Coordinates.conjugationAction_projection]
  exact (coordinates D S m).projection_component_conjugation l v

theorem alignedAction_component (l : L) (w : Fin 3 → S.field.Carrier) :
    alignedAction D S m (inclusion le_sup_left l) w =
      specialLinearNatural 3 (alignedQuotient D S m l) w := by
  change basis D S m (ambientAction D S m (inclusion le_sup_left l)
    ((basis D S m).symm w)) = _
  rw [ambientAction_component]
  change specialLinearNatural 3 (alignment D S m)⁻¹
    (specialLinearNatural 3 ((coordinates D S m).quotientMap l)
      (specialLinearNatural 3 ((alignment D S m)⁻¹)⁻¹ w)) = _
  simp only [alignedQuotient, MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply,map_mul,Module.End.mul_apply]
  rfl

theorem alignedAction_semilinear (g : ambientJoin D) :
    ∃ σ : S.field.Carrier ≃+* S.field.Carrier, ∀ c v,
      alignedAction D S m g (c • v) = σ c • alignedAction D S m g v := by
  let N := L.subgroupOf (ambientJoin D)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (ambientJoin_normalizes_component D)
  let e : N ≃* L := subgroupOfEquivOfLe le_sup_left
  let q := (alignedQuotient D S m).comp e.toMonoidHom
  apply Model.normalizer_semilinear_of_surjective N q
    ((alignedQuotient_surjective D S m).comp e.surjective) (alignedAction D S m)
  intro l v
  exact alignedAction_component D S m (e l) v

theorem radical_le_ambientJoin : (flag D S m).Ri 1 ≤ ambientJoin D :=
  (localRadical_le_sylow _).trans le_sup_right

def radicalInclusion : (flag D S m).Ri 1 →* ambientJoin D :=
  inclusion (radical_le_ambientJoin D S m)

/-- The original radical operator, with its original ambient conjugation. -/
def radicalOperator : (flag D S m).Ri 1 →*
    ((Fin 3 → S.field.Carrier) ≃ₗ[ZMod 2] (Fin 3 → S.field.Carrier)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → S.field.Carrier)).toMonoidHom.comp
    ((alignedAction D S m).asGroupHom.comp (radicalInclusion D S m))

/-- The operator is exactly the original Sylow quotient action conjugated by
its published flag alignment. -/
theorem radicalOperator_eq_sylowAction (r : (flag D S m).Ri 1) (w : Fin 3 → S.field.Carrier) :
    radicalOperator D S m r w = specialLinearNatural 3 (alignment D S m)⁻¹
      ((coordinates D S m).sylowAction S
        ⟨r,localRadical_le_sylow _ r.property⟩
        (specialLinearNatural 3 (alignment D S m) w)) := by
  change specialLinearNatural 3 (alignment D S m)⁻¹
    (ambientAction D S m (radicalInclusion D S m r)
      (specialLinearNatural 3 ((alignment D S m)⁻¹)⁻¹ w)) = _
  rw [inv_inv]
  apply congrArg (specialLinearNatural 3 (alignment D S m)⁻¹)
  obtain ⟨v,hv⟩ := (coordinates D S m).projection_surjective
    (Multiplicative.ofAdd (specialLinearNatural 3 (alignment D S m) w))
  have he : ((coordinates D S m).projection v).toAdd =
      specialLinearNatural 3 (alignment D S m) w := congrArg Multiplicative.toAdd hv
  rw [←he]
  change (coordinates D S m).conjugationAction _ _ _ _ =
    (coordinates D S m).conjugationAction _ _ _ _
  rw [Coordinates.conjugationAction_projection,Coordinates.conjugationAction_projection]
  rfl

theorem radicalOperator_shear (r : (flag D S m).Ri 1) :
    ∃ a b : S.field.Carrier, ∀ v,
      radicalOperator D S m r v = ![v 0+a*v 2,v 1+b*v 2,v 2] := by
  obtain ⟨σ,hσ⟩ := alignedAction_semilinear D S m (radicalInclusion D S m r)
  have hfix (w : Fin 3 → S.field.Carrier) (hw : w 2 = 0) : radicalOperator D S m r w = w := by
    obtain ⟨v,hv⟩ := (vectorEquiv D S m).surjective (Multiplicative.ofAdd w)
    have hvP : (v : G) ∈ (flag D S m).Vi 1 :=
      (vectorEquiv_mem_plane D S m v).mpr (by rw [hv]; exact hw)
    have he : V.normalizerMonoidHom
        (inclusion (ambientJoin_normalizes_seed D S) (radicalInclusion D S m r)) v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr
        (radical_centralizes_plane D S m r.property v.val hvP).symm
    have hh := alignedAction_projection D S m (radicalInclusion D S m r) v
    rw [he,hv] at hh
    exact hh.symm
  have hp : IsPGroup 2 ((flag D S m).Ri 1) := pCore_isPGroup.map _
  obtain ⟨k,hk⟩ := hp r
  exact Model.shear_of_fixed_plane (radicalOperator D S m r) σ hσ hfix k
    (by rw [←map_pow,hk,map_one])

/-- The action of the full intrinsic plane core lies inside the original radical. -/
theorem planeCore_le_radical : ((flag D S m).Li 1).pCoreIn 2 ≤ (flag D S m).Ri 1 := by
  rintro x ⟨l,hl,rfl⟩
  let a : localJoin D S m := ⟨l,mem_sup_left l.property⟩
  have ha : a ∈ (joinPlaneAction D S m).ker := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (plane_core_centralizes D S m
      (mem_map_of_mem _ hl) v.toMul v.toMul.property).symm
  rw [joinPlaneAction_ker] at ha
  exact mem_map_of_mem _ ha

/-- Every pair of shear coefficients is realized by an element of the original radical. -/
theorem radicalOperator_realizes (a b : S.field.Carrier) :
    ∃ r : (flag D S m).Ri 1, ∀ v,
      radicalOperator D S m r v = ![v 0+a*v 2,v 1+b*v 2,v 2] := by
  obtain ⟨l,hl⟩ := localProjection_surjective D S m 1 (Model.shear a b)
  have hlc : l ∈ pCore 2 ((flag D S m).Li 1) := by
    have hc := (localProjection D S m 1).comap_pCore_of_ker_isPGroup
      (localProjection_surjective D S m 1) (localProjection_ker_isTwoGroup D S m 1)
    rw [←hc]
    change localProjection D S m 1 l ∈ pCore 2 (Matrix.PSL3.LinearThree.lineLocalSL S.field.Carrier)
    rw [hl]
    exact Model.shear_mem_core a b
  let r : (flag D S m).Ri 1 := ⟨l,planeCore_le_radical D S m (mem_map_of_mem _ hlc)⟩
  refine ⟨r,fun v => ?_⟩
  change alignedAction D S m (inclusion le_sup_left
    (⟨l,(localResidual_le _ l.property).1⟩ : L)) v = _
  rw [alignedAction_component, ←localProjection_coe,hl]
  exact Model.shear_apply a b v

/-- This identifies the entire operator image with the full shear family. -/
theorem mem_radicalOperator_range (u : (Fin 3 → S.field.Carrier) ≃ₗ[ZMod 2]
    (Fin 3 → S.field.Carrier)) :
    u ∈ (radicalOperator D S m).range ↔ ∃ a b : S.field.Carrier,
      ∀ v, u v = ![v 0+a*v 2,v 1+b*v 2,v 2] := by
  constructor
  · rintro ⟨r,rfl⟩
    exact radicalOperator_shear D S m r
  · rintro ⟨a,b,hu⟩
    obtain ⟨r,hr⟩ := radicalOperator_realizes D S m a b
    exact ⟨r,LinearEquiv.ext (fun v => (hr v).trans (hu v).symm)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.RadicalAction
