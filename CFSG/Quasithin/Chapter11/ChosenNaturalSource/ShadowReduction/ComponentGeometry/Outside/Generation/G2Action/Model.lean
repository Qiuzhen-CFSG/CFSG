module
public import Theory.Representation.G2NaturalNormalizerOffenders
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Long
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Perfectness
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Odd actions on the exceptional point section

Norm preservation identifies the first natural-vector fixer with the genuine
long local group; nonzero-vector transitivity proves that every vector fixer
is perfect. For an odd natural normalizer, the proved inner-field description
and scalar commutant give its actual operator. Fixing the first vector places
its inner factor in the point parabolic. The literal SL₂ quotient kills the
field factor. Coprimality with q−1 kills the parabolic character, and odd order
kills the remaining two-core element and scalar.

These are the model calculations for the G₂ Hall-order and Hall-action steps
of source 11.4.4, consumed by HallOrder and G2Action. No automorphism coverage,
splitting or quotient-action premise is substituted for a source conclusion.
Source: Aschbacher--Smith, printed p.778 of refs/quasithin.pdf.
The octonion model retains the attribution in LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.G2Action
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion

def pointFixer {F : Type*} [Field F] [CharP F 2] (w : Natural.Space F) :
    Subgroup (Model F) where
  carrier := {g | Natural.action F g w = w}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; change Natural.action F (a*b) w = w; rw [map_mul,Module.End.mul_apply,hb,ha]
  inv_mem' := by
    intro a ha
    change Natural.action F a⁻¹ w = w
    have hh := congrArg (Natural.action F a⁻¹) ha
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] using hh.symm

def firstVector {F : Type*} [Field F] [CharP F 2] : Natural.TraceZero F :=
  ⟨basisVector 0,by simp [Natural.mem_traceZero,trace,basisVector]⟩

theorem first_ne_zero {F : Type*} [Field F] [CharP F 2] :
    Natural.mk F (firstVector (F := F)) ≠ 0 := by
  intro he
  have hh : Natural.mk F (firstVector (F := F)) = Natural.mk F 0 := by simpa using he
  obtain ⟨r,hr⟩ := (Natural.mk_eq_mk_iff F _ _).mp hh
  have h0 := congrFun hr 0
  simp [firstVector,basisVector,unit] at h0

theorem first_pointFixer {F : Type*} [Field F] [CharP F 2] :
    pointFixer (Natural.mk F (firstVector (F := F))) = local₂ := by
  ext g
  rw [local₂_eq_fixingFirstVector]
  change Natural.action F g (Natural.mk F firstVector) = Natural.mk F firstVector ↔
    g.val (basisVector 0) = basisVector 0
  constructor
  · intro hh
    obtain ⟨r,hr⟩ := (Natural.mk_eq_mk_iff F _ _).mp hh
    change r • unit = g.val (basisVector 0) - basisVector 0 at hr
    have he : g.val (basisVector 0) = r • unit + basisVector 0 :=
      (eq_sub_iff_add_eq.mp hr).symm
    have hn := automorphism_norm g (basisVector 0)
    rw [he] at hn
    have hr0 : r=0 := by
      have hs : r*r=0 := by simpa [Atlas.SplitOctonion.norm,unit,basisVector] using hn
      exact mul_self_eq_zero.mp hs
    simpa only [hr0,zero_smul,zero_add] using he
  · intro hh
    change Natural.mk F (Natural.traceZeroAction F g firstVector) = Natural.mk F firstVector
    exact congrArg (Natural.mk F) (Subtype.ext hh)

theorem pointFixer_map {F : Type*} [Field F] [CharP F 2]
    (g : Model F) (w : Natural.Space F) :
    (pointFixer w).map (MulAut.conj g).toMonoidHom = pointFixer (Natural.action F g w) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    change Natural.action F (g*a*g⁻¹) (Natural.action F g w) = Natural.action F g w
    simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply,
      show Natural.action F a w=w from ha]
  · intro hx
    refine ⟨g⁻¹*x*g,?_,by change g*(g⁻¹*x*g)*g⁻¹=x; group⟩
    change Natural.action F (g⁻¹*x*g) w = w
    change Natural.action F x (Natural.action F g w) = Natural.action F g w at hx
    simp only [map_mul,Module.End.mul_apply,hx,Representation.inv_self_apply]

theorem pointFixer_perfect {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) {w : Natural.Space F} (hw : w ≠ 0) :
    Group.IsPerfect (pointFixer w) := by
  obtain ⟨g,hg⟩ := Natural.action_transitive (first_ne_zero (F := F)) hw
  have he : pointFixer w = local₂.map (MulAut.conj g).toMonoidHom := by
    rw [←first_pointFixer,pointFixer_map,hg]
  rw [he]
  let := local₂_isPerfect (F := F) hF
  exact Group.IsPerfect.map _

open Natural.Normalizer LieAutomorphismExtensions HigherParabolicRadical.Long
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

omit [Finite F] in
private theorem first_field (σ : F ≃+* F) :
    Natural.BinarySemilinear.fieldEquivalence F σ (Natural.mk F (firstVector (F := F))) =
      Natural.mk F (firstVector (F := F)) := by
  apply (Natural.BinarySemilinear.coordinatesEquiv F).injective
  change (Natural.BinarySemilinear.coordinatesEquiv F)
    ((Natural.BinarySemilinear.coordinatesEquiv F).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;>
    simp [Natural.BinarySemilinear.coordinatesEquiv,Natural.BinarySemilinear.fieldLinear,
      Restricted.NaturalCoordinates.equiv,Restricted.NaturalCoordinates.projection,
      firstVector,basisVector]

omit [Finite F] in
private theorem first_scalar_lift (g : Model F) (c : F)
    (h : Natural.action F g (Natural.mk F (firstVector (F := F))) =
      c • Natural.mk F (firstVector (F := F))) :
    g.val (basisVector 0) = c • basisVector 0 := by
  rw [←map_smul] at h
  obtain ⟨r,hr⟩ := (Natural.mk_eq_mk_iff F _ _).mp h
  change r • unit = g.val (basisVector 0) - c • basisVector 0 at hr
  have he : g.val (basisVector 0) = r • unit + c • basisVector 0 :=
    (eq_sub_iff_add_eq.mp hr).symm
  have hn := automorphism_norm g (basisVector 0)
  rw [he] at hn
  have hr0 : r=0 := by
    have hs : r*r=0 := by simpa [Atlas.SplitOctonion.norm,unit,basisVector] using hn
    exact mul_self_eq_zero.mp hs
  simpa only [hr0,zero_smul,zero_add] using he

omit [Finite F] in
private theorem inner_field_parabolic
    (t : Representation.BinaryOffender.linearNormalizer (binary F))
    (g : Model F) (σ : F ≃+* F)
    (ha : normalizerAutomorphism F t = MulAut.conj g * fieldAction σ)
    (ht : t.val.val (Natural.mk F (firstVector (F := F))) =
      Natural.mk F (firstVector (F := F))) : g ∈ parabolic₂ := by
  obtain ⟨c,hc⟩ := normalizer_scalar_factor F t g σ ha
  have hh := hc (Natural.mk F (firstVector (F := F)))
  rw [ht,first_field] at hh
  have hc0 : c ≠ 0 := by
    intro he
    rw [he,zero_smul] at hh
    exact first_ne_zero hh
  have hact : Natural.action F g (Natural.mk F (firstVector (F := F))) =
      c⁻¹ • Natural.mk F (firstVector (F := F)) := by
    conv_rhs => rw [hh]
    rw [smul_smul,inv_mul_cancel₀ hc0,one_smul]
  change g ∈ parabolic
  rw [parabolic_eq_pointStabilizer]
  exact (mem_pointStabilizer_iff g).mpr
    ⟨(Units.mk0 c hc0)⁻¹,by simpa only [Units.smul_def,Units.val_inv_eq_inv_val,
      Units.val_mk0] using first_scalar_lift g c⁻¹ hact⟩

private theorem field_trivial (g : Model F) (hg : g ∈ parabolic₂)
    (σ : F ≃+* F)
    (hc : ∀ x ∈ local₂ (F := F),
      (MulAut.conj g * fieldAction σ) x / x ∈ (local₂ (F := F)).pCoreIn 2) :
    σ = 1 := by
  let g' : parabolic₂ (F := F) := ⟨g,hg⟩
  have hact (x : local₂ (F := F)) :
      fullSLHom g' * Matrix.SpecialLinearGroup.map σ.toRingHom (longSLHom x) *
        (fullSLHom g')⁻¹ = longSLHom x := by
    let y := local₂FieldEquiv σ x
    let x' : parabolic₂ (F := F) := ⟨x,local₂_le_parabolic₂ x.property⟩
    let y' : parabolic₂ (F := F) := ⟨y,local₂_le_parabolic₂ y.property⟩
    have hcore := hc x x.property
    rw [local₂_pCoreIn] at hcore
    have hlocal : g*y*g⁻¹ ∈ local₂ :=
      (mem_normalizer_iff.mp (parabolic₂_le_normalizer_local₂ hg) y).mp y.property
    let v : local₂ (F := F) := ⟨g*y*g⁻¹,hlocal⟩
    have hv : longSLHom (v / x) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [longSLHom_ker]
      exact hcore
    have hv' := div_eq_one.mp (by simpa only [map_div] using hv)
    have hvfull : fullSLHom (g'*y'*g'⁻¹) = longSLHom v := fullSLHom_local v
    rw [map_mul,map_mul,map_inv,fullSLHom_local y,longSLHom_field] at hvfull
    exact hvfull.trans hv'
  apply Atlas.RankOneFieldAutomorphisms.field_eq_one_of_SL_inner σ (fullSLHom g')⁻¹
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := longSLHom_surjective y
  have hh := hact x
  change Matrix.SpecialLinearGroup.map σ.toRingHom (longSLHom x) =
    (fullSLHom g')⁻¹ * longSLHom x * ((fullSLHom g')⁻¹)⁻¹
  calc
    _ = (fullSLHom g')⁻¹ * (fullSLHom g' * Matrix.SpecialLinearGroup.map σ.toRingHom (longSLHom x) * (fullSLHom g')⁻¹) * ((fullSLHom g')⁻¹)⁻¹ := by group
    _ = _ := by rw [hh]

/-- An odd actual natural normalizer which fixes the first vector and the
point-local quotient is trivial when its order is coprime to q−1. -/
theorem odd_coprime_point_section_eq_one (hF : 2 < Nat.card F)
    (t : Representation.BinaryOffender.linearNormalizer (binary F))
    {r : ℕ} (ho : Odd r) (hcop : Nat.Coprime r (Nat.card F - 1))
    (ht : t^r=1)
    (hfix : t.val.val (Natural.mk F (firstVector (F := F))) =
      Natural.mk F (firstVector (F := F)))
    (hc : ∀ x ∈ local₂ (F := F),
      normalizerAutomorphism F t x / x ∈ (local₂ (F := F)).pCoreIn 2) : t=1 := by
  obtain ⟨a,ha⟩ := semilinearAction_surjective hF (normalizerAutomorphism F t)
  let g := a.left
  let σ := a.right
  have he : normalizerAutomorphism F t = MulAut.conj g * fieldAction σ := ha.symm
  have hg := inner_field_parabolic t g σ he hfix
  have hσ : σ=1 := field_trivial g hg σ (by simpa only [he] using hc)
  have he' : normalizerAutomorphism F t = MulAut.conj g := by
    rw [he,hσ,map_one,mul_one]
  have hgr : g^r=1 := by
    apply conj_injective_of_center_eq_bot (model_center_eq_bot hF)
    rw [map_pow,←he',←map_pow,ht,map_one,map_one]
  have hscalar : scalarHom (⟨g,hg⟩ : parabolic₂ (F := F)) = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hcop
    · apply orderOf_dvd_of_pow_eq_one
      rw [←map_pow,show (⟨g,hg⟩ : parabolic₂ (F := F))^r=1 from Subtype.ext hgr,map_one]
    · simpa only [Nat.card_units] using orderOf_dvd_natCard (scalarHom (⟨g,hg⟩ : parabolic₂))
  have hgl : g ∈ local₂ := (scalar_eq_one_iff ⟨g,hg⟩).mp hscalar
  let g' : local₂ (F := F) := ⟨g,hgl⟩
  have hgc : g' ∈ pCore 2 local₂ := by
    rw [local₂_pCore,←longSLHom_ker]
    change longSLHom g' = 1
    apply (mem_bot.mp : _ ∈ (⊥ : Subgroup SL(2,F)) → _)
    rw [←longSL_center_eq_bot]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := longSLHom_surjective y
    have hh := hc x x.property
    rw [he',local₂_pCoreIn] at hh
    have hk : g'*x*g'⁻¹/x ∈ (longSLHom (F := F)).ker := by
      rw [longSLHom_ker]
      exact hh
    have hq := MonoidHom.mem_ker.mp hk
    rw [map_div,div_eq_one,map_mul,map_mul,map_inv] at hq
    exact (mul_inv_eq_iff_eq_mul.mp hq).symm
  have hg1 : g=1 := by
    let u : pCore 2 (local₂ (F := F)) := ⟨g',hgc⟩
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := local₂ (F := F))).exists_card_eq
    have hu : u=1 := by
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right k)
        (orderOf_dvd_of_pow_eq_one (show u^r=1 from Subtype.ext (Subtype.ext hgr)))
      exact hk ▸ orderOf_dvd_natCard u
    exact congrArg (fun v : pCore 2 (local₂ (F := F)) => v.val.val) hu
  obtain ⟨c,hscalar⟩ := normalizer_scalar_factor F t 1 1 (by
    simpa only [hg1,map_one,mul_one] using he')
  have hs (v : Natural.Space F) : t.val.val v = c • v := by
    have hh := hscalar v
    have hf (w : Natural.Space F) : Natural.BinarySemilinear.fieldEquivalence F (1 : F ≃+* F) w=w := by
      apply (Natural.BinarySemilinear.coordinatesEquiv F).injective
      exact (Natural.BinarySemilinear.coordinatesEquiv F).apply_symm_apply _
    simpa only [hf,map_one,Module.End.one_apply] using hh
  have hc1 : c=1 := by
    have hh := hs (Natural.mk F (firstVector (F := F)))
    rw [hfix] at hh
    exact (smul_left_injective _ first_ne_zero) (hh.symm.trans (one_smul F _).symm)
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  change t.val.val v = v
  simpa only [hc1,one_smul] using hs v

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.G2Action

