module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Suzuki.PairAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Orthogonal.OriginalPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Rows
public import Theory.Representation.Suzuki.FixedLineAction

/-!
# Triviality of the original central Hall action in the Suzuki row

Field linearity makes both literal component actions inner. Section-kernel
coprimality then places the original Hall group in L₀. A nonzero vector fixed
by the Sylow component stabilizer is fixed by the Hall group in both exchanged
moved factors. Each projection of the original Sylow quotient is Sylow in the
Suzuki model. The natural-module stabilizer calculation therefore kills both
odd Hall projections, hence the original quotient action.

This proves `SuzukiActionTrivialAt` without further action premises.
The earlier seed and module-recognition inputs remain with the central Hall
assembly, qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith 10.1.2(5), 10.2.3, printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_suzukiActionTrivialAt (T : Sylow 2 G) : SuzukiActionTrivialAt T := by
  intro L D H B c geometry m hm e d
  let R := localOrbit T L
  let J := SuzukiMatrixGroup m
  have hBR := suzuki_hall_le_orbit D c geometry m hm e d
  let j : B →* R := (H.subtype.comp B.subtype).codRestrict R
    (fun b => hBR (mem_map_of_mem H.subtype b.property))
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let : IsSimpleGroup J := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  obtain ⟨f,hf,hk,hfirst,hsecond⟩ := marked_pair_projection D e c.nonnormal ht htn
  let q : (R ⧸ pCore 2 R) ≃* (J × J) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  let Sq := S.mapSurjective hf
  let P₁ := Sq.mapSurjective (f := MonoidHom.fst J J) (fun x => ⟨(x,1),rfl⟩)
  let P₂ := Sq.mapSurjective (f := MonoidHom.snd J J) (fun x => ⟨(1,x),rfl⟩)
  obtain ⟨w,hw,hwS,hwB⟩ := exists_moved_fixed_pair D c geometry d
    (by
      intro v hv
      apply SuzukiNatural.natural_fixed_eq_zero m v
      intro g
      obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
      exact hv l) ht htn
  let v := (d.coordinates w).toAdd
  have hv : v ≠ 0 := hw
  let τ := R.normalizerMonoidHom
    ⟨t⁻¹,le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht)⟩
  have hτ (r : R) : (f (τ r)).1 = (f r).2 :=
    pair_projection_conj_inv_fst D c e ht htn f hfirst hsecond r
  have hfix (r : R) (hr : Commute (r : G) (w : G)) :
      SuzukiNatural.natural m (f r).1 v = v := by
    have he := moved_pair_action D c geometry e (SuzukiNatural.natural m) d
      ht htn f hfirst hsecond r w
    rw [←he]
    apply congrArg Multiplicative.toAdd
    congr 1
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hr.eq
  have hfix₂ (r : R) (hr : Commute (τ r : G) (w : G)) :
      SuzukiNatural.natural m (f r).2 v = v := by
    rw [←hτ]
    exact hfix (τ r) hr
  have hP₁ : ∀ g ∈ P₁, SuzukiNatural.natural m g v = v := by
    intro g hg
    change g ∈ (Sq : Subgroup (J × J)).map (MonoidHom.fst J J) at hg
    obtain ⟨x,hx,rfl⟩ := hg
    change x ∈ (S : Subgroup R).map f at hx
    obtain ⟨r,hr,rfl⟩ := hx
    have hrS : (r : G) ∈ (T : Subgroup G) ⊓ normalizer (L : Set G) :=
      ⟨(by change r ∈ (T : Subgroup G).subgroupOf R; rwa [←hS]),
        source_nonnormal_orbit_le_normalizer D c.nonnormal r.property⟩
    exact hfix r (hwS r hrS)
  have hP₂ : ∀ g ∈ P₂, SuzukiNatural.natural m g v = v := by
    intro g hg
    change g ∈ (Sq : Subgroup (J × J)).map (MonoidHom.snd J J) at hg
    obtain ⟨x,hx,rfl⟩ := hg
    change x ∈ (S : Subgroup R).map f at hx
    obtain ⟨r,hr,rfl⟩ := hx
    have hrT : (r : G) ∈ (T : Subgroup G) := by
      change r ∈ (T : Subgroup G).subgroupOf R
      rwa [←hS]
    have hrS : (τ r : G) ∈ (T : Subgroup G) ⊓ normalizer (L : Set G) :=
      ⟨by
        change t⁻¹*(r : G)*(t⁻¹)⁻¹ ∈ (T : Subgroup G)
        rw [inv_inv]
        exact (T : Subgroup G).mul_mem
          ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) hrT) ht,
        source_nonnormal_orbit_le_normalizer D c.nonnormal (τ r).property⟩
    exact hfix₂ r (hwS (τ r) hrS)
  apply MonoidHom.ext
  intro b
  have ho₁ : Odd (orderOf (f (j b)).1) := (hall_odd D c).of_dvd_nat
    ((orderOf_map_dvd ((MonoidHom.fst J J).comp (f.comp j)) b).trans
      (orderOf_dvd_natCard b))
  have ho₂ : Odd (orderOf (f (j b)).2) := (hall_odd D c).of_dvd_nat
    ((orderOf_map_dvd ((MonoidHom.snd J J).comp (f.comp j)) b).trans
      (orderOf_dvd_natCard b))
  have h₁ : (f (j b)).1 = 1 := SuzukiNatural.odd_eq_one_of_fixes_sylow_fixed
    m hm P₁ _ ho₁ v hv hP₁ (hfix (j b) (hwB b).1)
  have h₂ : (f (j b)).2 = 1 := by
    apply SuzukiNatural.odd_eq_one_of_fixes_sylow_fixed m hm P₂ _ ho₂ v hv hP₂
    apply hfix₂
    have hh := congrArg (MulAut.conj t⁻¹) (hwB b).2.eq
    change (t⁻¹*(b : G)*(t⁻¹)⁻¹)*(w : G) = (w : G)*(t⁻¹*(b : G)*(t⁻¹)⁻¹)
    simpa only [map_mul,MulAut.conj_apply,inv_inv,mul_assoc,
      mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel_right,
      mul_inv_cancel,inv_mul_cancel,one_mul,mul_one] using hh
  have hq : QuotientGroup.mk' (pCore 2 R) (j b) = 1 := by
    apply q.injective
    exact (Prod.ext h₁ h₂).trans q.map_one.symm
  have he : action D B c.hall_le b = MulAut.conj
      (QuotientGroup.mk' (pCore 2 R) (j b)) :=
    normalizerPCoreQuotientAction_inner R (j b)
  rw [he,hq,map_one]
  rfl
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
