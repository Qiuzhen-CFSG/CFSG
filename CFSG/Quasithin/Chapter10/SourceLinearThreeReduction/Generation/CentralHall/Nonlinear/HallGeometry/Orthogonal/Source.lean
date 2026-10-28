module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Orthogonal.OriginalPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Transport
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Rows
public import Theory.Representation.OrthogonalFourMinusRankOne.RootFixer

/-!
# Compatible norm-one coordinates for the original orthogonal Hall subgroup

After the field factors have been eliminated, the original Hall subgroup lies
in the component orbit and normalizes its Sylow two-subgroup. One pair of inner
conjugators simultaneously marks that Sylow by upper root groups and the whole
Hall subgroup by diagonal matrices. The actual moved module has a nonzero vector
fixed by the Sylow component stabilizer. The central diagonal argument fixes
both that vector and its exchanged partner under the Hall subgroup. In the
common matrix marking the two vectors lie on the respective upper singular
lines, forcing both diagonal parameters to have norm one.

This proves the entire orthogonal row, retaining the original quotient action.
The natural/Suzuki rows and the earlier module recognition remain with
qt-d-10-nona5-central-hall-orders; qt-d-10-nona5-generation-cap discharges the
original Hall faithfulness premise in the final source theorem.
Source: Aschbacher--Smith 10.1.2(5) and 10.2.3, printed pp.742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
local instance normOneBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance normOneBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

private theorem conjugated_fixes {A K V : Type*} [Group A] [Semiring K]
    [AddCommMonoid V] [Module K V] (ρ : Representation K A V)
    (a g : A) (v : V) (h : ρ g v = v) :
    ρ (a*g*a⁻¹) (ρ a v) = ρ a v := by
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  rw [map_mul,Module.End.mul_apply,h]

/-- The source orthogonal row has the required common pair marking and both
literal singular-vector equations. -/
theorem source_orthogonalDiagonalAt (T : Sylow 2 G) : OrthogonalDiagonalAt T := by
  intro L D H B c geometry n hn _hlarge e d
  let R := localOrbit T L
  let J := Matrix.SpecialLinearGroup (Fin 2) (Field n)
  let W : Subgroup G := ⁅D.fullModule,L⁆
  have hBR := orthogonal_hall_le_orbit D c geometry n e d
  let j : B →* R := (H.subtype.comp B.subtype).codRestrict R
    (fun b => hBR (mem_map_of_mem H.subtype b.property))
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let := D.quasisimple
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : IsSimpleGroup J :=
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := Field n))).trans
        QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨f,hf,hk,hfirst,hsecond⟩ := marked_pair_projection D e c.nonnormal ht htn
  let q₀ : (R ⧸ pCore 2 R) ≃* (J × J) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  let Sq := S.mapSurjective hf
  let C := j.range
  have hCN : C ≤ normalizer (S : Set R) := by
    rintro _ ⟨b,rfl⟩
    rw [←source_orbit_sylow_normalizer_eq S hS]
    exact ⟨(j b).property,hall_normalizes_orbit_sylow D c e
      (mem_map_of_mem H.subtype b.property)⟩
  have hCq : C.map f ≤ normalizer (Sq : Set (J × J)) :=
    (map_mono hCN).trans (le_normalizer_map f)
  obtain ⟨a₁,a₂,χ,hSq,hχ⟩ := pair_sylow_odd_subgroup_diagonal_coordinates Sq
    (C.map f) hCq ((hall_odd D c).of_dvd_nat
      ((C.card_map_dvd f).trans (card_range_dvd j)))
  let a := (MulAut.conj a₁).prodCongr (MulAut.conj a₂)
  let q := q₀.trans a
  let e' := e.trans (MulAut.conj a₁)
  let k : B →* C.map f := (f.comp j).codRestrict _ (fun b =>
    mem_map_of_mem f (show j b ∈ C from ⟨b,rfl⟩))
  let δ := χ.comp k
  have hdiag (b : B) : a (f (j b)) =
      (CartanFixed.diagonal n (δ b).1,CartanFixed.diagonal n (δ b).2) := hχ (k b)
  have hq (r : R) : q (QuotientGroup.mk' (pCore 2 R) r) = a (f r) := rfl
  have hnV : Nontrivial (Space n) := (coordinates n).nontrivial
  let := hnV
  obtain ⟨w,hw,hwS,hwB⟩ := exists_moved_fixed_pair D c geometry d
    (by
      intro v hv
      apply SL2.BinarySmall.hermitian_fixed_eq_zero n v
      intro g
      obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
      exact hv l) ht htn
  let v := (d.coordinates w).toAdd
  have hv : v ≠ 0 := hw
  let τ := R.normalizerMonoidHom
    ⟨t⁻¹,le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem ht)⟩
  have hτ (r : R) : (f (τ r)).1 = (f r).2 :=
    pair_projection_conj_inv_fst D c e ht htn f hfirst hsecond r
  have hfix (r : R) (hr : Commute (r : G) (w : G)) : FiniteModel.action n (f r).1 v = v := by
    have he := moved_pair_action D c geometry e (SL2.BinarySmall.hermitian n) d
      ht htn f hfirst hsecond r w
    change _ = FiniteModel.action n (f r).1 v at he
    rw [←he]
    apply congrArg Multiplicative.toAdd
    congr 1
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hr.eq
  have hfix₂ (r : R) (hr : Commute (τ r : G) (w : G)) : FiniteModel.action n (f r).2 v = v := by
    rw [←hτ]
    exact hfix (τ r) hr
  have hv₁ : FiniteModel.action n a₁ v ≠ 0 := by
    intro he
    have hh := congrArg (FiniteModel.action n a₁⁻¹) he
    simp only [map_zero,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] at hh
    exact hv hh
  have hv₂ : FiniteModel.action n a₂ v ≠ 0 := by
    intro he
    have hh := congrArg (FiniteModel.action n a₂⁻¹) he
    simp only [map_zero,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] at hh
    exact hv hh
  have hU₁ : ∀ g : upperUnipotent (Field n), FiniteModel.action n g (FiniteModel.action n a₁ v) = FiniteModel.action n a₁ v := by
    intro g
    have hm : (g.val,1) ∈ (S : Subgroup R).map (a.toMonoidHom.comp f) := by
      rw [←Subgroup.map_map]
      change (g.val,1) ∈ (Sq : Subgroup (J × J)).map a.toMonoidHom
      rw [hSq]
      exact ⟨g.property,one_mem _⟩
    obtain ⟨r,hr,he⟩ := hm
    have hrS : (r : G) ∈ (T : Subgroup G) ⊓ normalizer (L : Set G) :=
      ⟨(by change r ∈ (T : Subgroup G).subgroupOf R; rwa [←hS]),source_nonnormal_orbit_le_normalizer D c.nonnormal r.property⟩
    have hc := hwS r hrS
    have hg : a₁*(f r).1*a₁⁻¹ = g := congrArg Prod.fst he
    rw [←hg]
    exact conjugated_fixes (FiniteModel.action n) a₁ (f r).1 v (hfix r hc)
  have hU₂ : ∀ g : upperUnipotent (Field n), FiniteModel.action n g (FiniteModel.action n a₂ v) = FiniteModel.action n a₂ v := by
    intro g
    have hm : (1,g.val) ∈ (S : Subgroup R).map (a.toMonoidHom.comp f) := by
      rw [←Subgroup.map_map]
      change (1,g.val) ∈ (Sq : Subgroup (J × J)).map a.toMonoidHom
      rw [hSq]
      exact ⟨one_mem _,g.property⟩
    obtain ⟨r,hr,he⟩ := hm
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
    have hc := hwS (τ r) hrS
    have hg : a₂*(f r).2*a₂⁻¹ = g := congrArg Prod.snd he
    rw [←hg]
    exact conjugated_fixes (FiniteModel.action n) a₂ (f r).2 v (hfix₂ r hc)
  refine ⟨e',q,?_,fun b => ⟨δ b,?_,?_,?_⟩⟩
  · intro l
    rw [hq,hfirst]
    change (a₁*e (QuotientGroup.mk' (pCore 2 L) l)*a₁⁻¹,a₂*1*a₂⁻¹) = _
    simp only [mul_one,mul_inv_cancel]
    rfl
  · intro x
    have he : action D B c.hall_le b =
        MulAut.conj (QuotientGroup.mk' (pCore 2 R) (j b)) :=
      normalizerPCoreQuotientAction_inner R (j b)
    rw [he]
    change q (_ * x * _⁻¹) = _
    rw [map_mul,map_mul,map_inv,hq,hdiag]
  · apply CartanFixed.fixes_rootVector_of_nonzero_upper_fixed n (δ b).1
      (FiniteModel.action n a₁ v) hv₁ hU₁
    have he : a₁*(f (j b)).1*a₁⁻¹ = CartanFixed.diagonal n (δ b).1 :=
      congrArg Prod.fst (hdiag b)
    rw [←he]
    exact conjugated_fixes (FiniteModel.action n) a₁ (f (j b)).1 v (hfix (j b) (hwB b).1)
  · apply CartanFixed.fixes_rootVector_of_nonzero_upper_fixed n (δ b).2
      (FiniteModel.action n a₂ v) hv₂ hU₂
    have he : a₂*(f (j b)).2*a₂⁻¹ = CartanFixed.diagonal n (δ b).2 :=
      congrArg Prod.snd (hdiag b)
    rw [←he]
    apply conjugated_fixes (FiniteModel.action n) a₂ (f (j b)).2 v
    apply hfix₂
    have hh := congrArg (MulAut.conj t⁻¹) (hwB b).2.eq
    change (t⁻¹*(b : G)*(t⁻¹)⁻¹)*(w : G) = (w : G)*(t⁻¹*(b : G)*(t⁻¹)⁻¹)
    simpa only [map_mul,MulAut.conj_apply,inv_inv,mul_assoc,
      mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel_right,
      mul_inv_cancel,inv_mul_cancel,one_mul,mul_one] using hh

include c in
/-- The completed orthogonal geometry gives the exact exponent bound on the
original Hall carrier, using its permitted section-faithfulness hypothesis. -/
theorem orthogonal_hall_exponent_dvd
    (geometry : ModuleGeometry D) (n : ℕ) [NeZero n] (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Monoid.exponent B ∣ 2^n+1 := by
  obtain ⟨e',q,hq,hdiag⟩ := source_orthogonalDiagonalAt T L D H B c geometry n
    inferInstance hn e d
  obtain ⟨p⟩ := cartanCoordinates_of_pointwise D B c.hall_le n e' q hq hdiag
  obtain ⟨f,hf⟩ := p.image_embedding c.faithful
  exact exponent_dvd_of_image_embedding D B c.hall_le c.faithful n f hf

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
