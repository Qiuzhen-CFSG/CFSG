module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Orthogonal.FieldAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldKernel

/-!
# Innerness of the original orthogonal Hall action

The fixed-vector argument eliminates the field action on the first component.
Conjugating the original Hall actor by an element of the Sylow subgroup gives
an odd-order actor on the first component again, so the same argument also
eliminates the field action on its conjugate component. The literal marked
pair quotient then makes the entire Hall action inner.

The existing coefficient-kernel identification now places the original Hall
subgroup in the component orbit. This discharges the field-factor step in the
orthogonal row; the norm-one diagonal constraints remain a separate step.
Source: Aschbacher--Smith, 10.2.3, centralizing-Z branch, printed p.745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
local instance pairFieldBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance pairFieldBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- The original Hall actor is inner on the actual two-component quotient. -/
theorem orthogonal_hall_action_inner
    (geometry : ModuleGeometry D) (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) (b : B) :
    action D B c.hall_le b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L)) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let M := D.maximalLocal
  let N := (normalizer (L : Set G)).subgroupOf M
  have htM : t ∈ M := le_normalizer_componentOrbit L T ht
  have hbM : (b : G) ∈ M := c.hall_le b.property
  have hi : N.index = 2 := normalizer_relIndex_eq_two_of_pair M L
    (L.map (MulAut.conj t).toMonoidHom)
    (source_nonnormal_maximal_pair D c.nonnormal ht htn) t htM
    (fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he))
  let : N.Normal := normal_of_index_eq_two hi
  let x : G := t⁻¹*(b : G)*t
  have hxM : x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem htM) hbM) htM
  have hxH : x ∈ H := H.mul_mem
    (H.mul_mem (H.inv_mem (c.hstar.1.1.2 ht)) b.val.property) (c.hstar.1.1.2 ht)
  have hxL : x ∈ normalizer (L : Set G) := by
    have hbN : (⟨b,hbM⟩ : M) ∈ N := hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)
    have hh := (inferInstance : N.Normal).conj_mem _ hbN (⟨t,htM⟩ : M)⁻¹
    change t⁻¹*(b : G)*(t⁻¹)⁻¹ ∈ normalizer (L : Set G) at hh
    simpa only [inv_inv] using hh
  have hxo : Odd (orderOf x) := by
    have he := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom
      (MulAut.conj t⁻¹).injective (b : G)
    have ho : Odd (orderOf (b : G)) := by
      have hb := (hall_odd D c).of_dvd_nat (orderOf_dvd_natCard b)
      rwa [←orderOf_injective (H.subtype.comp B.subtype)
        (H.subtype_injective.comp B.subtype_injective) b] at hb
    have ho' : Odd (orderOf ((MulAut.conj t⁻¹).toMonoidHom (b : G))) := he.symm ▸ ho
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using ho'
  obtain ⟨a,ha⟩ := orthogonal_hall_component_inner D c geometry n e d b
  obtain ⟨a',ha'⟩ := orthogonal_odd_component_inner D c geometry n e d x hxH hxM hxL hxo
  let R := localOrbit T L
  let S := Matrix.SpecialLinearGroup (Fin 2) (Field n)
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : IsSimpleGroup S :=
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := Field n))).trans
        QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨f,hf,hk,hfirst,hsecond⟩ := marked_pair_projection D e c.nonnormal ht htn
  let q : (R ⧸ pCore 2 R) ≃* (S × S) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hq (r : R) : q (QuotientGroup.mk' (pCore 2 R) r) = f r := rfl
  let α := MulAut.congr q (action D B c.hall_le b)
  have hα (r : R) : α (f r) =
      f (R.normalizerMonoidHom ⟨b,hbM⟩ r) := by
    rw [←hq]
    change q (action D B c.hall_le b (q.symm (q (QuotientGroup.mk' (pCore 2 R) r)))) = _
    rw [q.symm_apply_apply]
    change q (quotientAut (pCore 2 R) _ _) = _
    rw [quotientAut_apply_mk,hq]
    rfl
  have h1 (z : S) : α (z,1) = (e a * z * (e a)⁻¹,1) := by
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) z
    change α (e (QuotientGroup.mk' (pCore 2 L) l),1) = _
    rw [←hfirst,hα]
    let l' := L.normalizerMonoidHom ⟨b,hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)⟩ l
    have he : R.normalizerMonoidHom ⟨b,hbM⟩
      ⟨l,le_componentOrbit L T l.property⟩ = ⟨l',le_componentOrbit L T l'.property⟩ := rfl
    rw [he,hfirst]
    congr 1
    have hh := MulEquiv.congr_fun ha (QuotientGroup.mk' (pCore 2 L) l)
    change _ = quotientAut (pCore 2 L) _ _ at hh
    rw [quotientAut_apply_mk] at hh
    exact (congrArg e hh).symm.trans
      ((e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _) (e.map_inv _)))
  have h2 (z : S) : α (1,z) = (1,e a' * z * (e a')⁻¹) := by
    obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) z
    change α (1,e (QuotientGroup.mk' (pCore 2 L) l)) = _
    rw [←hsecond,hα]
    let l' := L.normalizerMonoidHom ⟨x,hxL⟩ l
    have he : R.normalizerMonoidHom ⟨b,hbM⟩ (originalConjugateOrbitInclusion ht l) =
        originalConjugateOrbitInclusion ht l' := by
      apply Subtype.ext
      change (b : G)*(t*(l : G)*t⁻¹)*(b : G)⁻¹ = t*(x*(l : G)*x⁻¹)*t⁻¹
      dsimp [x]
      group
    rw [he,hsecond]
    congr 1
    have hh := MulEquiv.congr_fun ha' (QuotientGroup.mk' (pCore 2 L) l)
    change _ = quotientAut (pCore 2 L) _ _ at hh
    rw [quotientAut_apply_mk] at hh
    exact (congrArg e hh).symm.trans
      ((e.map_mul _ _).trans (congrArg₂ (· * ·) (e.map_mul _ _) (e.map_inv _)))
  have he : α = MulAut.conj (e a,e a') := by
    apply MulEquiv.ext
    intro z
    have hz : z = (z.1,1)*(1,z.2) := by simp
    rw [hz,map_mul,h1,h2]
    simp only [Prod.mk_mul_mk,one_mul,mul_one,MulAut.conj_apply,Prod.inv_mk]
  refine ⟨q.symm (e a,e a'),?_⟩
  apply (MulAut.congr q).injective
  rw [MulAut.congr_conj,q.apply_symm_apply]
  exact he.symm
include D c in
/-- In the orthogonal row the literal Hall group lies in the original
component orbit: both field factors have been eliminated. -/
theorem orthogonal_hall_le_orbit
    (geometry : ModuleGeometry D) (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    B.map H.subtype ≤ localOrbit T L := by
  obtain ⟨e',q,φ,χ,_hcomp,_hS,_ho,hk,_hi,_hexp,_hact,hd⟩ :=
    exists_hall_field_kernel_coordinates D c e
  let ρ := (MulAut.congr q).toMonoidHom.comp (action D B c.hall_le)
  have hd' : ∀ b, ∃ z : (Field n)ˣ × (Field n)ˣ, ρ b =
      (MulAut.conj (Matrix.SpecialLinearGroup.splitDiagonalHom z.1) *
        BenderSuzuki.ZD.Linear.sl2FieldAut (φ b).1).prodCongr
      (MulAut.conj (Matrix.SpecialLinearGroup.splitDiagonalHom z.2) *
        BenderSuzuki.ZD.Linear.sl2FieldAut (φ b).2) := by
    intro b
    obtain ⟨z,hz⟩ := hd b
    refine ⟨z,?_⟩
    change MulAut.congr q (action D B c.hall_le b) = _
    simpa only [Matrix.SpecialLinearGroup.splitDiagonalHom_apply] using hz
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro b
    have hm := orthogonal_hall_action_inner D c geometry n e d b
    have hm' : MulAut.congr q (action D B c.hall_le b) ∈
        MulAut.innerSubgroup (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
          Matrix.SpecialLinearGroup (Fin 2) (Field n)) := by
      rw [←MulAut.map_innerSubgroup_congr q]
      exact mem_map_of_mem _ hm
    exact (Matrix.SpecialLinearGroup.pair_diagonal_field_inner_iff
      ρ φ hd' b).mpr hm'
  rintro _ ⟨b,hb,rfl⟩
  have hh : (⟨b,hb⟩ : B) ∈ φ.ker := by simp [hφ]
  rw [hk] at hh
  exact hh
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
