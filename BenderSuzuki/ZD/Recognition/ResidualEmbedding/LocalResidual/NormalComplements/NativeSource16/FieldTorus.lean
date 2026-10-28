module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.FixedCircle

/-!
# The literal residual torus and its field action

The marked Sylow normalizer identifies the model two-point torus with
D∩F°. Its cyclic order and inversion transport through the injective circle
map. The actual fixed-group model rules out an inner marked action: such
an action would be trivial, forcing the positive field degree to equal
half itself. Consequently the marked automorphism is square-root Frobenius
on the original ambient torus.

Source: GLS IV, Chapter 2, Proposition 16.5, construction of R₀=Oₚ(D∩B°).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem fieldTorus_twoPoint_comap {C : Type*} [Group C] (f : C →* G)
    (M : Subgroup G) (t : C) :
    twoPoint (M.comap f) t = (residualPairStabilizer M (f t)).comap f := by
  ext x
  simp only [twoPoint,residualPairStabilizer,mem_inf,mem_comap]
  apply and_congr_right
  intro _
  change x ∈ (M.comap f).map (MulAut.conj t⁻¹).toMonoidHom ↔
    f x ∈ M.map (MulAut.conj (f t)⁻¹).toMonoidHom
  rw [map_equiv_eq_comap_symm',map_equiv_eq_comap_symm']
  change f ((MulAut.conj t⁻¹).symm x) ∈ M ↔ (MulAut.conj (f t)⁻¹).symm (f x) ∈ M
  rw [MulAut.conj_symm_apply,MulAut.conj_symm_apply,inv_inv,inv_inv,map_mul,map_mul,map_inv]

/-- The first and second field circles give literal ambient tori with the
orders and actions used to construct the nontrivial odd p-core. -/
public theorem source16_field_torus_geometry
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    {z t : G} (hz : z ∈ Z) (hzF : z ∈ F) (hzM : z ∈ M)
    (ht : t ∈ Z) (htF : t ∈ F) (htM : t ∉ M)
    (hns : ¬ Group.IsSolvable (localCircle Z F))
    (v : F) (hv : PFAppendixIII.IsInvolution (v : G)) (hvM : (v : G) ∈ M)
    (hzv : Commute z (v : G)) (htv : Commute t (v : G))
    {m : ℕ} (hm : 0 < m) (e : localCircle Z F ≃* PSL2BinaryMatrixGroup (2 * m))
    (ef : (source16_circleAction h.disconnected F hFM hne v).fixedSubgroup ≃*
      PSL2BinaryMatrixGroup m) :
    let a := source16_circleAction h.disconnected F hFM hne v
    a ^ 2 = 1 ∧ (¬ ∃ g, a = MulAut.conj g) ∧
    let D₀ := residualPairStabilizer M t ⊓ localCircleIn Z F
    IsCyclic D₀ ∧ Nat.card D₀ = 2 ^ (2 * m) - 1 ∧
      (∀ x ∈ D₀, t * x * t⁻¹ = x⁻¹) ∧
      (∀ x ∈ D₀, (v : G) * x * (v : G)⁻¹ = x ^ (2 ^ m)) := by
  let C := localCircle Z F
  let f := localCircleHom Z F
  let a := source16_circleAction h.disconnected F hFM hne v
  have hav (x : C) : f (a x) = (v : G) * f x * (v : G)⁻¹ := rfl
  have ha2 : a ^ 2 = 1 := by
    change (source16_circleAction h.disconnected F hFM hne v) ^ 2 = 1
    rw [← map_pow, show v ^ 2 = 1 from Subtype.ext hv.sq_eq_one,map_one]
  have ha1 : a ≠ 1 := by
    intro he
    have htop : a.fixedSubgroup = ⊤ := by
      ext x
      simp only [MulAut.mem_fixedSubgroup,he,MulAut.one_apply,mem_top,iff_self]
    let f0 : a.fixedSubgroup ≃* C := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hh := source16_binary_parameter_eq hm (by omega : 0 < 2 * m)
      (ef.symm.trans (f0.trans e))
    omega
  obtain ⟨P,hP,hmark⟩ := localCircle_exists_marked_sylow h r ha F hF hFM hne hns
  let zC : C := ⟨⟨z,hzF⟩,subset_closure hz⟩
  let tC : C := ⟨⟨t,htF⟩,subset_closure ht⟩
  have hzC : PFAppendixIII.IsInvolution zC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions z hz) hzF) _
  have htC : PFAppendixIII.IsInvolution tC :=
    IsInvolution.subtype (IsInvolution.subtype (h.disconnected.involutions t ht) htF) _
  have htNP : tC ∉ normalizer (P : Set C) := by rw [← hP]; exact htM
  have haz : a zC = zC := (localCircleHom_injective Z F)
    (by rw [hav]; exact mul_inv_eq_iff_eq_mul.mpr hzv.symm.eq)
  have hat : a tC = tC := (localCircleHom_injective Z F)
    (by rw [hav]; exact mul_inv_eq_iff_eq_mul.mpr htv.symm.eq)
  have houter : ¬ ∃ g : C, a = MulAut.conj g := fun hi =>
    ha1 (LinearGeometry.inner_fixing_eq_one e P hzC (hmark zC hz hzM) htNP a hi haz hat)
  have haNP : (normalizer (P : Set C)).map a.toMonoidHom = normalizer (P : Set C) := by
    rw [← hP]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change f (a x) ∈ M
      rw [hav]
      exact M.mul_mem (M.mul_mem hvM hx) (M.inv_mem hvM)
    · intro x hx
      refine ⟨a x,?_,?_⟩
      · change f (a x) ∈ M
        rw [hav]
        exact M.mul_mem (M.mul_mem hvM hx) (M.inv_mem hvM)
      · change a (a x) = x
        have hh := DFunLike.congr_fun ha2 x
        simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using hh
  obtain ⟨m',_,hmm,_,hpower,_⟩ := linear_outer_marked_fixed_and_pCore (by omega) e P tC
    htC htNP a ha2 houter haNP hat
  have heqm : m' = m := by omega
  subst m'
  let D := twoPoint (normalizer (P : Set C)) tC
  have hmap : D.map f = residualPairStabilizer M t ⊓ localCircleIn Z F := by
    dsimp only [D]
    rw [← hP,fieldTorus_twoPoint_comap,map_comap_eq]
    have hf : f.range = localCircleIn Z F := by
      change (localCircleHom Z F).range = _
      rw [localCircleHom,MonoidHom.range_comp,(localCircle Z F).range_subtype]
      rfl
    rw [hf]
    exact inf_comm _ _
  obtain ⟨hcyc,hcard⟩ := LinearGeometry.twoPoint_cyclic_card (by omega) e P htC htNP
  refine ⟨ha2,houter,?_,?_,?_,?_⟩
  · let : IsCyclic D := hcyc
    rw [← hmap]
    exact isCyclic_of_surjective (f.subgroupMap D) (f.subgroupMap_surjective D)
  · rw [← hmap,card_map_of_injective (localCircleHom_injective Z F)]
    exact hcard
  · intro x hx
    rw [← hmap] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := congrArg f (LinearGeometry.twoPoint_inverted e P htC htNP hy)
    change f (tC⁻¹ * y * tC) = f y⁻¹ at hh
    simpa only [map_mul,map_inv,show f tC = t from rfl,(h.disconnected.involutions t ht).inv_eq_self]
      using hh
  · intro x hx
    rw [← hmap] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := congrArg f (hpower y hy)
    rw [hav,map_pow] at hh
    exact hh

end BenderSuzuki.ZD
