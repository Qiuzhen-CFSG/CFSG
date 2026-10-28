module

public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Generation by a full Sylow and a root-Sylow subgroup

A finite group with nonnormal Sylow two-subgroup and two-group kernel,
whose Sylow image lies in the first long root of Sp₄, generates all Sp₄
with the standard unipotent group. A proper generated subgroup would have
an orthogonal point orbit. Its root conjugates would commute, making their
normal closure elementary abelian. Pulling it back would make the original
Sylow normal, contradicting the hypothesis.

This is the normalizer-generation input used in MS93 (5.1), printed p.913.
The quotient map and its entire two-group kernel remain explicit.
-/

public section
open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem first_root_formula (s : F) (v : Vector F) :
    rootElement 0 s • v = v + (s * form F (e 0) v) • e 0 := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootElement,rootMatrix,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,Matrix.single,
      Matrix.one_apply,form_apply,e]

omit [CharP F 2] in
private theorem conjugate_first_root_formula (g : Sp F) (s : F) (v : Vector F) :
    (g * rootElement 0 s * g⁻¹) • v =
      v + (s * form F (g • e 0) v) • (g • e 0) := by
  have hp : form F (e 0) (g⁻¹ • v) = form F (g • e 0) v := by
    simpa only [smul_inv_smul] using (preserves_form g (e 0) (g⁻¹ • v)).symm
  rw [mul_smul,mul_smul,first_root_formula]
  change toLinear g _ = _
  rw [map_add,(toLinear g).map_smul]
  change g • (g⁻¹ • v) + (s * form F (e 0) (g⁻¹ • v)) • (g • e 0) = _
  rw [smul_inv_smul,hp]

omit [CharP F 2] in
private theorem first_root_commutes_conjugate (g : Sp F)
    (ho : form F (e 0) (g • e 0) = 0) (s t : F) :
    Commute (rootElement 0 s) (g * rootElement 0 t * g⁻¹) := by
  have hr : form F (g • e 0) (e 0) = 0 := TwoLocalCover.form_alternating.eq_iff.mp ho
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  change (rootElement 0 s * (g * rootElement 0 t * g⁻¹)) • v =
    ((g * rootElement 0 t * g⁻¹) * rootElement 0 s) • v
  rw [mul_smul (rootElement 0 s),mul_smul (g * rootElement 0 t * g⁻¹),
    conjugate_first_root_formula,first_root_formula,
    first_root_formula,conjugate_first_root_formula]
  simp only [map_add,map_smul,
    smul_eq_mul,ho,hr,mul_zero,add_zero]
  abel

/-- A subgroup with a nonnormal Sylow mapping into the first long root
must generate the full symplectic group with the standard Sylow. -/
theorem unipotent_sup_range_eq_top_of_root_sylow
    {G : Type*} [Group G] [Finite G]
    (q : G →* Sp F) (hk : IsPGroup 2 q.ker) (P : Sylow 2 G)
    (hP : (P : Subgroup G).map q ≤ RootSubgroup.group 0)
    (hn : ¬ (P : Subgroup G).Normal) : unipotent ⊔ q.range = ⊤ := by
  by_contra hproper
  let A := unipotent ⊔ q.range
  have ho := ThreeResidualPlacement.orthogonal_point_orbit_of_proper_unipotent_overgroup
    A le_sup_left hproper
  let f := q.rangeRestrict
  let V := (P : Subgroup G).map f
  let W := normalClosure (V : Set q.range)
  have hc : W ≤ centralizer (V : Set q.range) := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨v,hv,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hconj
    intro y hy
    obtain ⟨a,ha,rfl⟩ := hv
    obtain ⟨b,hb,rfl⟩ := hy
    obtain ⟨s,hs⟩ := (RootSubgroup.mem_group_iff 0 _).mp (hP (mem_map_of_mem q ha))
    obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 _).mp (hP (mem_map_of_mem q hb))
    apply Subtype.ext
    change q b * (g.val * q a * g.val⁻¹) = (g.val * q a * g.val⁻¹) * q b
    rw [←hs,←ht]
    exact first_root_commutes_conjugate g.val (ho g.val (mem_sup_right g.property)) t s
  have hVW : V ≤ centralizer (W : Set q.range) := le_centralizer_iff.mp hc
  have hWW : W ≤ centralizer (W : Set q.range) := normalClosure_le_normal hVW
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp hWW
  have hWe : IsElementaryAbelian 2 W := by
    let : IsMulCommutative (closure (Group.conjugatesOfSet (V : Set q.range))) := inferInstanceAs (IsMulCommutative W)
    apply IsElementaryAbelian.closure_of_isMulCommutative
    intro x hx
    obtain ⟨v,hv,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hconj
    rw [conj_pow]
    have hv2 : v^2=1 := by
      obtain ⟨a,ha,rfl⟩ := hv
      obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 _).mp (hP (mem_map_of_mem q ha))
      apply Subtype.ext
      change (q a)^2=1
      rw [←ht,pow_two,RootSubgroup.element_add,CharTwo.add_self_eq_zero,RootSubgroup.element_zero]
    rw [hv2,mul_one,mul_inv_cancel]
  let := hWe
  have hfk : f.ker = q.ker := by
    ext x
    change f x=1 ↔ q x=1
    exact Subtype.ext_iff
  have hrp : IsPGroup 2 (W.comap f) :=
    (IsElementaryAbelian.isPGroup 2 W).comap_of_ker_isPGroup f (hfk ▸ hk)
  have he : W.comap f = (P : Subgroup G) := P.is_maximal' hrp (by
    intro x hx
    exact le_normalClosure (mem_map_of_mem f hx))
  apply hn
  rw [←he]
  infer_instance
end Theory.SpecificGroups.SymplecticFour
