module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Geometry
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.LocalFusion.CentralFactor
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.SylowTransport
public import GorensteinWalter.DihedralOuterInvolutionConjugacy
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Local fusion and the direct product in Lemma 16.4.6

Involutions in T_L fuse inside the actual PSL₂ model. For an involution
x in the other coset of D = T_L⟨u⟩, the central twist xz lies outside
T_L in the dihedral group T_L⟨r⟩. That subgroup has index two and is
noncyclic, so the dihedral conjugacy theorem fuses xz to uz. Its
conjugator fixes z, hence fuses x to u and then to v. This excludes every
conjugate of z from D. The central-factor transvection construction gives
T_C = ⟨z⟩, and the relation vz = ur identifies T_C T_L R with T_C × D.

Source: Aschbacher–Smith, Lemma 16.4.6, printed pp.1185–1186. These
results are conditional on the published configuration and the genuine
outer PGL₂ action; no local fusion or product conclusion is a premise.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
open Subgroup GorensteinWalter
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

private theorem mem_two {a x : G} (ha : orderOf a = 2) :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, hn'⟩
    interval_cases n <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

private theorem join_cases {A : Subgroup G} {a x : G}
    (hn : a ∈ normalizer (A : Set G)) (ha : orderOf a = 2)
    (hx : x ∈ A ⊔ zpowers a) : x ∈ A ∨ ∃ b ∈ A, x = b * a := by
  have hx' : x ∈ (A : Set G) * (zpowers a : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A (zpowers a) (zpowers_le.mpr hn)]
    exact hx
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  rcases (mem_two ha).mp hc with rfl | rfl
  · exact Or.inl (by simpa using hb)
  · exact Or.inr ⟨b, hb, rfl⟩

namespace Configuration
variable {T : Sylow 2 G} {L R : Subgroup G} {g r z v u s t : G}
variable (h : Configuration T L R g r z v u s t)
include h

/-- The transfer subgroup is a subgroup of the specified Sylow subgroup. -/
theorem transferSubgroup_le : transferSubgroup T L u ≤ (T : Subgroup G) :=
  sup_le inf_le_left (zpowers_le.mpr h.u_mem_sylow)

/-- The central twist of u is the marked outer involution rv. -/
theorem u_mul_z : u * z = r * v := by
  have hz2 : z * z = 1 := by simpa [h.eight.z_order, pow_two] using pow_orderOf_eq_one z
  have hvz : v * z = z * v := mem_centralizer_singleton_iff.mp
    (h.source.sylow_centralizes h.v_mem_inner.1)
  rw [h.eight.u_eq, ← hvz, mul_assoc, mul_assoc, hz2, mul_one]

/-- T_L is a genuine Sylow subgroup of L, by relative normality in N_G(L). -/
theorem inner_sylow : SylowIn (innerSylow T L) L := by
  have hTN : SylowIn (T : Subgroup G) (normalizer (L : Set G)) :=
    ⟨T.subtype h.source.sylow_normalizes, map_subgroupOf_eq_of_le h.source.sylow_normalizes⟩
  exact hTN.inf_normal L.le_normalizer le_rfl

variable {F : Type*} [Field F] [Finite F]

/-- The intrinsic odd PSL₂ Sylow calculation proves that T_L is noncyclic. -/
theorem inner_not_cyclic (e : L ≃* PSL2 F) (hF : IsOddPrimePower (Nat.card F)) :
    ¬ IsCyclic (innerSylow T L) := by
  intro hcyc
  obtain ⟨S, hS⟩ := h.inner_sylow
  let eS : S ≃* innerSylow T L :=
    (equivMapOfInjective (S : Subgroup L) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hS)
  let : IsCyclic S := eS.isCyclic.mpr hcyc
  let P : Sylow 2 (PSL2 F) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let eP : S ≃* P := e.subgroupMap (S : Subgroup L)
  have hPc : IsCyclic P := eP.isCyclic.mp inferInstance
  obtain ⟨m, hm, ⟨em⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF P
  exact DihedralGroup.not_isCyclic
    (Nat.one_lt_pow (by omega : m ≠ 0) (by decide : 1 < (2 : ℕ))).ne.symm
    (em.isCyclic.mp hPc)

/-- The actual outer projective action prevents r from lying in L. -/
theorem r_not_mem_inner_of_outer (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e) :
    r ∉ innerSylow T L := by
  intro hr
  apply not_inner_of_inducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e hF hcard hout
  refine ⟨⟨r, hr.2⟩, ?_⟩
  ext x
  rfl

/-- The inner Sylow has index two in the retained dihedral overgroup. -/
theorem inner_index_two (hr : r ∉ innerSylow T L) :
    (innerSylow T L).relIndex (innerSylow T L ⊔ R) = 2 := by
  rw [h.R_eq]
  apply relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨r, mem_sup_right (mem_zpowers r), hr, ?_⟩
  intro b hb
  rcases join_cases (h.sylow_normalizes_inner h.r_mem_sylow) h.eight.r_order hb with
    hb | ⟨a, ha, rfl⟩
  · exact Or.inr hb
  · left
    have hr2 : r * r = 1 := by simpa [h.eight.r_order, pow_two] using pow_orderOf_eq_one r
    simpa only [mul_assoc, hr2, mul_one] using ha

/-- Involutions in L fuse through its actual projective model. -/
theorem inner_involution_fused (e : L ≃* PSL2 F) {x : G}
    (hx : x ∈ innerSylow T L) (hx2 : orderOf x = 2) : IsConj x v := by
  let xL : L := ⟨x, hx.2⟩
  let vL : L := ⟨v, h.v_mem_inner.2⟩
  have hxL : orderOf (e xL) = 2 := by
    rw [e.orderOf_eq, ← orderOf_injective L.subtype L.subtype_injective xL]
    exact hx2
  have hvL : orderOf (e vL) = 2 := by
    rw [e.orderOf_eq, ← orderOf_injective L.subtype L.subtype_injective vL]
    exact h.eight.v_order
  have hh := L.subtype.map_isConj (e.symm.toMonoidHom.map_isConj
    (Theory.PSL2.involutions_isConj (e xL) (e vL) hxL hvL))
  change IsConj (e.symm (e xL) : G) (e.symm (e vL) : G) at hh
  simpa only [e.symm_apply_apply] using hh

/-- The outer coset of D fuses by cancelling the fixed central twist z
from the dihedral conjugacy of xz and uz. -/
theorem outer_involution_fused (hr : r ∉ innerSylow T L)
    (hnc : ¬ IsCyclic (innerSylow T L)) {x : G}
    (hx : x ∈ transferSubgroup T L u) (hxout : x ∉ innerSylow T L)
    (hx2 : orderOf x = 2) : IsConj x v := by
  let A := innerSylow T L
  let J := A ⊔ R
  have hJT : J ≤ (T : Subgroup G) := sup_le inf_le_left h.source.le_sylow
  have hrJ : r ∈ J := mem_sup_right (h.R_eq ▸ mem_zpowers r)
  have huzJ : u * z ∈ J := by
    rw [h.u_mul_z]
    exact J.mul_mem hrJ (mem_sup_left h.v_mem_inner)
  have huzout : u * z ∉ A := by
    intro hu
    apply hr
    have hh := A.mul_mem hu (A.inv_mem h.v_mem_inner)
    simpa only [h.u_mul_z, mul_inv_cancel_right] using hh
  obtain ⟨a, ha, he⟩ := (join_cases (h.sylow_normalizes_inner h.u_mem_sylow)
    h.eight.u_order hx).resolve_left hxout
  have hxz : x * z = a * (u * z) := by rw [he, mul_assoc]
  have hxzJ : x * z ∈ J := by rw [hxz]; exact J.mul_mem (mem_sup_left ha) huzJ
  have hxzout : x * z ∉ A := by
    intro hh
    apply huzout
    have hh' := A.mul_mem (A.inv_mem ha) hh
    simpa only [hxz, inv_mul_cancel_left] using hh'
  have twist_involution {y : G} (hyT : y ∈ T) (hy2 : orderOf y = 2)
      (hyout : y * z ∉ A) (hyJ : y * z ∈ J) : IsInvolution (⟨y * z, hyJ⟩ : J) := by
    constructor
    · intro hy
      apply hyout
      have heq : y * z = 1 := congrArg Subtype.val hy
      rw [heq]
      exact A.one_mem
    · apply Subtype.ext
      change (y * z) ^ 2 = 1
      have hc : Commute y z := mem_centralizer_singleton_iff.mp (h.source.sylow_centralizes hyT)
      have hy_sq : y ^ 2 = 1 := hy2 ▸ pow_orderOf_eq_one y
      have hz_sq : z ^ 2 = 1 := h.eight.z_order ▸ pow_orderOf_eq_one z
      rw [hc.mul_pow, hy_sq, hz_sq, one_mul]
  let H := A.subgroupOf J
  have hHnc : ¬ IsCyclic H := by
    intro hh
    exact hnc ((subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).isCyclic.mp hh)
  obtain ⟨n, hn, ⟨en⟩⟩ := h.inner_dihedral
  have hconj : IsConj (⟨x * z, hxzJ⟩ : J) ⟨u * z, huzJ⟩ :=
    dihedral_involutions_not_mem_noncyclic_index_two_isConj hn en H (h.inner_index_two hr)
      hHnc (twist_involution (h.transferSubgroup_le hx) hx2 hxzout hxzJ)
      (twist_involution h.u_mem_sylow h.eight.u_order huzout huzJ) hxzout huzout
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hc' : MulAut.conj (c : G) (x * z) = u * z := congrArg Subtype.val hc
  rw [map_mul, h.sylow_fixes_z (hJT c.property)] at hc'
  exact (isConj_iff.mpr ⟨(c : G), mul_right_cancel hc'⟩).trans h.eight.u_fused_v

/-- Every involution of the actual transfer subgroup D is G-conjugate to v. -/
theorem transfer_involutions_fused (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e)
    {x : G} (hx : x ∈ transferSubgroup T L u) (hx2 : orderOf x = 2) : IsConj x v := by
  by_cases hxin : x ∈ innerSylow T L
  · exact h.inner_involution_fused e hxin hx2
  · exact h.outer_involution_fused (h.r_not_mem_inner_of_outer e hF hcard hout)
      (h.inner_not_cyclic e hF) hx hxin hx2

/-- No element of D is conjugate to z: a conjugate would be an involution
and hence fuse to v, contradicting the marked weak closure. -/
theorem transfer_no_conjugate (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e) :
    ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x := by
  intro x hx hzx
  obtain ⟨a, ha⟩ := isConj_iff.mp hzx
  have hx2 : orderOf x = 2 := by
    rw [← ha]
    exact ((MulAut.conj a).orderOf_eq z).trans h.eight.z_order
  exact h.eight.z_not_fused_v (hzx.trans (h.transfer_involutions_fused e hF hcard hout hx hx2))

/-- The nonfusion statement on the actual subgroup of T, for transfer. -/
theorem transfer_subgroupOf_no_conjugate (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e) :
    ∀ x : T, x ∈ (transferSubgroup T L u).subgroupOf (T : Subgroup G) →
      ¬ IsConj z (x : G) := by
  intro x hx
  exact h.transfer_no_conjugate e hF hcard hout x hx

/-- The marked relation identifies the generated local overgroup. -/
theorem central_inner_outer_eq :
    (centralizingSylow T L ⊔ innerSylow T L) ⊔ R =
      centralizingSylow T L ⊔ transferSubgroup T L u := by
  let W := centralizingSylow T L ⊔ transferSubgroup T L u
  have huW : u ∈ W := mem_sup_right (mem_sup_right (mem_zpowers u))
  have hvW : v ∈ W := mem_sup_right (mem_sup_left h.v_mem_inner)
  have hzW : z ∈ W := mem_sup_left h.z_mem_central
  have hrW : r ∈ W := by
    have hu2 : u * u = 1 := by simpa [h.eight.u_order, pow_two] using pow_orderOf_eq_one u
    have he : r = u * (v * z) := by
      rw [h.eight.fixed_line_relation, ← mul_assoc, hu2, one_mul]
    rw [he]
    exact W.mul_mem huW (W.mul_mem hvW hzW)
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (h.R_eq ▸ zpowers_le.mpr hrW)
  · refine sup_le (le_sup_left.trans le_sup_left) (sup_le
      (le_sup_right.trans le_sup_left) (zpowers_le.mpr ?_))
    rw [h.eight.u_eq]
    exact ((centralizingSylow T L ⊔ innerSylow T L) ⊔ R).mul_mem
      (mem_sup_right (h.R_eq ▸ mem_zpowers r))
      (((centralizingSylow T L ⊔ innerSylow T L) ⊔ R).mul_mem
        (mem_sup_left (mem_sup_left h.z_mem_central))
        (mem_sup_left (mem_sup_right h.v_mem_inner)))

/-- The central factor commutes elementwise with D. -/
theorem central_commutes_transfer :
    centralizingSylow T L ≤ centralizer (transferSubgroup T L u : Set G) := by
  rw [h.central_eq_zpowers]
  apply zpowers_le.mpr
  intro x hx
  exact mem_centralizer_singleton_iff.mp
    (h.source.sylow_centralizes (h.transferSubgroup_le hx))

/-- The central factor and D have trivial intersection. -/
theorem central_disjoint_transfer (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e) :
    Disjoint (centralizingSylow T L) (transferSubgroup T L u) := by
  rw [h.central_eq_zpowers]
  apply Subgroup.disjoint_def.mpr
  intro x hx hxD
  rcases (mem_two h.eight.z_order).mp hx with he | he
  · exact he
  · rw [he] at hxD
    exact False.elim (h.transfer_no_conjugate e hF hcard hout z hxD (IsConj.refl z))

/-- Multiplication is an actual group isomorphism from T_C × D onto T_C T_L R,
with the prescribed embeddings of both factors. -/
theorem local_product_equiv (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h.source (h.R_eq ▸ mem_zpowers r) e) :
    ∃ j : centralizingSylow T L × transferSubgroup T L u ≃*
        ↥((centralizingSylow T L ⊔ innerSylow T L) ⊔ R),
      ∀ a b, (j (a, b) : G) = (a : G) * (b : G) := by
  obtain ⟨j, hj⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (centralizingSylow T L) (transferSubgroup T L u)
    (h.central_disjoint_transfer e hF hcard hout) h.central_commutes_transfer
  exact ⟨j.trans (MulEquiv.subgroupCongr h.central_inner_outer_eq.symm), hj⟩

end Configuration
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
