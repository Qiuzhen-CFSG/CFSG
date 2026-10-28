module
public import Theory.GroupTheory.DisjointKernelCentralizer
public import Theory.GroupTheory.AbelianKernelCentralizer
public import Mathlib.GroupTheory.Index
public import Theory.GroupTheory.DihedralNormalAbelian
public import Theory.GroupTheory.SemidihedralNormalAbelian

/-!
# The exponent obstruction for a crossed abelian kernel

A noncentral abelian kernel has centralizer C*D when that commuting
product has index at most two. Its automorphic crossed copy embeds in
the image of D, so both factors share D's power bound. Normality and
kernel disjointness pull the quotient centralizer back exactly. A maximal
rotation downstairs then contradicts that power bound in the automorphic
centralizer upstairs.

The two final concrete applications discharge the model properties for
dihedral and semidihedral-sixteen quotients in Aschbacher--Smith 2.5.21,
printed p.565. No centralizer abelianness is assumed.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {S Q : Type*} [Group S] [Finite S] [Group Q]

/-- The model exponent obstruction for an abelian crossed kernel. -/
theorem abelian_crossing_kernel_impossible
    (q : S →* Q) (hq : Function.Surjective q) (C D : Subgroup S)
    (hk : q.ker = C) [IsMulCommutative C]
    (hCD : Disjoint C D) (hDC : D ≤ centralizer (C : Set S))
    (hi : (C ⊔ D).index ≤ 2) (hnC : ¬ C ≤ center S) (hnD : ¬ IsMulCommutative D)
    (a : MulAut S) (hCX : Disjoint C (C.map a.toMonoidHom))
    (hXC : C.map a.toMonoidHom ≤ centralizer (C : Set S))
    (m : ℕ)
    (hpow : ∀ B : Subgroup Q, B.index = 2 → ¬ IsMulCommutative B → ∀ b ∈ B, b ^ m = 1)
    (hrot : ∀ B : Subgroup Q, B.Normal → IsMulCommutative B →
      ∃ r : Q, r ∈ centralizer (B : Set Q) ∧ ¬ orderOf r ∣ m) : False := by
  let : C.Normal := hk ▸ q.normal_ker
  let X := C.map a.toMonoidHom
  let : X.Normal := Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  let : IsMulCommutative X := inferInstance
  have hXker : Disjoint X q.ker := hk.symm ▸ hCX.symm
  have hinj (B : Subgroup S) (hb : Disjoint B C) :
      Function.Injective (q.comp B.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro b hbq
    exact Subtype.ext (disjoint_def.mp hb b.property (hk ▸ hbq))
  have hDinj := hinj D hCD.symm
  have hXinj := hinj X hCX.symm
  obtain ⟨hcent, hindex⟩ := centralizer_eq_sup_of_index_le_two C D hDC hi hnC
  have hDb : (D.map q).index = 2 := by
    rw [index_map, hk, q.range_eq_top_of_surjective hq, index_top, mul_one, sup_comm, hindex]
  have hDnon : ¬ IsMulCommutative (D.map q) := by
    intro hh
    apply hnD
    refine ⟨⟨fun d e => hDinj ?_⟩⟩
    simpa only [map_mul, MonoidHom.comp_apply, coe_mul, subtype_apply] using congrArg Subtype.val (hh.is_comm.comm
      (⟨q d, mem_map_of_mem q d.property⟩ : D.map q)
      ⟨q e, mem_map_of_mem q e.property⟩)
  have hDp (d : S) (hd : d ∈ D) : d ^ m = 1 := by
    have hh := hpow (D.map q) hDb hDnon (q d) (mem_map_of_mem q hd)
    have hh' : (⟨d, hd⟩ : D) ^ m = 1 := hDinj (by simpa only [map_mul, map_pow, map_one, MonoidHom.comp_apply, subtype_apply] using hh)
    exact congrArg Subtype.val hh'
  have hXle : X.map q ≤ D.map q := by
    have hle : X ≤ C ⊔ D := hcent ▸ hXC
    have hh := map_mono (f := q) hle
    rw [Subgroup.map_sup, ← hk, map_ker_self, bot_sup_eq] at hh
    exact hh
  have hXp (x : S) (hx : x ∈ X) : x ^ m = 1 := by
    have hh := hpow (D.map q) hDb hDnon (q x) (hXle (mem_map_of_mem q hx))
    have hh' : (⟨x, hx⟩ : X) ^ m = 1 := hXinj (by simpa only [map_mul, map_pow, map_one, MonoidHom.comp_apply, subtype_apply] using hh)
    exact congrArg Subtype.val hh'
  have hCp (c : S) (hc : c ∈ C) : c ^ m = 1 := a.injective (by
    rw [map_pow, map_one]
    exact hXp (a c) (mem_map_of_mem a.toMonoidHom hc))
  have hbound : ∀ c ∈ centralizer (C : Set S), c ^ m = 1 := by
    rw [hcent]
    exact sup_power_bound_of_commute C D hDC m hCp hDp
  have he : (centralizer (C : Set S)).map a.toMonoidHom = centralizer (X : Set S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg a (hy z hz)
    · intro hx
      refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
      intro z hz
      apply a.injective
      simpa only [map_mul, a.apply_symm_apply] using hx (a z) ⟨z, hz, rfl⟩
  let e := (a.subgroupMap (centralizer (C : Set S))).trans (MulEquiv.subgroupCongr he)
  have hXn : (X.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hXcomm : IsMulCommutative (X.map q) := inferInstance
  obtain ⟨r, hr, horder⟩ := hrot (X.map q) hXn hXcomm
  exact centralizer_power_obstruction q hq C X hXker e m hbound r hr horder
/-- The complete intrinsic obstruction for a semidihedral-sixteen quotient. -/
theorem abelian_crossing_kernel_semidihedral_impossible
    (q : S →* Semidihedral.StandardModel 4 (by decide)) (hq : Function.Surjective q)
    (C D : Subgroup S) (hk : q.ker = C) [IsMulCommutative C]
    (hCD : Disjoint C D) (hDC : D ≤ centralizer (C : Set S))
    (hi : (C ⊔ D).index ≤ 2) (hnC : ¬ C ≤ center S) (hnD : ¬ IsMulCommutative D)
    (a : MulAut S) (hCX : Disjoint C (C.map a.toMonoidHom))
    (hXC : C.map a.toMonoidHom ≤ centralizer (C : Set S)) : False := by
  apply abelian_crossing_kernel_impossible q hq C D hk hCD hDC hi hnC hnD a hCX hXC 4
  · exact Semidihedral.AbelianCore.nonabelian_index_two_pow_four
  · intro B hn hc
    let := hn
    let := hc
    obtain ⟨r, hr, hc⟩ := Semidihedral.AbelianCore.exists_eight_centralizing_normal_abelian B
    exact ⟨r, hc, by rw [hr]; decide⟩

/-- The complete intrinsic obstruction for every dihedral two-group quotient. -/
theorem abelian_crossing_kernel_dihedral_impossible
    {n : ℕ} (q : S →* DihedralGroup (2 ^ n)) (hq : Function.Surjective q)
    (C D : Subgroup S) (hk : q.ker = C) [IsMulCommutative C]
    (hCD : Disjoint C D) (hDC : D ≤ centralizer (C : Set S))
    (hi : (C ⊔ D).index ≤ 2) (hnC : ¬ C ≤ center S) (hnD : ¬ IsMulCommutative D)
    (a : MulAut S) (hCX : Disjoint C (C.map a.toMonoidHom))
    (hXC : C.map a.toMonoidHom ≤ centralizer (C : Set S)) : False := by
  have hDinj : Function.Injective (q.comp D.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro d hd
    exact Subtype.ext (disjoint_def.mp hCD (hk ▸ hd) d.property)
  have hnDb : ¬ IsMulCommutative (D.map q) := by
    intro hh
    apply hnD
    refine ⟨⟨fun d e => hDinj ?_⟩⟩
    simpa only [map_mul, MonoidHom.comp_apply, coe_mul, subtype_apply] using
      congrArg Subtype.val (hh.is_comm.comm
        (⟨q d, mem_map_of_mem q d.property⟩ : D.map q) ⟨q e, mem_map_of_mem q e.property⟩)
  have hiDb : (D.map q).index = 2 := by
    rw [index_map, hk, q.range_eq_top_of_surjective hq, index_top, mul_one, sup_comm,
      (centralizer_eq_sup_of_index_le_two C D hDC hi hnC).2]
  have hn := DihedralGroup.parameter_ge_three_of_nonabelian_index_two (D.map q) hiDb hnDb
  apply abelian_crossing_kernel_impossible q hq C D hk hCD hDC hi hnC hnD a hCX hXC (2 ^ (n - 1))
  · exact fun B hiB hnB => DihedralGroup.nonabelian_index_two_pow hn B hiB hnB
  · intro B hnB hcB
    let := hnB
    let := hcB
    refine ⟨DihedralGroup.r 1, ?_, ?_⟩
    · exact (centralizer_le (DihedralGroup.normal_abelian_le_rotations hn B))
        ((zpowers (DihedralGroup.r 1)).le_centralizer (mem_zpowers _))
    · rw [DihedralGroup.orderOf_r_one]
      intro hd
      have hle := Nat.le_of_dvd (by positivity : 0 < 2 ^ (n - 1)) hd
      have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega)
      omega

end Theory.GroupTheory
