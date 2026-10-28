module

public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.InvariantLeviDecomposition

/-!
# Coboundaries in an invariant direct product

If the fixed elements of each of two disjoint commuting invariant factors are
coboundaries, the same holds in their join. Uniqueness of the factorization
makes each factor of a fixed element fixed; multiplication then combines its
two coboundary witnesses.

This is the direct-product step for the center calculation used in
Aschbacher–Smith, 2.4.12(2) and 2.4.21, printed pp.530 and 536.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem coboundaries_sup_of_disjoint_commuting
    (A B : Subgroup G) (hd : Disjoint A B) (hc : A≤centralizer (B:Set G))
    (α : MulAut G) (hA : ∀u∈A,α u∈A) (hB : ∀v∈B,α v∈B)
    (htraceA : ∀u∈A,α u=u→∃w∈A,u=w*(α w)⁻¹)
    (htraceB : ∀u∈B,α u=u→∃w∈B,u=w*(α w)⁻¹) :
    ∀z∈A⊔B,α z=z→∃w∈A⊔B,z=w*(α w)⁻¹ := by
  intro z hz hzfix
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  obtain ⟨⟨u,v⟩,huv⟩ := e.surjective ⟨z,hz⟩
  have hz' : (u:G)*(v:G)=z := (he u v).symm.trans (congrArg Subtype.val huv)
  have hf := fixed_factors_of_disjoint α.toMonoidHom A B hd hA hB u.property v.property
    (hz' ▸ hzfix)
  obtain ⟨w,hw,hewu⟩ := htraceA u u.property hf.1
  obtain ⟨y,hy,heyv⟩ := htraceB v v.property hf.2
  refine ⟨w*y,mul_mem (mem_sup_left hw) (mem_sup_right hy),?_⟩
  rw [←hz',hewu,heyv,map_mul,mul_inv_rev]
  calc
    (w*(α w)⁻¹)*(y*(α y)⁻¹)=w*(y*(α y)⁻¹)*(α w)⁻¹ := by
      have hh : (α w)⁻¹ * (y*(α y)⁻¹) = (y*(α y)⁻¹) * (α w)⁻¹ :=
        (hc (A.inv_mem (hA w hw)) _ (B.mul_mem hy (B.inv_mem (hB y hy)))).symm
      rw [mul_assoc,hh]
      simp only [mul_assoc]
    _=(w*y)*((α y)⁻¹*(α w)⁻¹) := by simp only [mul_assoc]
end Theory.GroupTheory

