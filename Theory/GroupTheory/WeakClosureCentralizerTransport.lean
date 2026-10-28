module
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Weak closure and Sylow subgroups of element centralizers

Let Q be weakly closed in a Sylow p-subgroup T. If x is conjugate to an
element centralizing Q and C_G(x) has a Sylow subgroup contained in T,
then x itself centralizes Q. Conjugate Q into C_G(x), move that conjugate
into its specified Sylow using conjugacy inside C_G(x), and apply weak
closure. The correcting conjugator centralizes x throughout.

This is a general fusion step used in the unitary case of Aschbacher–Smith
F.4.37–38, printed pp.293–294 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Weak closure recovers centralization when the target centralizer has
a Sylow subgroup contained in the specified ambient Sylow. -/
theorem mem_centralizer_of_isConj_of_weakly_closed
    (T : Sylow p G) (Q : Subgroup G) (hQT : Q ≤ (T : Subgroup G))
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      Q.map (MulAut.conj g).toMonoidHom = Q)
    {x y : G} (hy : y ∈ centralizer (Q : Set G)) (hxy : IsConj y x)
    (P : Sylow p (centralizer ({x} : Set G)))
    (hPT : (P : Subgroup _).map (centralizer ({x} : Set G)).subtype ≤ (T : Subgroup G)) :
    x ∈ centralizer (Q : Set G) := by
  let C := centralizer ({x} : Set G)
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  let V := Q.map (MulAut.conj g).toMonoidHom
  have hVC : V ≤ C := by
    rintro _ ⟨q,hq,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change (MulAut.conj g q) * x = x * (MulAut.conj g q)
    change MulAut.conj g y = x at hg
    rw [←hg,←map_mul,←map_mul,hy q hq]
  obtain ⟨R,hR⟩ := (((T.isPGroup'.to_le hQT).map
    (MulAut.conj g).toMonoidHom).comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq C R P
  have hV : V.map (MulAut.conj c.val).toMonoidHom ≤
      (P : Subgroup C).map C.subtype := by
    rintro _ ⟨v,hv,rfl⟩
    have hvR := hR (show (⟨v,hVC hv⟩ : C) ∈ V.subgroupOf C from hv)
    have hvP : MulAut.conj c ⟨v,hVC hv⟩ ∈ (P : Subgroup C) := by
      rw [←hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom hvR
    exact mem_map_of_mem C.subtype hvP
  have hcomp : Q.map (MulAut.conj (c.val*g)).toMonoidHom =
      V.map (MulAut.conj c.val).toMonoidHom := by
    rw [map_map]
    congr 1
    ext q
    simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe,MulAut.conj_apply,mul_inv_rev,mul_assoc]
  have hQ : V.map (MulAut.conj c.val).toMonoidHom = Q :=
    hcomp ▸ hweak (c.val*g) (hcomp ▸ hV.trans hPT)
  have hcentral : V.map (MulAut.conj c.val).toMonoidHom ≤ C := by
    rintro _ ⟨v,hv,rfl⟩
    exact (C.mul_mem (C.mul_mem c.property (hVC hv)) (C.inv_mem c.property))
  intro q hq
  exact mem_centralizer_singleton_iff.mp (hcentral (hQ.symm ▸ hq))

end Sylow
