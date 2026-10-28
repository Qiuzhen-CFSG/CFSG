module
public import Mathlib.GroupTheory.IsPerfect

/-!
# Two-conjugate subgroups in a paired product

A subgroup with perfect first projection and abelian second projection is
the product of those projections. Its derived subgroup supplies every first
coordinate with second coordinate one. Thus the original, possibly diagonal
V and its conjugate by (g,1) generate the perfect first witness times V₂.

Source: Aschbacher–Smith E.2.7, paired Bender paragraph, printed p.219.
-/

@[expose] public section
namespace Subgroup
variable {G A : Type*} [Group G] [Group A]

theorem eq_prod_of_perfect_fst (I : Subgroup (G × A))
    [Group.IsPerfect (I.map (MonoidHom.fst G A))]
    [IsMulCommutative (I.map (MonoidHom.snd G A))] :
    I = (I.map (MonoidHom.fst G A)).prod (I.map (MonoidHom.snd G A)) := by
  have hfst : (⁅I,I⁆).map (MonoidHom.fst G A) = I.map (MonoidHom.fst G A) := by
    rw [map_commutator, commutator_eq_self]
  have hsnd : (⁅I,I⁆).map (MonoidHom.snd G A) = ⊥ := by
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  have hin (x : G) (hx : x ∈ I.map (MonoidHom.fst G A)) : (x,1) ∈ I := by
    rw [← hfst] at hx
    obtain ⟨z,hz,he⟩ := hx
    have hz2 : z.2 = 1 := by
      have hh := mem_map_of_mem (MonoidHom.snd G A) hz
      rwa [hsnd,mem_bot] at hh
    have hz1 : z.1 = x := he
    have hez : z = (x,1) := Prod.ext hz1 hz2
    exact hez ▸ commutator_le_self I hz
  apply le_antisymm (le_prod_iff.mpr ⟨le_rfl,le_rfl⟩)
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  obtain ⟨z,hz,he⟩ := hy
  have hz1 : z.1 ∈ I.map (MonoidHom.fst G A) := mem_map_of_mem _ hz
  have hz2 : z.2 = y := he
  have hone : (1,y) ∈ I := by
    have hh := I.mul_mem (I.inv_mem (hin z.1 hz1)) hz
    have hez : z = (z.1,y) := Prod.ext rfl hz2
    rw [hez] at hh
    simpa using hh
  simpa only [Prod.mk_mul_mk, one_mul, mul_one] using I.mul_mem (hin x hx) hone

theorem twoConjugate_eq_prod (V : Subgroup (G × A)) (g : G)
    [Group.IsPerfect ↥(V.map (MonoidHom.fst G A) ⊔
      (V.map (MonoidHom.fst G A)).map (MulAut.conj g).toMonoidHom)]
    [IsMulCommutative (V.map (MonoidHom.snd G A))] :
    V ⊔ V.map (MulAut.conj (g,1)).toMonoidHom =
      (V.map (MonoidHom.fst G A) ⊔
        (V.map (MonoidHom.fst G A)).map (MulAut.conj g).toMonoidHom).prod
          (V.map (MonoidHom.snd G A)) := by
  let I := V ⊔ V.map (MulAut.conj (g,1)).toMonoidHom
  have hf : I.map (MonoidHom.fst G A) = V.map (MonoidHom.fst G A) ⊔
      (V.map (MonoidHom.fst G A)).map (MulAut.conj g).toMonoidHom := by
    simp only [I,map_sup,map_map]
    congr 2
  have hs : I.map (MonoidHom.snd G A) = V.map (MonoidHom.snd G A) := by
    simp only [I,map_sup,map_map]
    have hc : (MonoidHom.snd G A).comp (MulAut.conj (g,1)).toMonoidHom =
        MonoidHom.snd G A := by
      ext x
      simp [MulAut.conj_apply]
    rw [hc,sup_idem]
  let : Group.IsPerfect (I.map (MonoidHom.fst G A)) := hf.symm ▸ inferInstance
  let : IsMulCommutative (I.map (MonoidHom.snd G A)) := hs.symm ▸ inferInstance
  exact (eq_prod_of_perfect_fst I).trans (by rw [hf,hs])
end Subgroup
