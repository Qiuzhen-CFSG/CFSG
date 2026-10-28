module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OrbitSupports
public import Theory.GroupTheory.NormalSymmetricThreeQuotient
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Two symmetric-three factors and the literal support stabilizer

Independent nonzero factor supports identify their indices. With at most two
factors, the stabilizer of one support fixes the other index and normalizes
its actor. That second actor fixes the first support pointwise. An S₃² action
image on the first support would therefore kill a normal S₃, producing an
S₃³ section of the original rank-two covering group, which is impossible.

Source: Aschbacher--Smith 15.1.2, printed p.1085, the proper-orbit case.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData

theorem ambient_spaces_injective : Function.Injective (fun i => (c.ambientFactor d i).space) := by
  intro i j he
  by_contra hij
  have hh := (c.ambient_spaces_independent d).pairwiseDisjoint hij
  change Disjoint (c.ambientFactor d i).space (c.ambientFactor d j).space at hh
  change (c.ambientFactor d i).space = (c.ambientFactor d j).space at he
  rw [he] at hh
  exact c.ambient_space_ne_bot d j (disjoint_self.mp hh)

theorem support_stabilizer_fixes_index (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space) (i : d.Index)
    {g : G} (hg : g ∈ subspaceStabilizer ρ (c.ambientFactor d i).space) : π g i = i := by
  apply c.ambient_spaces_injective d
  change (c.ambientFactor d (π g i)).space = (c.ambientFactor d i).space
  rw [←hs]
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact (hg w).2 hw
  · intro w hw
    refine ⟨ρ g⁻¹ w,?_,?_⟩
    · apply (hg (ρ g⁻¹ w)).1
      simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
        Module.End.one_apply] using hw
    · simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

private theorem perm_fix_other_of_card_le_two {I : Type*} [Finite I]
    (hcard : Nat.card I ≤ 2) (p : Equiv.Perm I) {i j : I} (hij : i ≠ j)
    (hi : p i = i) : p j = j := by
  let : Nontrivial I := ⟨⟨i,j,hij⟩⟩
  let := Fintype.ofFinite I
  have hlo : 1 < Nat.card I := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hc : Nat.card I = 2 := by omega
  obtain ⟨k,hk,hunique⟩ := (Nat.card_eq_two_iff' i).mp hc
  have hpj : p j ≠ i := by
    intro he
    exact hij (p.injective (hi.trans he.symm))
  exact (hunique (p j) hpj).trans (hunique j hij.symm).symm

theorem support_stabilizer_normalizes_other_actor
    (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (hcount : Nat.card d.Index ≤ 2) {i j : d.Index} (hij : i ≠ j) :
    subspaceStabilizer ρ (c.ambientFactor d i).space ≤
      normalizer ((c.ambientFactor d j).actor : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hi := c.support_stabilizer_fixes_index d π hs i hg
  have hj := perm_fix_other_of_card_le_two hcount (π g) hij hi
  have he := hp g j
  rw [hj] at he
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [he] at hh
  exact hh

theorem not_pair_image_with_other_symmetricThree_factor
    (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (hcount : Nat.card d.Index ≤ 2) {i j : d.Index} (hij : i ≠ j)
    (ej : (c.ambientFactor d j).Carrier ≃* Equiv.Perm (Fin 3))
    (ei : subspaceActionImage ρ (c.ambientFactor d i).space ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    {B : Type*} [Group B] [Finite B] (f : B →* G) (hf : Function.Surjective f)
    (hrank : primeRank 3 B ≤ 2) : False := by
  let S := subspaceStabilizer ρ (c.ambientFactor d i).space
  let H := (c.ambientFactor d j).actor
  have hHS : H ≤ S := by
    apply le_subspaceStabilizer
    intro g hg w hw
    rw [show ρ g w = w from c.ambient_cross d hij hw ⟨g,hg⟩]
    exact hw
  let L := H.subgroupOf S
  let : L.Normal := normal_subgroupOf_of_le_normalizer
    (c.support_stabilizer_normalizes_other_actor d π hp hs hcount hij)
  let eL : L ≃* Equiv.Perm (Fin 3) :=
    (subgroupOfEquivOfLe hHS).trans
      ((MonoidHom.ofInjective (c.ambientFactor d j).embedding.group_injective).symm.trans ej)
  let q : S →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    ei.toMonoidHom.comp (subspaceActionHom ρ (c.ambientFactor d i).space)
  have hq : Function.Surjective q := ei.surjective.comp
    (stabilizerRepresentation ρ (c.ambientFactor d i).space).asGroupHom.rangeRestrict_surjective
  have hL : L ≤ q.ker := by
    intro g hg
    change ei (subspaceActionHom ρ (c.ambientFactor d i).space g) = 1
    rw [←ei.map_one]
    apply congrArg ei
    apply subspaceImageRepresentation_injective ρ (c.ambientFactor d i).space
    ext w
    change ρ (g : G) (w : V) = w
    exact c.ambient_cross d hij w.property ⟨g,hg⟩
  let C := S.comap f
  exact Theory.GroupTheory.NormalSymmetricThree.not_surjective_pair_killing_normal_symmetricThree
    ((primeRank_subgroup_le 3 C).trans hrank) (f.subgroupComap S)
    (f.subgroupComap_surjective_of_surjective S hf) L eL q hq hL

end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
