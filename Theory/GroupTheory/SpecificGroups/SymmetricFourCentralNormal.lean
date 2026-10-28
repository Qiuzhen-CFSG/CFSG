module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.SpecificGroups.SymmetricFourElementaryCentralizer

/-!
# Normal elementary subgroups above the center of E₄ × S₄

The only normal subgroups of the natural Klein four in S₄ are the identity
and the whole Klein four. Consequently a normal subgroup of an elementary
normal subgroup of E₄ × S₄ which contains the full center and has more than
four elements is the whole elementary subgroup. The proof projects to S₄
and then lifts using the contained central factor.

This is the generation calculation for the five-element root class in
Aschbacher–Smith F.5.4(4), printed p.301.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace SymmetricFourCentralNormal
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
abbrev Model := (C2 × C2) × S4

private theorem center_perm : ∀ x : S4, (∀ y : S4, y * x = x * y) → x = 1 := by
  decide +kernel

theorem center_eq : center Model = (⊤ : Subgroup (C2 × C2)).prod ⊥ := by
  ext x
  constructor
  · intro hx
    refine ⟨mem_top _,?_⟩
    apply center_perm x.2
    intro y
    exact congrArg Prod.snd (mem_center_iff.mp hx (1,y))
  · rintro ⟨_,hx⟩
    change x.2=1 at hx
    apply mem_center_iff.mpr
    intro y
    apply Prod.ext
    · exact mul_comm _ _
    · simp [hx]

theorem center_card : Nat.card (center Model) = 4 := by
  rw [center_eq,Nat.card_congr ((⊤ : Subgroup (C2 × C2)).prodEquiv (⊥ : Subgroup S4)).toEquiv,
    Nat.card_prod,Nat.card_congr (topEquiv (G := C2 × C2)).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- In E₄ × S₄, a normal subgroup of an elementary normal two-subgroup
which contains the full center and has order greater than four is the whole subgroup. -/
theorem normal_eq_of_center_le (A N : Subgroup Model) [A.Normal] [N.Normal]
    [IsElementaryAbelian 2 A] (hNA : N ≤ A) (hZN : center Model ≤ N)
    (hc : 4 < Nat.card N) : N = A := by
  classical
  let f := MonoidHom.snd (C2 × C2) S4
  have hfs : Function.Surjective f := fun y => ⟨(1,y),rfl⟩
  let B := N.map f
  let : B.Normal := Normal.map inferInstance f hfs
  let : (A.map f).Normal := Normal.map inferInstance f hfs
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hAc : A.map f ≤ core := by
    rw [core_eq]
    exact le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 (A.map f)⟩
  have hBc : B ≤ core := (map_mono hNA).trans hAc
  rcases normal_subgroup_core B hBc with hbot | hcore
  · have hNZ : N ≤ center Model := by
      intro x hx
      rw [center_eq]
      refine ⟨mem_top _,?_⟩
      have hh : f x ∈ B := mem_map_of_mem f hx
      rw [hbot] at hh
      exact hh
    have hh := (card_le_of_le hNZ).trans_eq center_card
    omega
  · apply le_antisymm hNA
    intro a ha
    have haB : f a ∈ B := hcore.symm ▸ hAc (mem_map_of_mem f ha)
    obtain ⟨n,hn,he⟩ := haB
    have hz : (a.1 * n.1⁻¹,1) ∈ N := by
      apply hZN
      rw [center_eq]
      exact ⟨mem_top _,one_mem _⟩
    have hm := N.mul_mem hz hn
    convert hm using 1
    apply Prod.ext
    · simp
    · exact he.symm

end SymmetricFourCentralNormal
