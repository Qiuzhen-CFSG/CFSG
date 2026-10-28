module

public import Theory.AlgebraicGroup.RootSubgroups.CocharacterExistence
public import Theory.AlgebraicGroup.Tori.Character.ConnectedKernel
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Cocharacter separation for distinct singular subtori

This proves the character-lattice step in Borel IV, 13.12. Distinct connected
character kernels force integral independence. A two-functional determinant
then supplies opposite signs. Finite successive perturbations avoid any finite
set of nonzero characters without changing those signs. Torus duality realizes
the resulting integral functional by an actual algebraic cocharacter.

The endpoint retains the literal ambient connected kernels. It does not
construct a Borel from the cocharacter or assert the Weyl-chamber restriction
criterion of 13.11(3); those are separate preceding source theorems.

Source: `refs/KGroup/Bor1/Chapter4.tex`, proof of 13.12, especially its last
sentence. The printed corollary's malformed display is read according to its
proof and its use in 13.15(2).
-/

open Matrix Module
public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M]

theorem exists_integral_separating_dual {α β : M}
    (hi : LinearIndependent ℤ ![α, β]) :
    ∃ φ : Module.Dual ℤ M, 0 < φ α ∧ φ β < 0 := by
  have ha : α ≠ 0 := hi.ne_zero 0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℤ ha
  have hz : (f α) • β - (f β) • α ≠ 0 := by
    intro hz
    have he : -(f β) • α + (f α) • β = 0 := by
      simpa [sub_eq_add_neg, neg_smul, add_comm] using hz
    exact hf ((LinearIndependent.pair_iff.mp hi _ _ he).2)
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℤ hz
  let d : ℤ := f α * g β - f β * g α
  have hd : d ≠ 0 := by
    simpa [d, map_sub, map_smul, smul_eq_mul] using hg
  let h : Module.Dual ℤ M := (g β + g α) • f - (f β + f α) • g
  have hα : h α = d := by simp [h, d]; ring
  have hβ : h β = -d := by simp [h, d]; ring
  refine ⟨d • h, ?_, ?_⟩
  · change 0 < d * h α
    rw [hα]
    exact mul_self_pos.mpr hd
  · change d * h β < 0
    rw [hβ, mul_neg]
    exact neg_neg_of_pos (mul_self_pos.mpr hd)

private theorem large_multiple_pos {n z y : ℤ} (hn : |y| < n) (hz : 0 < z) :
    0 < n * z + y := by
  have hn0 : 0 < n := lt_of_le_of_lt (abs_nonneg y) hn
  have hy := neg_abs_le y
  have hz1 : 1 ≤ z := by omega
  nlinarith

private theorem large_multiple_neg {n z y : ℤ} (hn : |y| < n) (hz : z < 0) :
    n * z + y < 0 := by
  have h := large_multiple_pos (n := n) (z := -z) (y := -y)
    (by simpa only [abs_neg] using hn) (neg_pos.mpr hz)
  nlinarith

theorem exists_integral_separating_regular_dual {α β : M}
    (hi : LinearIndependent ℤ ![α, β]) (s : Finset M)
    (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ φ : Module.Dual ℤ M, 0 < φ α ∧ φ β < 0 ∧ ∀ x ∈ s, φ x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨φ,ha,hb⟩ := exists_integral_separating_dual hi
    exact ⟨φ,ha,hb,by simp⟩
  | @insert x s hxs ih =>
    obtain ⟨φ,ha,hb,hφ⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
    by_cases hx : φ x ≠ 0
    · exact ⟨φ,ha,hb,by simpa only [Finset.forall_mem_insert] using And.intro hx hφ⟩
    push Not at hx
    obtain ⟨ψ,hψ⟩ := Module.Projective.exists_dual_ne_zero ℤ (hs x (Finset.mem_insert_self _ _))
    let t : Finset M := insert α (insert β s)
    let n : ℤ := 1 + ∑ y ∈ t, |ψ y|
    have hn (y : M) (hy : y ∈ t) : |ψ y| < n := by
      have he := Finset.single_le_sum (fun z (_ : z ∈ t) => abs_nonneg (ψ z)) hy
      dsimp only [n]
      omega
    let f : Module.Dual ℤ M := n • φ + ψ
    have hf (y : M) : f y = n * φ y + ψ y := rfl
    refine ⟨f, ?_, ?_, ?_⟩
    · rw [hf]
      exact large_multiple_pos (hn α (Finset.mem_insert_self _ _)) ha
    · rw [hf]
      exact large_multiple_neg (hn β (by simp [t])) hb
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa only [hf, hx, mul_zero, zero_add] using hψ
      · rw [hf]
        have hny : |ψ y| < n := hn y (by simp only [t, Finset.mem_insert]; exact Or.inr (Or.inr hy))
        rcases lt_or_gt_of_ne (hφ y hy) with hyneg | hypos
        · exact ne_of_lt (large_multiple_neg hny hyneg)
        · exact ne_of_gt (large_multiple_pos hny hypos)

section Kernels
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {T : Variety k} [AlgebraicGroup T]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

omit [IsAlgClosed k] in
private theorem carrier_connected (H : ClosedSubgroup T)
    (hH : _root_.IsConnected (H : Set (Variety.Point T))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point T // x ∈ (H : Set (Variety.Point T))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) := e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem pullback_connectedKernel_eq_one (χ : TorusCharacter T) :
    TorusCharacter.pullback χ.connectedKernel.inclusion χ = 1 := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  change χ.onPoints (χ.connectedKernel.inclusion.onPoints x) = 1
  exact χ.kernelClosedSubgroup.identityComponentAmbient_le
    (χ.connectedKernel.pointEquiv x).property

theorem connectedKernel_le_of_zpow_eq (χ ψ : TorusCharacter T) (m n : ℤ)
    (hn : n ≠ 0) (h : χ ^ m = ψ ^ n) : χ.connectedKernel ≤ ψ.connectedKernel := by
  let K := χ.connectedKernel
  have hKc : _root_.IsConnected (K : Set (Variety.Point T)) :=
    χ.kernelClosedSubgroup.identityComponentAmbient_isConnected
  let : IsMulTorsionFree (TorusCharacter K.carrierVariety) :=
    torusCharacter_isTorsionFree_of_isConnected _ (carrier_connected K hKc)
  have he := congrArg (TorusCharacter.pullback K.inclusion) h
  rw [map_zpow, map_zpow, pullback_connectedKernel_eq_one, one_zpow] at he
  have hψ : TorusCharacter.pullback K.inclusion ψ = 1 :=
    (IsMulTorsionFree.zpow_eq_one_iff_left hn).mp he.symm
  apply connected_closedSubgroup_le_identityComponentAmbient K ψ.kernelClosedSubgroup hKc
  intro x hx
  let y := K.pointEquiv.symm ⟨x,hx⟩
  have hy := congrArg (fun f : TorusCharacter K.carrierVariety => f.onPoints y) hψ
  change ψ.onPoints x = 1
  exact hy

theorem connectedKernel_eq_of_nonzero_zpow_eq (χ ψ : TorusCharacter T) (m n : ℤ)
    (hm : m ≠ 0) (hn : n ≠ 0) (h : χ ^ m = ψ ^ n) :
    χ.connectedKernel = ψ.connectedKernel := by
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · exact connectedKernel_le_of_zpow_eq χ ψ m n hn h
  · exact connectedKernel_le_of_zpow_eq ψ χ n m hm h.symm

theorem characters_independent_of_connectedKernel_ne (hT : Variety.IsConnected T)
    (χ ψ : TorusCharacter T) (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hne : χ.connectedKernel ≠ ψ.connectedKernel) :
    LinearIndependent ℤ ![Additive.ofMul χ, Additive.ofMul ψ] := by
  let : IsMulTorsionFree (TorusCharacter T) :=
    torusCharacter_isTorsionFree_of_isConnected T hT
  rw [LinearIndependent.pair_iff]
  intro m n h
  have he : χ ^ m = ψ ^ (-n) := by
    have hh : χ ^ m * ψ ^ n = 1 := congrArg Additive.toMul h
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left hh
  by_cases hm : m = 0
  · subst m
    simp only [zpow_zero] at he
    have hn : -n = 0 := (IsMulTorsionFree.zpow_eq_one_iff_right hψ).mp he.symm
    exact ⟨rfl,by omega⟩
  · by_cases hn : n = 0
    · subst n
      simp only [neg_zero,zpow_zero] at he
      exact False.elim (hm ((IsMulTorsionFree.zpow_eq_one_iff_right hχ).mp he))
    · exact False.elim (hne (connectedKernel_eq_of_nonzero_zpow_eq χ ψ m (-n) hm
        (neg_ne_zero.mpr hn) he))

end Kernels

section Cocharacters
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

theorem exists_cocharacter_separating_weights
    (T : ClosedSubgroup G) (hT : IsSubtorus T) (α β : TorusWeight T)
    (hi : LinearIndependent ℤ ![Additive.ofMul α, Additive.ofMul β])
    (s : Finset (TorusWeight T)) (hs : ∀ χ ∈ s, χ ≠ 1) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      0 < characterCocharacterPairing T c (Additive.ofMul α) ∧
      characterCocharacterPairing T c (Additive.ofMul β) < 0 ∧
      ∀ χ ∈ s, characterCocharacterPairing T c (Additive.ofMul χ) ≠ 0 := by
  classical
  obtain ⟨n,⟨e⟩⟩ := hT
  let : Module.Free ℤ (Additive (TorusWeight T)) := torus_character_free_of_iso n e
  obtain ⟨φ,ha,hb,hφ⟩ := exists_integral_separating_regular_dual hi
    (s.image Additive.ofMul) (by
      intro x hx
      obtain ⟨χ,hχ,rfl⟩ := Finset.mem_image.mp hx
      exact hs χ hχ)
  obtain ⟨c,hc⟩ := exists_cocharacter_realizing_characterFunctional T ⟨n,⟨e⟩⟩ φ.toAddMonoidHom
  have heq (χ : TorusWeight T) : characterCocharacterPairing T c (Additive.ofMul χ) =
      φ (Additive.ofMul χ) :=
    (weightCocharacterEquation_existsUnique T χ c).unique
      (characterCocharacterPairing_spec T χ c) (hc χ)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [heq]; exact ha
  · rw [heq]; exact hb
  · intro χ hχ
    rw [heq]
    exact hφ _ (Finset.mem_image.mpr ⟨χ,hχ,rfl⟩)
/-- The source cocharacter separates two distinct actual connected character
kernels, avoiding every member of the supplied finite set of nontrivial
characters. No root-system realization is assumed. -/
theorem exists_cocharacter_of_distinct_connectedKernels
    (T : ClosedSubgroup G) (hT : IsSubtorus T) (S Q : ClosedSubgroup G)
    (α β : TorusWeight T) (hα : α ≠ 1) (hβ : β ≠ 1)
    (hS : α.ambientConnectedKernel T = S)
    (hQ : β.ambientConnectedKernel T = Q) (hSQ : S ≠ Q)
    (s : Finset (TorusWeight T)) (hs : ∀ χ ∈ s, χ ≠ 1) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      0 < characterCocharacterPairing T c (Additive.ofMul α) ∧
      characterCocharacterPairing T c (Additive.ofMul β) < 0 ∧
      ∀ χ ∈ s, characterCocharacterPairing T c (Additive.ofMul χ) ≠ 0 := by
  apply exists_cocharacter_separating_weights T hT α β _ s hs
  apply characters_independent_of_connectedKernel_ne hT.isConnected α β hα hβ
  intro he
  apply hSQ
  rw [← hS, ← hQ]
  unfold TorusCharacter.ambientConnectedKernel
  rw [he]
end Cocharacters
end Theory.AlgebraicGroup.Bor1.SeparatingBorel

