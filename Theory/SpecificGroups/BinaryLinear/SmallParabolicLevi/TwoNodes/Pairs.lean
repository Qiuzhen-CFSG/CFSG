module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags

/-!
# Ordered rank-one blocks at two nonadjacent nodes

The three possible unordered pairs give block sizes 2+2+1, 2+1+2 or 1+2+2.
The original two coordinate positions at each marked node identify its block
with binary two-space. All other blocks have size at most one and trivial
binary general linear group. Projection to the two marked blocks, followed
by their projective-line actions, is therefore an actual equivalence to
S₃ × S₃, in the order supplied by the two nodes.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the rank-two
nonadjacent-node parabolic in 13.8.25, printed p.960 (PDF p.977).
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

noncomputable def pairLabel (i j : Fin 4) : Fin 5 → Fin 5 := cutLabel ({i, j} : Set (Fin 4))ᶜ
noncomputable def nodeLabel (i j : Fin 4) : Fin 5 := pairLabel i j i.castSucc


private theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
private theorem univ_five : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide


private theorem label02 : pairLabel 0 2 = ![0, 0, 1, 1, 2] := by
  funext t
  fin_cases t <;> simp [pairLabel, cutLabel, univ_four, Finset.filter_insert,
    Finset.filter_singleton]
private theorem label03 : pairLabel 0 3 = ![0, 0, 1, 2, 2] := by
  funext t
  fin_cases t <;> simp [pairLabel, cutLabel, univ_four, Finset.filter_insert,
    Finset.filter_singleton]
private theorem label13 : pairLabel 1 3 = ![0, 1, 1, 2, 2] := by
  funext t
  fin_cases t <;> simp [pairLabel, cutLabel, univ_four, Finset.filter_insert,
    Finset.filter_singleton]
private theorem label20 : pairLabel 2 0 = pairLabel 0 2 := by simp only [pairLabel, Set.pair_comm]
private theorem label30 : pairLabel 3 0 = pairLabel 0 3 := by simp only [pairLabel, Set.pair_comm]
private theorem label31 : pairLabel 3 1 = pairLabel 1 3 := by simp only [pairLabel, Set.pair_comm]

theorem nodeLabel_ne (i j : Fin 4) (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    nodeLabel i j ≠ nodeLabel j i := by
  fin_cases i <;> fin_cases j <;> norm_num at h <;>
    simp [nodeLabel, label20, label30, label31, label02, label03, label13]

theorem nodeBlock_iff (i j : Fin 4) (h : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    (t : Fin 5) :
    pairLabel i j t = nodeLabel i j ↔ t = i.castSucc ∨ t = i.succ := by
  fin_cases i <;> fin_cases j <;> norm_num at h <;> fin_cases t <;>
    simp [nodeLabel, label20, label30, label31, label02, label03, label13]

theorem otherBlock_card_le_one (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (k : Fin 5)
    (hki : k ≠ nodeLabel i j) (hkj : k ≠ nodeLabel j i) :
    Fintype.card (Block (pairLabel i j) k) ≤ 1 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases i <;> fin_cases j <;> norm_num at h <;> fin_cases k <;>
    simp_all [nodeLabel, label20, label30, label31, label02, label03, label13,
      univ_five, Finset.filter_insert, Finset.filter_singleton]

end BinaryLinear.SmallParabolicLevi.TwoNodes

namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

theorem pairLabel_comm (i j : Fin 4) : pairLabel j i = pairLabel i j := by
  simp only [pairLabel, Set.pair_comm]

theorem nodeBlock_iff_of_mem (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j)
    (t : Fin 5) : pairLabel i j t = pairLabel i j n.castSucc ↔
      t = n.castSucc ∨ t = n.succ := by
  rcases hn with hi | hj
  · subst n
    exact nodeBlock_iff i j h t
  · subst n
    simpa only [nodeLabel, pairLabel_comm j i] using nodeBlock_iff j i h.symm t

/-- The two coordinates at a marked node, with their original order. -/
noncomputable def nodeIndexEquiv (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j) :
    Fin 2 ≃ Block (pairLabel i j) (pairLabel i j n.castSucc) := by
  let f : Fin 2 → Block (pairLabel i j) (pairLabel i j n.castSucc) := fun r =>
    ⟨if r = 0 then n.castSucc else n.succ,
      (nodeBlock_iff_of_mem i j h n hn _).mpr (by split_ifs <;> simp)⟩
  exact Equiv.ofBijective f ⟨by
    intro r s he
    have hv := congrArg Subtype.val he
    fin_cases r <;> fin_cases s <;> first | rfl | simp [f, Fin.ext_iff] at hv, by
    intro t
    rcases (nodeBlock_iff_of_mem i j h n hn t.val).mp t.property with ht | ht
    · exact ⟨0, Subtype.ext (by simpa [f] using ht.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [f] using ht.symm)⟩⟩

@[simp] theorem nodeIndexEquiv_zero (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j) :
    (nodeIndexEquiv i j h n hn 0).val = n.castSucc := rfl

@[simp] theorem nodeIndexEquiv_one (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j) :
    (nodeIndexEquiv i j h n hn 1).val = n.succ := rfl

/-- Literal ordered coordinates on either of the two rank-one blocks. -/
noncomputable def nodeCoordinates (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j) :
    BlockSpace (pairLabel i j) (pairLabel i j n.castSucc) ≃ₗ[ZMod 2] Space 2 :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (nodeIndexEquiv i j h n hn)

@[simp] theorem nodeCoordinates_apply (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j)
    (v : BlockSpace (pairLabel i j) (pairLabel i j n.castSucc)) (r : Fin 2) :
    nodeCoordinates i j h n hn v r = v (nodeIndexEquiv i j h n hn r) := rfl

/-- A binary block of size at most one has no nonidentity automorphism. -/
theorem linearBlock_eq_one_of_card_le_one (c : Fin 5 → Fin 5) (k : Fin 5)
    (hk : Fintype.card (Block c k) ≤ 1) (g : BinaryLinear.GL (BlockSpace c k)) : g = 1 := by
  let : Subsingleton (Block c k) := Fintype.card_le_one_iff_subsingleton.mp hk
  ext v i
  change g v i = v i
  let w : BlockSpace c k := fun _ => 1
  have hnonzero : g w i ≠ 0 := by
    intro hz
    have he : g w = 0 := by
      funext j
      change g w j = 0
      simpa only [Subsingleton.elim j i] using hz
    have hw := g.injective (he.trans (map_zero g).symm)
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (congrFun hw i)
  have hfix : g w i = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hnonzero
  have hv : v = v i • w := by
    funext j
    simp [w, Subsingleton.elim j i]
  conv_lhs => rw [hv, map_smul]
  change v i * g w i = v i
  rw [hfix, mul_one]

/-- Projection to the two nontrivial blocks of a nonadjacent-node flag. -/
noncomputable def pairProjection (i j : Fin 4) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (pairLabel i j) k)) →*
      BinaryLinear.GL (BlockSpace (pairLabel i j) (pairLabel i j i.castSucc)) ×
      BinaryLinear.GL (BlockSpace (pairLabel i j) (pairLabel i j j.castSucc)) :=
  (Pi.evalMonoidHom _ (pairLabel i j i.castSucc)).prod
    (Pi.evalMonoidHom _ (pairLabel i j j.castSucc))

theorem pairProjection_bijective (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Function.Bijective (pairProjection i j) := by
  have hne : pairLabel i j i.castSucc ≠ pairLabel i j j.castSucc := by
    simpa only [nodeLabel, pairLabel_comm j i] using nodeLabel_ne i j h
  constructor
  · intro a b he
    funext k
    by_cases hki : k = pairLabel i j i.castSucc
    · subst k
      exact congrArg Prod.fst he
    by_cases hkj : k = pairLabel i j j.castSucc
    · subst k
      exact congrArg Prod.snd he
    have hc : Fintype.card (Block (pairLabel i j) k) ≤ 1 :=
      otherBlock_card_le_one i j h k hki (by simpa only [nodeLabel, pairLabel_comm j i] using hkj)
    exact (linearBlock_eq_one_of_card_le_one _ _ hc (a k)).trans
      (linearBlock_eq_one_of_card_le_one _ _ hc (b k)).symm
  · rintro ⟨a, b⟩
    refine ⟨Function.update (Function.update 1 (pairLabel i j i.castSucc) a)
      (pairLabel i j j.castSucc) b, ?_⟩
    apply Prod.ext <;> simp [pairProjection, hne]

/-- Identification of the two ordered geometric blocks with the two S₃ factors. -/
noncomputable def pairFactorsEquiv (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (pairLabel i j) k)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective (pairProjection i j) (pairProjection_bijective i j h)).trans
    (((linearGroupCongr (nodeCoordinates i j h i (Or.inl rfl))).trans
      linearTwoEquivSymmetricThree).prodCongr
     ((linearGroupCongr (nodeCoordinates i j h j (Or.inr rfl))).trans
      linearTwoEquivSymmetricThree))

end BinaryLinear.SmallParabolicLevi.TwoNodes

end
