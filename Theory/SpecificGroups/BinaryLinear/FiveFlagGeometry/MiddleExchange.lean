module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneExchange
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.GroupTheory.SolvableMutualCommutator
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Adjacent
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.SL3.BinaryPointStabilizer
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.SolvableFlags
/-!
# The exchange obstruction in a middle binary five-space parabolic

The quotient by the two-core of a middle parabolic has order 1008.
Among its three rank-one nodes exactly one pair has nonsolvable join:
its adjacent pair has quotient SL₃(2), while each other pair has quotient
S₃ × S₃. An exchange of two nodes with solvable join cannot fix the third
node, since it would identify a solvable join with a nonsolvable one.
The obstruction lifts through a two-group kernel by subgroup correspondence
and solvability of extensions, with the actual Sylow and joins retained.

Source: Aschbacher--Smith, 10.2.9, printed p.753, the rank-ten contradiction.
-/

public section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic MaximalOvergroups SmallParabolicLevi.TwoNodes
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

/-- Nonadjacent rank-one binary nodes have solvable join. -/
theorem nonadjacent_pair_solvable (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Group.IsSolvable (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) := by
  let Q := flagStabilizer b ({i,j} : Set (Fin 4))ᶜ
  let e := (flagDiagonalQuotientEquiv b _).trans (pairFactorsEquiv i j h)
  let := symmetricThree_solvable
  let : Group.IsSolvable (Q ⧸ pCore 2 Q) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 Q) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 Q)).mpr ⟨inferInstance,inferInstance⟩

/-- Each outer adjacent pair has its actual nonsolvable SL₃(2) quotient. -/
theorem adjacent_pair_not_solvable (b : FiveBasis) (i : Fin 4) :
    ¬ Group.IsSolvable (flagStabilizer b ({i,adjacentNode i} : Set (Fin 4))ᶜ) := by
  intro hs
  let := hs
  let e := adjacentQuotientEquiv b i
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsSolvable (LinearGroup 3) :=
    Group.isSolvable_of_surjective (f := (slEquivLinear 3).toMonoidHom) (slEquivLinear 3).surjective
  let : Group.IsPerfect (LinearGroup 3) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Nontrivial (LinearGroup 3) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [←Nat.card_congr (slEquivLinear 3).toEquiv,NaturalThreePoint.group_card]
    decide)
  exact Group.IsPerfect.not_isSolvable (LinearGroup 3) inferInstance

/-- In either middle parabolic the only nonsolvable pair is its adjacent pair. -/
theorem middle_pair_solvable_iff (b : FiveBasis) (k i j : Fin 4)
    (hk : k = 1 ∨ k = 2) (hi : i ≠ k) (hj : j ≠ k) (hij : i ≠ j) :
    Group.IsSolvable (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) ↔
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
  constructor
  · intro hs
    by_contra hn
    have he : j = adjacentNode i := by
      rcases hk with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
        simp_all [adjacentNode]
    subst j
    exact adjacent_pair_not_solvable b i hs
  · exact nonadjacent_pair_solvable b i j

private theorem middle_nodes_combinatorics : ∀ k i j l : Fin 4,
    (k = 1 ∨ k = 2) → i ≠ k → j ≠ k → l ≠ k →
    i ≠ j → i ≠ l → j ≠ l →
    (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
    ¬ ((i.val + 1 < l.val ∨ l.val + 1 < i.val) ↔
       (j.val + 1 < l.val ∨ l.val + 1 < j.val)) := by decide

/-- Exchanging two nodes with solvable join cannot preserve the solvability
of their joins with the third node in a middle parabolic. -/
theorem middle_nodes_no_solvable_exchange (b : FiveBasis) (k i j l : Fin 4)
    (hk : k = 1 ∨ k = 2) (hi : i ≠ k) (hj : j ≠ k) (hl : l ≠ k)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hs : Group.IsSolvable (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ))
    (he : Group.IsSolvable (flagStabilizer b ({i,l} : Set (Fin 4))ᶜ) ↔
      Group.IsSolvable (flagStabilizer b ({j,l} : Set (Fin 4))ᶜ)) : False := by
  rw [middle_pair_solvable_iff b k i j hk hi hj hij] at hs
  rw [middle_pair_solvable_iff b k i l hk hi hl hil,
    middle_pair_solvable_iff b k j l hk hj hl hjl] at he
  exact middle_nodes_combinatorics k i j l hk hi hj hl hij hil hjl hs he

private theorem linearGroup_card_formula (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

/-- The actual order 1008 of the two-core quotient recognizes a middle cut. -/
theorem middle_cut_of_quotient_card (b : FiveBasis) (k : Fin 4)
    (hc : Nat.card (flagStabilizer b {k} ⧸ pCore 2 (flagStabilizer b {k})) = 1008) :
    k = 1 ∨ k = 2 := by
  rw [Nat.card_congr (singletonQuotientEquiv b k).toEquiv,Nat.card_prod,
    linearGroup_card_formula,linearGroup_card_formula] at hc
  fin_cases k
  · norm_num at hc
    exact ((by decide : (∏ x : Fin 4, (16 - 2 ^ x.val)) ≠ 1008) hc).elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · norm_num at hc
    norm_num [Fin.prod_univ_succ] at hc

/-- Joining two rank-one nodes deletes both of their cuts. -/
theorem rankOne_sup_eq_pair (b : FiveBasis) (i j : Fin 4) :
    flagStabilizer b {i}ᶜ ⊔ flagStabilizer b {j}ᶜ =
      flagStabilizer b ({i,j} : Set (Fin 4))ᶜ := by
  rw [flag_sup]
  congr 1
  ext k
  simp

/-- No automorphism of a middle parabolic can exchange two nodes with
solvable join while fixing its third node. The stated invariance is exactly
the consequence of an actual subgroup isomorphism on the two joins. -/
theorem no_solvable_exchange_of_quotient_card
    (S : Sylow 2 (LinearGroup 5)) (C A B P : Subgroup (LinearGroup 5))
    (hSC : (S : Subgroup _) ≤ C) (hC : IsCoatom C)
    (hc : Nat.card (C ⧸ pCore 2 C) = 1008)
    (hA : (S : Subgroup _) ⋖ A) (hAC : A ≤ C)
    (hB : (S : Subgroup _) ⋖ B) (hBC : B ≤ C)
    (hP : (S : Subgroup _) ⋖ P) (hPC : P ≤ C)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBP : B ≠ P)
    (hs : Group.IsSolvable (A ⊔ B : Subgroup _))
    (he : Group.IsSolvable (A ⊔ P : Subgroup _) ↔
      Group.IsSolvable (B ⊔ P : Subgroup _)) : False := by
  obtain ⟨b,hb⟩ := sylow_eq_flagStabilizer S
  obtain ⟨k,hk⟩ := coatom_eq_singleton_flag b C (hb ▸ hSC) hC
  have hkm : k = 1 ∨ k = 2 := middle_cut_of_quotient_card b k (by rwa [hk] at hc)
  obtain ⟨i,hi⟩ := (fullFlag_covBy_iff b A).mp (hb ▸ hA)
  obtain ⟨j,hj⟩ := (fullFlag_covBy_iff b B).mp (hb ▸ hB)
  obtain ⟨l,hl⟩ := (fullFlag_covBy_iff b P).mp (hb ▸ hP)
  have hik : i ≠ k := by
    rw [hi,hk,flag_le_iff] at hAC
    exact fun he => hAC (Set.mem_singleton k) he.symm
  have hjk : j ≠ k := by
    rw [hj,hk,flag_le_iff] at hBC
    exact fun he => hBC (Set.mem_singleton k) he.symm
  have hlk : l ≠ k := by
    rw [hl,hk,flag_le_iff] at hPC
    exact fun he => hPC (Set.mem_singleton k) he.symm
  have hij : i ≠ j := fun h => hAB (hi.trans ((congrArg (fun n : Fin 4 =>
    flagStabilizer b {n}ᶜ) h).trans hj.symm))
  have hil : i ≠ l := fun h => hAP (hi.trans ((congrArg (fun n : Fin 4 =>
    flagStabilizer b {n}ᶜ) h).trans hl.symm))
  have hjl : j ≠ l := fun h => hBP (hj.trans ((congrArg (fun n : Fin 4 =>
    flagStabilizer b {n}ᶜ) h).trans hl.symm))
  rw [hi,hj,rankOne_sup_eq_pair] at hs
  rw [hi,hj,hl,rankOne_sup_eq_pair,rankOne_sup_eq_pair] at he
  exact middle_nodes_no_solvable_exchange b k i j l hkm hik hjk hlk hij hil hjl hs he

/-- The middle-parabolic exchange obstruction lifts through any two-group
kernel, retaining the prescribed Sylow and the literal node joins. -/
theorem no_solvable_exchange_of_two_kernel {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (C A B P : Subgroup H)
    (hSC : (S : Subgroup H) ≤ C) (hC : IsCoatom C)
    (hc : Nat.card (C ⧸ pCore 2 C) = 1008)
    (hA : (S : Subgroup H) ⋖ A) (hAC : A ≤ C)
    (hB : (S : Subgroup H) ⋖ B) (hBC : B ≤ C)
    (hP : (S : Subgroup H) ⋖ P) (hPC : P ≤ C)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBP : B ≠ P)
    (hs : Group.IsSolvable (A ⊔ B : Subgroup H))
    (he : Group.IsSolvable (A ⊔ P : Subgroup H) ↔
      Group.IsSolvable (B ⊔ P : Subgroup H)) : False := by
  have hker := hk.le_sylow_of_normal S
  have hkerC := hker.trans hSC
  have hkerA := hker.trans hA.le
  have hkerB := hker.trans hB.le
  have hkerP := hker.trans hP.le
  have cov (X : Subgroup H) (hx : (S : Subgroup H) ⋖ X) :
      (S : Subgroup H).map f ⋖ X.map f := by
    apply (comap_covBy_iff_of_surjective f hf _ _).mp
    rw [comap_map_eq_self hker,comap_map_eq_self (hker.trans hx.le)]
    exact hx
  have hkC : IsPGroup 2 (f.subgroupMap C).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let e := (f.subgroupMap C).pCoreQuotientEquiv (f.subgroupMap_surjective C) hkC
  have hc' : Nat.card (C.map f ⧸ pCore 2 (C.map f)) = 1008 :=
    (Nat.card_congr e.toEquiv).symm.trans hc
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have hs' : Group.IsSolvable (A.map f ⊔ B.map f : Subgroup _) := by
    rw [←Subgroup.map_sup]
    exact (Group.isSolvable_map_iff_of_solvable_ker f _).mpr hs
  have he' : Group.IsSolvable (A.map f ⊔ P.map f : Subgroup _) ↔
      Group.IsSolvable (B.map f ⊔ P.map f : Subgroup _) := by
    rw [←Subgroup.map_sup,←Subgroup.map_sup,
      Group.isSolvable_map_iff_of_solvable_ker,Group.isSolvable_map_iff_of_solvable_ker]
    exact he
  exact no_solvable_exchange_of_quotient_card (S.mapSurjective hf)
    (C.map f) (A.map f) (B.map f) (P.map f) (map_mono hSC)
    (isCoatom_map_of_surjective_of_ker_le f hf C hkerC hC) hc'
    (cov A hA) (map_mono hAC) (cov B hB) (map_mono hBC)
    (cov P hP) (map_mono hPC)
    (fun h => hAB (map_injective_of_ker_le f hkerA hkerB h))
    (fun h => hAP (map_injective_of_ker_le f hkerA hkerP h))
    (fun h => hBP (map_injective_of_ker_le f hkerB hkerP h)) hs' he'
end BinaryLinear.FiveFlagGeometry
