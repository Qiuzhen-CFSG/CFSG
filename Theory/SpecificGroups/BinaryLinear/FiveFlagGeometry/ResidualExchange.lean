module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MiddleExchange
public import Theory.GroupTheory.PResidual.AbelianQuotient
/-!
# The residual-normalizing node in the binary five-space exchange

Solvability detects the nonadjacent pairs of rank-one parabolics. If an
exchange swaps two such nodes inside a maximal parabolic and fixes its
third node, that third node is nonadjacent to the unique node outside.
Their actual two-core quotient is S₃ × S₃. Subgroup correspondence lifts
the quotient through a two-group kernel, and the abelian-residual argument
makes the pair normalize the embedded two-residual of either node.

Source: Aschbacher--Smith, 10.2.9, printed p.753, the rank-five argument.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic MaximalOvergroups SmallParabolicLevi.TwoNodes
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem middle_adjacent_pair_not_solvable (b : FiveBasis) :
    ¬ Group.IsSolvable (flagStabilizer b ({1,2} : Set (Fin 4))ᶜ) := by
  intro hs
  have hh := flag_block_card_le_two_of_solvable b _ hs 1
  have hlabel : cutLabel ({1,2} : Set (Fin 4))ᶜ = ![0,1,1,1,2] := by
    funext t
    fin_cases t <;> simp [cutLabel,
      show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide,
      Finset.filter_insert, Finset.filter_singleton]
  rw [hlabel] at hh
  have hc : Nat.card (Block ![0,1,1,1,2] 1) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc] at hh
  omega

/-- Solvability detects precisely the nonadjacent pairs of the four nodes. -/
theorem pair_solvable_iff (b : FiveBasis) (i j : Fin 4) (hne : i ≠ j) :
    Group.IsSolvable (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) ↔
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
  constructor
  · intro hs
    by_contra hn
    have hc : j = adjacentNode i ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
      fin_cases i <;> fin_cases j <;> simp_all [adjacentNode]
    rcases hc with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact adjacent_pair_not_solvable b i hs
    · exact middle_adjacent_pair_not_solvable b hs
    · exact middle_adjacent_pair_not_solvable b (by rwa [Set.pair_comm])
  · exact nonadjacent_pair_solvable b i j

private theorem exchange_nodes_combinatorics : ∀ k i j l : Fin 4,
    i ≠ k → j ≠ k → l ≠ k → i ≠ j → i ≠ l → j ≠ l →
    (i.val+1 < j.val ∨ j.val+1 < i.val) →
    ((i.val+1 < l.val ∨ l.val+1 < i.val) ↔
      (j.val+1 < l.val ∨ l.val+1 < j.val)) →
    (k.val+1 < l.val ∨ l.val+1 < k.val) := by decide

/-- The node fixed by a solvable exchange is nonadjacent to the unique
node outside the maximal parabolic. The actual join has Levi quotient S₃². -/
theorem pair_quotient_of_solvable_exchange
    (S : Sylow 2 (LinearGroup 5)) (C A B P F : Subgroup (LinearGroup 5))
    (hSC : (S : Subgroup _) ≤ C) (hC : IsCoatom C)
    (hA : (S : Subgroup _) ⋖ A) (hAC : A ≤ C)
    (hB : (S : Subgroup _) ⋖ B) (hBC : B ≤ C)
    (hP : (S : Subgroup _) ⋖ P) (hPC : P ≤ C)
    (hF : (S : Subgroup _) ⋖ F) (hFC : ¬ F ≤ C)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBP : B ≠ P)
    (hs : Group.IsSolvable (A ⊔ B : Subgroup _))
    (he : Group.IsSolvable (A ⊔ P : Subgroup _) ↔
      Group.IsSolvable (B ⊔ P : Subgroup _)) :
    Nonempty (((P ⊔ F : Subgroup _) ⧸ pCore 2 (P ⊔ F : Subgroup _)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨b,hb⟩ := sylow_eq_flagStabilizer S
  obtain ⟨k,hk⟩ := coatom_eq_singleton_flag b C (hb ▸ hSC) hC
  obtain ⟨i,hi⟩ := (fullFlag_covBy_iff b A).mp (hb ▸ hA)
  obtain ⟨j,hj⟩ := (fullFlag_covBy_iff b B).mp (hb ▸ hB)
  obtain ⟨l,hl⟩ := (fullFlag_covBy_iff b P).mp (hb ▸ hP)
  obtain ⟨n,hn⟩ := (fullFlag_covBy_iff b F).mp (hb ▸ hF)
  have hik : i ≠ k := by
    rw [hi,hk,flag_le_iff] at hAC
    exact fun h => hAC (Set.mem_singleton k) h.symm
  have hjk : j ≠ k := by
    rw [hj,hk,flag_le_iff] at hBC
    exact fun h => hBC (Set.mem_singleton k) h.symm
  have hlk : l ≠ k := by
    rw [hl,hk,flag_le_iff] at hPC
    exact fun h => hPC (Set.mem_singleton k) h.symm
  have hnk : n = k := by
    by_contra h
    apply hFC
    rw [hn,hk,flag_le_iff,Set.singleton_subset_iff]
    exact Ne.symm h
  subst n
  have hij : i ≠ j := fun h => hAB (hi.trans ((congrArg (fun n : Fin 4 => flagStabilizer b {n}ᶜ) h).trans hj.symm))
  have hil : i ≠ l := fun h => hAP (hi.trans ((congrArg (fun n : Fin 4 => flagStabilizer b {n}ᶜ) h).trans hl.symm))
  have hjl : j ≠ l := fun h => hBP (hj.trans ((congrArg (fun n : Fin 4 => flagStabilizer b {n}ᶜ) h).trans hl.symm))
  rw [hi,hj,rankOne_sup_eq_pair,pair_solvable_iff b i j hij] at hs
  rw [hi,hj,hl,rankOne_sup_eq_pair,rankOne_sup_eq_pair,
    pair_solvable_iff b i l hil,pair_solvable_iff b j l hjl] at he
  have hkl := exchange_nodes_combinatorics k i j l hik hjk hlk hij hil hjl hs he
  rw [hl,hn,rankOne_sup_eq_pair]
  exact ⟨(flagDiagonalQuotientEquiv b _).trans (pairFactorsEquiv l k (Or.symm hkl))⟩


/-- The actual two-core quotient of the node pair survives a two-group kernel. -/
theorem pair_quotient_of_solvable_exchange_of_two_kernel
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (C A B P F : Subgroup H)
    (hSC : (S : Subgroup H) ≤ C) (hC : IsCoatom C)
    (hA : (S : Subgroup H) ⋖ A) (hAC : A ≤ C)
    (hB : (S : Subgroup H) ⋖ B) (hBC : B ≤ C)
    (hP : (S : Subgroup H) ⋖ P) (hPC : P ≤ C)
    (hF : (S : Subgroup H) ⋖ F) (hFC : ¬ F ≤ C)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBP : B ≠ P)
    (hs : Group.IsSolvable (A ⊔ B : Subgroup H))
    (he : Group.IsSolvable (A ⊔ P : Subgroup H) ↔
      Group.IsSolvable (B ⊔ P : Subgroup H)) :
    Nonempty (((P ⊔ F : Subgroup H) ⧸ pCore 2 (P ⊔ F : Subgroup H)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
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
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have hs' : Group.IsSolvable (A.map f ⊔ B.map f : Subgroup _) := by
    rw [←Subgroup.map_sup]
    exact (Group.isSolvable_map_iff_of_solvable_ker f _).mpr hs
  have he' : Group.IsSolvable (A.map f ⊔ P.map f : Subgroup _) ↔
      Group.IsSolvable (B.map f ⊔ P.map f : Subgroup _) := by
    rw [←Subgroup.map_sup,←Subgroup.map_sup,
      Group.isSolvable_map_iff_of_solvable_ker,Group.isSolvable_map_iff_of_solvable_ker]
    exact he
  have hFC' : ¬ F.map f ≤ C.map f := by
    intro h
    have hh := comap_mono (f := f) h
    rw [comap_map_eq_self (hker.trans hF.le),comap_map_eq_self hkerC] at hh
    exact hFC hh
  obtain ⟨e⟩ := pair_quotient_of_solvable_exchange (S.mapSurjective hf)
    (C.map f) (A.map f) (B.map f) (P.map f) (F.map f) (map_mono hSC)
    (isCoatom_map_of_surjective_of_ker_le f hf C hkerC hC)
    (cov A hA) (map_mono hAC) (cov B hB) (map_mono hBC)
    (cov P hP) (map_mono hPC) (cov F hF) hFC'
    (fun h => hAB (map_injective_of_ker_le f hkerA hkerB h))
    (fun h => hAP (map_injective_of_ker_le f hkerA hkerP h))
    (fun h => hBP (map_injective_of_ker_le f hkerB hkerP h)) hs' he'
  rw [←Subgroup.map_sup] at e
  have hkJ : IsPGroup 2 (f.subgroupMap (P ⊔ F)).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  exact ⟨((f.subgroupMap (P ⊔ F)).pCoreQuotientEquiv
    (f.subgroupMap_surjective (P ⊔ F)) hkJ).trans e⟩

/-- The pair's full preimage normalizes the literal embedded two-residual. -/
theorem pair_normalizes_residual {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (P F : Subgroup H) (hSP : (S : Subgroup H) ≤ P)
    (e : ((P ⊔ F : Subgroup H) ⧸ pCore 2 (P ⊔ F : Subgroup H)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    P ⊔ F ≤ normalizer ((pResidual 2 P).map P.subtype : Set H) := by
  let J := P ⊔ F
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    have he : q.ker = pCore 2 J := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 J) x) = 1 ↔ x ∈ pCore 2 J
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [he]
    exact pCore_isPGroup
  have hn := residual_normal_of_symmetricThreePair q hq hk
    (S.subtype (hSP.trans le_sup_left)) (P.subgroupOf J) (by
      intro x hx
      exact hSP hx)
  have hle : J ≤ normalizer
      ((((pResidual 2 (P.subgroupOf J)).map (P.subgroupOf J).subtype).map J.subtype) : Set H) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp (by
      change ((Subgroup.map J.subtype _).comap J.subtype).Normal
      rw [comap_map_eq_self_of_injective J.subtype_injective]
      exact hn)
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le (show P ≤ J from le_sup_left)] at hle
  exact hle
end BinaryLinear.FiveFlagGeometry
