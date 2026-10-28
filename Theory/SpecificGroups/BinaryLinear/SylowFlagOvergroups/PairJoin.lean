module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeSpaceQuotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Joining binary rank-two parabolics along a rank-one parabolic

Two distinct overgroups of a full Sylow two-subgroup in GL₅(2), each of
three-rank at most one and each lying strictly above a common proper Sylow
overgroup, generate an endpoint parabolic. Indeed their omitted flag cuts
are adjacent pairs; the common strict overgroup excludes disjoint pairs.
The diagonal action on the resulting four-space block identifies the join
modulo its intrinsic two-core with GL₄(2). The last theorem transports this
calculation through any specified surjection with two-group kernel.

The original mixed point row of 12.9.7 uses this with Y and L₁T, retaining
their common last-node parabolic. Source: Aschbacher--Smith,
refs/quasithin.pdf, printed p.862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions SmallParabolicLevi SmallParabolicLevi.TwoNodes

private instance (d : ℕ) : Finite (LinearGroup d) :=
  Finite.of_injective (fun g : LinearGroup d => (g : Space d → Space d)) DFunLike.coe_injective

private theorem nonadjacent_rank' (b : Basis 4) (i j : Fin 4)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    2 ≤ primeRank 3 (cutStabilizer b ({i,j} : Set (Fin 4))ᶜ) := by
  change 2 ≤ primeRank 3 (FiveFlagGeometry.flagStabilizer b ({i,j} : Set (Fin 4))ᶜ)
  let e := (flagDiagonalQuotientEquiv b ({i,j} : Set (Fin 4))ᶜ).trans
    (pairFactorsEquiv i j hij)
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (FiveFlagGeometry.flagStabilizer b ({i,j} : Set (Fin 4))ᶜ)) pCore_isPGroup,
    primeRank_equiv 3 e, primeRank_prod_eq_add]
  have hn : primeRank 3 (Equiv.Perm (Fin 3)) ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [Nat.card_perm,Nat.card_fin] at hh
    exact hh (by decide)
  omega

private theorem chain_cuts (S : Sylow 2 (LinearGroup 5)) (b : Basis 4)
    (hb : (S : Subgroup _) = cutStabilizer b Set.univ)
    (J : Subgroup (LinearGroup 5)) (s : Set (Fin 4))
    (hSJ : (S : Subgroup _) < J) (hJs : J < cutStabilizer b s)
    (hr : primeRank 3 (cutStabilizer b s) ≤ 1) :
    s = {2,3} ∨ s = {0,3} ∨ s = {0,1} := by
  classical
  obtain ⟨t,rfl⟩ := overgroup_eq_cutStabilizer S b hb J hSJ.le
  have hnear (i j : Fin 4) (hi : i ∉ s) (hj : j ∉ s) :
      ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
    intro h
    have hle : cutStabilizer b ({i,j} : Set (Fin 4))ᶜ ≤ cutStabilizer b s := by
      apply (cutStabilizer_le_iff b _ _).mpr
      intro k hk
      simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
      exact ⟨fun he => hi (he ▸ hk),fun he => hj (he ▸ hk)⟩
    have hh := (nonadjacent_rank' b i j h).trans ((primeRank_mono 3 hle).trans hr)
    omega
  have hst : s ⊂ t := ⟨(cutStabilizer_le_iff b _ _).mp hJs.le,fun he =>
    hJs.not_ge ((cutStabilizer_le_iff b _ _).mpr he)⟩
  have ht : t ≠ Set.univ := by
    intro he
    exact hSJ.ne (by rw [he,←hb])
  have patterns : ∀ s t : Finset (Fin 4), s ⊂ t → t ≠ Finset.univ →
      (∀ i j : Fin 4, i ∉ s → j ∉ s →
        ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val)) →
      s = {2,3} ∨ s = {0,3} ∨ s = {0,1} := by decide +kernel
  have hs := patterns s.toFinset t.toFinset (by simpa using hst)
    (by simpa using ht) (by simpa using hnear)
  rcases hs with hs | hs | hs
  · exact Or.inl (by ext j; simpa using congrArg (fun a : Finset (Fin 4) => j ∈ a) hs)
  · exact Or.inr (Or.inl (by ext j; simpa using congrArg (fun a : Finset (Fin 4) => j ∈ a) hs))
  · exact Or.inr (Or.inr (by ext j; simpa using congrArg (fun a : Finset (Fin 4) => j ∈ a) hs))

private def endCuts (i : Fin 2) : Set (Fin 4) := ![{0},{3}] i
private def largeBlock (i : Fin 2) : Fin 5 := ![1,0] i
private theorem end_label (i : Fin 2) :
    cutLabel (endCuts i) = ![![0,1,1,1,1],![0,0,0,0,1]] i := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [endCuts,cutLabel,hu,Finset.filter_insert,Finset.filter_singleton]
private theorem large_card (i : Fin 2) :
    Fintype.card (Block (cutLabel (endCuts i)) (largeBlock i)) = 4 := by
  classical
  have hu : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  simp only [Block,Fintype.card_subtype]
  fin_cases i <;> simp [end_label,largeBlock,hu,Finset.filter_insert,Finset.filter_singleton]
private theorem other_card (i : Fin 2) (k : Fin 5) (hk : k ≠ largeBlock i) :
    Fintype.card (Block (cutLabel (endCuts i)) k) ≤ 1 := by
  classical
  have hu : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  simp only [Block,Fintype.card_subtype]
  fin_cases i <;> fin_cases k <;>
    simp_all [end_label,largeBlock,Finset.filter_insert,Finset.filter_singleton]
private def endFactorsEquiv (i : Fin 2) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel (endCuts i)) k)) ≃*
      LinearGroup 4 := by
  classical
  let f := Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace (cutLabel (endCuts i)) k)) (largeBlock i)
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      funext j
      by_cases hj : j = largeBlock i
      · subst j; exact he
      exact (linearBlock_eq_one_of_card_le_one _ _ (other_card i j hj) (a j)).trans
        (linearBlock_eq_one_of_card_le_one _ _ (other_card i j hj) (b j)).symm
    · intro a
      exact ⟨Function.update 1 (largeBlock i) a,Function.update_self ..⟩
  let c : BlockSpace (cutLabel (endCuts i)) (largeBlock i) ≃ₗ[ZMod 2] Space 4 :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
      ((Fintype.equivFin (Block (cutLabel (endCuts i)) (largeBlock i))).trans
        (finCongr (large_card i))).symm
  exact (MulEquiv.ofBijective f hf).trans (linearGroupCongr c)

/-- Two distinct cubic-rank-one rank-two parabolics sharing a rank-one
parabolic generate an endpoint parabolic with intrinsic quotient GL₄(2). -/
theorem five_pair_join_quotient_linearFour
    (S : Sylow 2 (LinearGroup 5)) (J P Q : Subgroup (LinearGroup 5))
    (hSJ : (S : Subgroup _) < J) (hJP : J < P) (hJQ : J < Q)
    (hne : P ≠ Q) (hP : primeRank 3 P ≤ 1) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty (((P ⊔ Q : Subgroup _) ⧸ pCore 2 (P ⊔ Q : Subgroup _)) ≃* LinearGroup 4) := by
  classical
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨s,rfl⟩ := overgroup_eq_cutStabilizer S b hb P (hSJ.le.trans hJP.le)
  obtain ⟨t,rfl⟩ := overgroup_eq_cutStabilizer S b hb Q (hSJ.le.trans hJQ.le)
  have hs := chain_cuts S b hb J s hSJ hJP hP
  have ht := chain_cuts S b hb J t hSJ hJQ hQ
  have hst : s ≠ t := fun he => hne (congrArg (cutStabilizer b) he)
  have hunion : s ∪ t ≠ Set.univ := by
    intro he
    have hh : J ≤ cutStabilizer b (s ∪ t) := by
      intro g hg
      rw [mem_cutStabilizer]
      intro i hi
      exact hi.elim (fun hi => ((mem_cutStabilizer b s g).mp (hJP.le hg)) i hi)
        (fun hi => ((mem_cutStabilizer b t g).mp (hJQ.le hg)) i hi)
    rw [he,←hb] at hh
    exact hSJ.not_ge hh
  have hp : ∃ i : Fin 2, s ∩ t = endCuts i := by
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · exact (hst rfl).elim
    · exact ⟨1,by ext j; fin_cases j <;> simp [endCuts]⟩
    · exact (hunion (by ext j; fin_cases j <;> decide)).elim
    · exact ⟨1,by ext j; fin_cases j <;> simp [endCuts]⟩
    · exact (hst rfl).elim
    · exact ⟨0,by ext j; fin_cases j <;> simp [endCuts]⟩
    · exact (hunion (by ext j; fin_cases j <;> decide)).elim
    · exact ⟨0,by ext j; fin_cases j <;> simp [endCuts]⟩
    · exact (hst rfl).elim
  have hjoin : cutStabilizer b s ⊔ cutStabilizer b t = cutStabilizer b (s ∩ t) := by
    obtain ⟨r,hr⟩ := overgroup_eq_cutStabilizer S b hb
      (cutStabilizer b s ⊔ cutStabilizer b t) ((hSJ.le.trans hJP.le).trans le_sup_left)
    apply le_antisymm
    · exact sup_le ((cutStabilizer_le_iff b _ _).mpr Set.inter_subset_left)
        ((cutStabilizer_le_iff b _ _).mpr Set.inter_subset_right)
    · rw [hr]
      exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_inter
        ((cutStabilizer_le_iff b _ _).mp (le_sup_left.trans_eq hr))
        ((cutStabilizer_le_iff b _ _).mp (le_sup_right.trans_eq hr)))
  obtain ⟨i,hi⟩ := hp
  let e := MulEquiv.subgroupCongr (hjoin.trans (congrArg (cutStabilizer b) hi))
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((flagDiagonalQuotientEquiv b _).trans (endFactorsEquiv i))⟩

/-- The pair-join quotient through a specified two-group kernel. -/
theorem five_pair_join_quotient_of_two_kernel
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (J P Q : Subgroup H)
    (hSJ : (S : Subgroup H) < J) (hJP : J < P) (hJQ : J < Q)
    (hne : P ≠ Q) (hP : primeRank 3 P ≤ 1) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty (((P ⊔ Q : Subgroup H) ⧸ pCore 2 (P ⊔ Q : Subgroup H)) ≃* LinearGroup 4) := by
  let S' := S.mapSurjective hf
  have hker := hk.le_sylow_of_normal S
  have hstrict {A B : Subgroup H} (hSA : (S : Subgroup H) ≤ A) (hAB : A < B) :
      A.map f < B.map f := lt_of_le_of_ne (map_mono hAB.le)
    (fun he => hAB.ne (map_injective_of_ker_le f (hker.trans hSA)
      (hker.trans (hSA.trans hAB.le)) he))
  have hr (A : Subgroup H) : primeRank 3 (A.map f) = primeRank 3 A := by
    let g := f.subgroupMap A
    have hg : IsPGroup 2 g.ker := by
      change IsPGroup 2 (f.subgroupMap A).ker
      rw [ker_subgroupMap]
      exact hk.comap_subtype
    symm
    apply primeRank_eq_of_surjective_of_coprime 3 g (f.subgroupMap_surjective A)
    obtain ⟨k,hk⟩ := hg.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hneq : P.map f ≠ Q.map f := fun he => hne
    (map_injective_of_ker_le f (hker.trans (hSJ.le.trans hJP.le))
      (hker.trans (hSJ.le.trans hJQ.le)) he)
  obtain ⟨e⟩ := five_pair_join_quotient_linearFour S' (J.map f) (P.map f) (Q.map f)
    (hstrict le_rfl hSJ) (hstrict hSJ.le hJP) (hstrict hSJ.le hJQ) hneq
    (by rw [hr]; exact hP) (by rw [hr]; exact hQ)
  rw [←Subgroup.map_sup] at e
  let g := f.subgroupMap (P ⊔ Q)
  have hg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.subgroupMap (P ⊔ Q)).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  exact ⟨(g.pCoreQuotientEquiv (f.subgroupMap_surjective _) hg).trans e⟩

end BinaryLinear.SylowFlagOvergroups
