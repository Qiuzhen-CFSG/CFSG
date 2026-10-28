module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeRankOne
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Adjacent
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Three-space quotients of cubic-rank-one Sylow overgroups

In GL₅(2), a subgroup of three-rank at most one cannot delete two
nonadjacent cuts of its Sylow flag: their diagonal quotient is S₃ × S₃.
Two strict inclusions above the Sylow force exactly two adjacent deletions.
Projection to the resulting three-dimensional block identifies the intrinsic
two-core quotient with GL₃(2), including the middle pair of nodes.
The final theorem transports the calculation through a specified surjection
with two-group kernel, retaining the actual subgroups and intrinsic cores.

The consumer is the original escaping plane join in degree four of 12.9.7.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions SmallParabolicLevi SmallParabolicLevi.TwoNodes

private instance (d : ℕ) : Finite (LinearGroup d) :=
  Finite.of_injective (fun g : LinearGroup d => (g : Space d → Space d)) DFunLike.coe_injective

private theorem nonadjacent_rank (b : Basis 4) (i j : Fin 4)
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

private def tripleCuts (i : Fin 3) : Set (Fin 4) := ![{2,3},{0,3},{0,1}] i

private theorem triple_label (i : Fin 3) :
    cutLabel (tripleCuts i) = ![![0,0,0,1,2],![0,1,1,1,2],![0,1,2,2,2]] i := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [tripleCuts,cutLabel,hu,Finset.filter_insert,Finset.filter_singleton]

private theorem triple_block_card (i : Fin 3) :
    Fintype.card (Block (cutLabel (tripleCuts i)) (i.castLE (by decide))) = 3 := by
  classical
  have hu : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  simp only [Block,Fintype.card_subtype]
  fin_cases i <;> simp [triple_label,hu,Finset.filter_insert,Finset.filter_singleton]

private theorem triple_other_card (i : Fin 3) (k : Fin 5)
    (hk : k ≠ i.castLE (by decide)) :
    Fintype.card (Block (cutLabel (tripleCuts i)) k) ≤ 1 := by
  classical
  have hu : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  simp only [Block,Fintype.card_subtype]
  fin_cases i <;> fin_cases k <;>
    simp_all [triple_label,Finset.filter_insert,Finset.filter_singleton]

private def tripleFactorsEquiv (i : Fin 3) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel (tripleCuts i)) k)) ≃*
      LinearGroup 3 := by
  classical
  let k : Fin 5 := i.castLE (by decide)
  let f := Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace (cutLabel (tripleCuts i)) k)) k
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      funext j
      by_cases hj : j = k
      · subst j; exact he
      exact (linearBlock_eq_one_of_card_le_one _ _ (triple_other_card i j hj) (a j)).trans
        (linearBlock_eq_one_of_card_le_one _ _ (triple_other_card i j hj) (b j)).symm
    · intro a
      exact ⟨Function.update 1 k a,Function.update_self ..⟩
  let c : BlockSpace (cutLabel (tripleCuts i)) k ≃ₗ[ZMod 2] Space 3 :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
      ((Fintype.equivFin (Block (cutLabel (tripleCuts i)) k)).trans
        (finCongr (triple_block_card i))).symm
  exact (MulEquiv.ofBijective f hf).trans (linearGroupCongr c)

/-- Two strict Sylow inclusions and cubic rank one force the genuine GL₃(2) quotient. -/
theorem five_quotient_linearThree_of_chain
    (S : Sylow 2 (LinearGroup 5)) (P Q : Subgroup (LinearGroup 5))
    (hSP : (S : Subgroup _) < P) (hPQ : P < Q) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty ((Q ⧸ pCore 2 Q) ≃* LinearGroup 3) := by
  classical
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨s,rfl⟩ := overgroup_eq_cutStabilizer S b hb P hSP.le
  obtain ⟨t,rfl⟩ := overgroup_eq_cutStabilizer S b hb Q (hSP.le.trans hPQ.le)
  have hnear (i j : Fin 4) (hi : i ∉ t) (hj : j ∉ t) :
      ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
    intro h
    have hle : cutStabilizer b ({i,j} : Set (Fin 4))ᶜ ≤ cutStabilizer b t := by
      apply (cutStabilizer_le_iff b _ _).mpr
      intro k hk
      simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
      exact ⟨fun he => hi (he ▸ hk),fun he => hj (he ▸ hk)⟩
    have hh := (nonadjacent_rank b i j h).trans ((primeRank_mono 3 hle).trans hQ)
    omega
  have hst : t ⊂ s := ⟨(cutStabilizer_le_iff b _ _).mp hPQ.le,fun he =>
    hPQ.not_ge ((cutStabilizer_le_iff b _ _).mpr he)⟩
  have hs : s ≠ Set.univ := by
    intro he
    exact hSP.ne (by rw [he,←hb])
  have patterns : ∀ s t : Finset (Fin 4), t ⊂ s → s ≠ Finset.univ →
      (∀ i j : Fin 4, i ∉ t → j ∉ t →
        ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val)) →
      t = {2,3} ∨ t = {0,3} ∨ t = {0,1} := by decide +kernel
  have ht : ∃ i : Fin 3, t = tripleCuts i := by
    have hp := patterns s.toFinset t.toFinset (by simpa using hst)
      (by simpa using hs) (by simpa using hnear)
    rcases hp with hp | hp | hp
    · exact ⟨0,by ext j; simpa [tripleCuts] using congrArg (fun a : Finset (Fin 4) => j ∈ a) hp⟩
    · exact ⟨1,by ext j; simpa [tripleCuts] using congrArg (fun a : Finset (Fin 4) => j ∈ a) hp⟩
    · exact ⟨2,by ext j; simpa [tripleCuts] using congrArg (fun a : Finset (Fin 4) => j ∈ a) hp⟩
  obtain ⟨i,rfl⟩ := ht
  exact ⟨(flagDiagonalQuotientEquiv b _).trans (tripleFactorsEquiv i)⟩

/-- The original three-space quotient survives any specified two-group kernel. -/
theorem five_quotient_linearThree_of_two_kernel_chain
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (P Q : Subgroup H)
    (hSP : (S : Subgroup H) < P) (hPQ : P < Q) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty ((Q ⧸ pCore 2 Q) ≃* LinearGroup 3) := by
  let S' := S.mapSurjective hf
  have hker := hk.le_sylow_of_normal S
  have hSP' : (S' : Subgroup _) < P.map f := lt_of_le_of_ne (map_mono hSP.le)
    (fun he => hSP.ne (map_injective_of_ker_le f hker (hker.trans hSP.le) he))
  have hPQ' : P.map f < Q.map f := lt_of_le_of_ne (map_mono hPQ.le)
    (fun he => hPQ.ne (map_injective_of_ker_le f (hker.trans hSP.le)
      (hker.trans (hSP.le.trans hPQ.le)) he))
  let g := f.subgroupMap Q
  have hg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.subgroupMap Q).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hr : primeRank 3 (Q.map f) = primeRank 3 Q := by
    symm
    apply primeRank_eq_of_surjective_of_coprime 3 g (f.subgroupMap_surjective Q)
    obtain ⟨k,hk⟩ := hg.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  obtain ⟨e⟩ := five_quotient_linearThree_of_chain S' (P.map f) (Q.map f)
    hSP' hPQ' (hr ▸ hQ)
  exact ⟨(g.pCoreQuotientEquiv (f.subgroupMap_surjective Q) hg).trans e⟩

end BinaryLinear.SylowFlagOvergroups
