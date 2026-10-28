module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeSpaceQuotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair

/-!
# The binary-four plane-overgroup quotient

The middle 2+2 parabolic has diagonal quotient S₃ × S₃ and hence
three-rank at least two. A subgroup of three-rank one lying two strict
steps above the specified Sylow must therefore be an end parabolic.
Its intrinsic two-core quotient is GL₃(2), and it is maximal. The final
transport handles both GL₄(2) and GL₅(2) through the given two-group
kernel, as required by the original degree-four plane join in 12.9.7.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.862.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions SmallParabolicLevi SmallParabolicLevi.TwoNodes

private instance (d : ℕ) : Finite (LinearGroup d) :=
  Finite.of_injective (fun g : LinearGroup d => (g : Space d → Space d)) DFunLike.coe_injective

private theorem singleton_stabilizer (b : Basis 3) (i : Fin 3) :
    cutStabilizer b {i} = parabolic (cutSpace b i) := by
  ext g
  simp only [mem_cutStabilizer,Set.mem_singleton_iff,forall_eq]
  rfl

private theorem middle_rank (b : Basis 3) :
    2 ≤ primeRank 3 (cutStabilizer b ({1} : Set (Fin 3))) := by
  let W := cutSpace b (1 : Fin 3)
  have hd : Module.finrank (ZMod 2) W = 2 := cutSpace_finrank b 1
  have hq : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 2 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hd,Module.finrank_fin_fun] at hh
    change Module.finrank (ZMod 2) (Space 4 ⧸ W) + 2 = 4 at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let c : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  let e := (quotientTwoCoreEquivOfCoordinates W a c).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  rw [singleton_stabilizer,←primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (parabolic W)) pCore_isPGroup,primeRank_equiv 3 e,primeRank_prod_eq_add]
  have hn : primeRank 3 (Equiv.Perm (Fin 3)) ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [Nat.card_perm,Nat.card_fin] at hh
    exact hh (by decide)
  omega

private def four_point_quotient (b : Basis 3) :
    (cutStabilizer b ({0} : Set (Fin 3)) ⧸ pCore 2 (cutStabilizer b {0})) ≃*
      LinearGroup 3 := by
  let W := cutSpace b (0 : Fin 3)
  have hd : Module.finrank (ZMod 2) W = 1 := cutSpace_finrank b 0
  have hq : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 3 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hd,Module.finrank_fin_fun] at hh
    change Module.finrank (ZMod 2) (Space 4 ⧸ W) + 1 = 4 at hh
    omega
  let a : W ≃ₗ[ZMod 2] Space 1 := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let c : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space 3 := LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  let e := quotientTwoCoreEquivOfCoordinates W a c
  have hsub : Subsingleton (LinearGroup 1) := by
    apply Finite.card_le_one_iff_subsingleton.mp
    have hc : Nat.card (LinearGroup 1) = 1 := by
      rw [←Nat.card_congr (matrixEquivLinear 1).toEquiv,Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    omega
  let f : LinearGroup 1 × LinearGroup 3 →* LinearGroup 3 := MonoidHom.snd _ _
  have hf : Function.Bijective f := by
    let := hsub
    exact ⟨fun x y he => Prod.ext (Subsingleton.elim _ _) he,fun x => ⟨(1,x),rfl⟩⟩
  let h := singleton_stabilizer b 0
  exact (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr h) (pCore_map_iso 2 _)).trans
    (e.trans (MulEquiv.ofBijective f hf))

private theorem singleton_coatom (S : Sylow 2 (LinearGroup 4))
    (b : Basis 3) (hb : (S : Subgroup _) = cutStabilizer b Set.univ) (i : Fin 3) :
    IsCoatom (cutStabilizer b {i}) := by
  have ht : cutStabilizer b ∅ = ⊤ := by
    ext x
    simp only [mem_cutStabilizer,Set.mem_empty_iff_false,forall_false,forall_const,mem_top]
  have hSQ : (S : Subgroup _) ≤ cutStabilizer b {i} := by
    rw [hb]
    exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
  constructor
  · intro he
    have hi := (cutStabilizer_le_iff b ∅ {i}).mp (by rw [ht,he])
    exact hi (Set.mem_singleton i)
  · intro R hR
    obtain ⟨t,rfl⟩ := overgroup_eq_cutStabilizer S b hb R (hSQ.trans hR.le)
    have hti := (cutStabilizer_le_iff b _ _).mp hR.le
    have hi : i ∉ t := by
      intro hi
      have he : t = {i} := Set.Subset.antisymm hti (Set.singleton_subset_iff.mpr hi)
      exact hR.ne (congrArg (cutStabilizer b) he.symm)
    have he : t = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun j hj => hi ((hti hj) ▸ hj))
    rw [he,ht]

/-- The four-dimensional ambient group gives the same intrinsic three-space quotient. -/
theorem four_quotient_and_coatom_of_chain
    (S : Sylow 2 (LinearGroup 4)) (P Q : Subgroup (LinearGroup 4))
    (hSP : (S : Subgroup _) < P) (hPQ : P < Q) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty ((Q ⧸ pCore 2 Q) ≃* LinearGroup 3) ∧ IsCoatom Q := by
  classical
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨s,rfl⟩ := overgroup_eq_cutStabilizer S b hb P hSP.le
  obtain ⟨t,rfl⟩ := overgroup_eq_cutStabilizer S b hb Q (hSP.le.trans hPQ.le)
  have hnot : ¬ t ⊆ ({1} : Set (Fin 3)) := by
    intro he
    have hh := (middle_rank b).trans ((primeRank_mono 3
      ((cutStabilizer_le_iff b _ _).mpr he)).trans hQ)
    omega
  have hst : t ⊂ s := ⟨(cutStabilizer_le_iff b _ _).mp hPQ.le,fun he =>
    hPQ.not_ge ((cutStabilizer_le_iff b _ _).mpr he)⟩
  have hs : s ≠ Set.univ := by
    intro he
    exact hSP.ne (by rw [he,←hb])
  have patterns : ∀ s t : Finset (Fin 3), t ⊂ s → s ≠ Finset.univ →
      ¬ t ⊆ {1} → t = {0} ∨ t = {2} := by decide +kernel
  have ht := patterns s.toFinset t.toFinset (by simpa using hst)
    (by simpa using hs) (by
      intro he
      apply hnot
      intro k hk
      have hm := he (Set.mem_toFinset.mpr hk)
      simpa only [Finset.mem_singleton,Set.mem_singleton_iff] using hm)
  rcases ht with ht | ht
  · have he : t = ({0} : Set (Fin 3)) := by
      ext j; simpa using congrArg (fun a : Finset (Fin 3) => j ∈ a) ht
    subst t
    exact ⟨⟨four_point_quotient b⟩,singleton_coatom S b hb 0⟩
  · have he : t = ({0,1} : Set (Fin 3))ᶜ := by
      ext j
      have hj := congrArg (fun a : Finset (Fin 3) => j ∈ a) ht
      fin_cases j <;> simpa using hj
    subst t
    refine ⟨⟨(OrderedResidualConjugators.four_head_quotient b).trans (slEquivLinear 3)⟩,?_⟩
    have he : ({0,1} : Set (Fin 3))ᶜ = {2} := by ext j; fin_cases j <;> decide
    rw [he]
    exact singleton_coatom S b hb 2

/-- The intrinsic two-core quotient in ambient dimension four. -/
theorem four_quotient_linearThree_of_chain
    (S : Sylow 2 (LinearGroup 4)) (P Q : Subgroup (LinearGroup 4))
    (hSP : (S : Subgroup _) < P) (hPQ : P < Q) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty ((Q ⧸ pCore 2 Q) ≃* LinearGroup 3) :=
  (four_quotient_and_coatom_of_chain S P Q hSP hPQ hQ).1

/-- In ambient binary dimension four the same subgroup is maximal, also above a two-kernel. -/
theorem four_coatom_of_two_kernel_chain
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 4) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (P Q : Subgroup H)
    (hSP : (S : Subgroup H) < P) (hPQ : P < Q) (hQ : primeRank 3 Q ≤ 1) :
    IsCoatom Q := by
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
  have hc := (four_quotient_and_coatom_of_chain S' (P.map f) (Q.map f)
    hSP' hPQ' (hr ▸ hQ)).2
  have hc' := isCoatom_comap_of_surjective hf hc
  rwa [comap_map_eq_self (hker.trans (hSP.le.trans hPQ.le))] at hc'

/-- Either binary point model yields the literal three-space quotient. -/
theorem binary_quotient_linearThree_of_two_kernel_chain
    {H : Type*} [Group H] [Finite H] {d : ℕ} (hd : d = 4 ∨ d = 5)
    (f : H →* LinearGroup d) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (P Q : Subgroup H)
    (hSP : (S : Subgroup H) < P) (hPQ : P < Q) (hQ : primeRank 3 Q ≤ 1) :
    Nonempty ((Q ⧸ pCore 2 Q) ≃* LinearGroup 3) := by
  rcases hd with rfl | rfl
  swap
  · exact five_quotient_linearThree_of_two_kernel_chain f hf hk S P Q hSP hPQ hQ
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
  obtain ⟨e⟩ := four_quotient_linearThree_of_chain S' (P.map f) (Q.map f)
    hSP' hPQ' (hr ▸ hQ)
  exact ⟨(g.pCoreQuotientEquiv (f.subgroupMap_surjective Q) hg).trans e⟩

end BinaryLinear.SylowFlagOvergroups
