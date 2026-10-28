module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionThreeModels
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.PrimeRankZero

/-!
# Rank-one centralizers of the marked D.3.10 constituents

Each actual constituent model contains an order-three subgroup normalized
but not centralized by an involution. Use the binary SL₂ pair, embedded on
one symplectic plane or one linear block, and explicit even permutations
for A₆ and A₇. The original rank-two cover then gives three-rank at most
one for the component centralizer, with no prior restriction to SL₃.

In a subgroup of three-rank at most one, a component with order divisible
by three is unique. Cyclic Sylow transfer makes its center prime to three,
so commuting distinct components would have rank at least two. If the
subgroup is normal, uniqueness gives normality in the full ambient group.
The same rank argument excludes its three-core and collapses every actor
orbit of that component. No central cover is replaced by a simple quotient.

The actual application is `SeedAlternativesMovedExhaustionComponentRank`.
These are the centralizer rank and component-normality steps of D.3.14--15;
the three-free component and subsequent module exclusions remain with the
Source325 assembly owner qt-baumann-fsu.
Source: Aschbacher--Smith, printed pp.202 and580.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

private theorem inverted_three_of_pair {H : Type*} [Group H]
    (r t : H) (hr : orderOf r = 3) (ht : orderOf t = 2)
    (hi : t * r * t⁻¹ = r⁻¹) :
    ∃ (J : Subgroup H) (t : H), Nat.card J = 3 ∧ orderOf t = 2 ∧
      t ∈ normalizer (J : Set H) ∧ t ∉ centralizer (J : Set H) := by
  refine ⟨zpowers r,t,by rw [Nat.card_zpowers,hr],ht,?_,?_⟩
  · rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (t * r * t⁻¹) = zpowers r
    rw [hi,zpowers_inv]
  · intro hc
    have he : r = r⁻¹ := by
      calc
        r = t * r * t⁻¹ := by rw [←hc r (mem_zpowers r),mul_inv_cancel_right]
        _ = r⁻¹ := hi
    have hsq : r ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun x => r * x) he).trans (mul_inv_cancel r)
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [hr] at hd
    norm_num at hd

private theorem inverted_three_map {H P : Type*} [Group H] [Group P]
    (f : H →* P) (hf : Function.Injective f)
    (hex : ∃ (J : Subgroup H) (t : H), Nat.card J = 3 ∧ orderOf t = 2 ∧
      t ∈ normalizer (J : Set H) ∧ t ∉ centralizer (J : Set H)) :
    ∃ (J : Subgroup P) (t : P), Nat.card J = 3 ∧ orderOf t = 2 ∧
      t ∈ normalizer (J : Set P) ∧ t ∉ centralizer (J : Set P) := by
  obtain ⟨J,t,hJ,ht,htn,htc⟩ := hex
  refine ⟨J.map f,f t,?_,(orderOf_injective f hf t).trans ht,
    le_normalizer_map f (mem_map_of_mem f htn),?_⟩
  · rwa [card_map_of_injective hf]
  · intro hc
    apply htc
    intro j hj
    apply hf
    simpa only [map_mul] using hc (f j) (mem_map_of_mem f hj)

private def cubicTwo : SL(2,ZMod 2) := ⟨!![0,1;1,1],by decide⟩
private def inverterTwo : SL(2,ZMod 2) := ⟨!![1,1;0,1],by decide⟩
private theorem two_inverted :
    ∃ (J : Subgroup SL(2,ZMod 2)) (t : SL(2,ZMod 2)),
      Nat.card J = 3 ∧ orderOf t = 2 ∧ t ∈ normalizer (J : Set _) ∧
      t ∉ centralizer (J : Set _) :=
  inverted_three_of_pair cubicTwo inverterTwo
    (orderOf_eq_prime (by decide : cubicTwo ^ 3 = 1) (by decide : cubicTwo ≠ 1))
    (orderOf_eq_prime (by decide : inverterTwo ^ 2 = 1) (by decide : inverterTwo ≠ 1))
    (by decide)

/-- The binary SL₂ pair on one hyperbolic plane supplies an inverted cubic in Sp₄. -/
theorem symplecticFour_exists_inverted_three (F : BinaryField) :
    ∃ (J : Subgroup (Matrix.symplecticGroup (Fin 2) F.Carrier))
      (t : Matrix.symplecticGroup (Fin 2) F.Carrier),
      Nat.card J = 3 ∧ orderOf t = 2 ∧ t ∈ normalizer (J : Set _) ∧
      t ∉ centralizer (J : Set _) := by
  let f : SL(2,ZMod 2) →* SL(2,F.Carrier) :=
    Matrix.SpecialLinearGroup.map (algebraMap (ZMod 2) F.Carrier)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    ext i j
    exact (algebraMap (ZMod 2) F.Carrier).injective
      (congrArg (fun a : SL(2,F.Carrier) => a.val i j) he)
  let g := (Theory.SpecificGroups.Symplectic.FundamentalPlane.firstHom (F := F.Carrier) 1).comp
    Theory.SpecificGroups.SymplecticRoot.rankOneEquivSL.symm.toMonoidHom
  have hg : Function.Injective g :=
    (Theory.SpecificGroups.Symplectic.FundamentalPlane.firstHom_injective 1).comp
      Theory.SpecificGroups.SymplecticRoot.rankOneEquivSL.symm.injective
  exact inverted_three_map g hg (inverted_three_map f hf two_inverted)

private def twoBlock (r : ℕ) : SL(2,ZMod 2) →* SL(2+r,ZMod 2) where
  toFun g := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin r) (Fin r) (ZMod 2))), by
      rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
      exact g.property⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 1) = 1
    rw [Matrix.fromBlocks_one]
    exact (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv).map_one
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (g.val * h.val) 0 0 1) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.val 0 0 1) *
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks h.val 0 0 1)
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv]
    congr 1
    simp [Matrix.fromBlocks_multiply]

private theorem twoBlock_injective (r : ℕ) : Function.Injective (twoBlock r) := by
  intro g h he
  have hm := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective (congrArg Subtype.val he)
  apply Subtype.ext
  exact congrArg (fun M => M.submatrix Sum.inl Sum.inl) hm

/-- The same binary SL₂ pair embeds on a literal block in SL₄(2) and SL₅(2). -/
theorem binaryHigher_exists_inverted_three (n : ℕ) (hn : n = 4 ∨ n = 5) :
    ∃ (J : Subgroup SL(n,ZMod 2)) (t : SL(n,ZMod 2)),
      Nat.card J = 3 ∧ orderOf t = 2 ∧ t ∈ normalizer (J : Set _) ∧
      t ∉ centralizer (J : Set _) := by
  rcases hn with rfl | rfl
  · exact inverted_three_map (twoBlock 2) (twoBlock_injective 2) two_inverted
  · exact inverted_three_map (twoBlock 3) (twoBlock_injective 3) two_inverted

private def alternatingCubicSix : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by change Equiv.Perm.sign _ = 1; decide⟩
private def alternatingInverterSix : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by change Equiv.Perm.sign _ = 1; decide⟩
private def alternatingCubicSeven : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by change Equiv.Perm.sign _ = 1; decide⟩
private def alternatingInverterSeven : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by change Equiv.Perm.sign _ = 1; decide⟩

/-- A three-cycle and a double transposition supply the A₆ and separate A₇ witnesses. -/
theorem alternatingSixSeven_exists_inverted_three (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∃ (J : Subgroup (alternatingGroup (Fin n))) (t : alternatingGroup (Fin n)),
      Nat.card J = 3 ∧ orderOf t = 2 ∧ t ∈ normalizer (J : Set _) ∧
      t ∉ centralizer (J : Set _) := by
  rcases hn with rfl | rfl
  · exact inverted_three_of_pair alternatingCubicSix alternatingInverterSix
      (orderOf_eq_prime (by decide : alternatingCubicSix ^ 3 = 1)
        (by decide : alternatingCubicSix ≠ 1))
      (orderOf_eq_prime (by decide : alternatingInverterSix ^ 2 = 1)
        (by decide : alternatingInverterSix ≠ 1)) (by decide)
  · exact inverted_three_of_pair alternatingCubicSeven alternatingInverterSeven
      (orderOf_eq_prime (by decide : alternatingCubicSeven ^ 3 = 1)
        (by decide : alternatingCubicSeven ≠ 1))
      (orderOf_eq_prime (by decide : alternatingInverterSeven ^ 2 = 1)
        (by decide : alternatingInverterSeven ≠ 1)) (by decide)

/-- Every marked constituent has an actual inverted order-three subgroup. -/
theorem constituentModel_exists_inverted_three
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) H E) (hmodel : ConstituentModel ρ) :
    ∃ (J : Subgroup H) (t : H), Nat.card J = 3 ∧ orderOf t = 2 ∧
      t ∈ normalizer (J : Set H) ∧ t ∉ centralizer (J : Set H) := by
  rcases hmodel with hm | hm | hm | hm | hm
  · obtain ⟨F,⟨e⟩⟩ := hm
    exact inverted_three_map e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.injective
      (linearThree_exists_inverted_three F)
  · obtain ⟨F,_,⟨e⟩⟩ := hm
    exact inverted_three_map e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.injective
      (symplecticFour_exists_inverted_three F)
  · obtain ⟨e⟩ := hm
    exact inverted_three_map e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.injective
      (alternatingSixSeven_exists_inverted_three 6 (Or.inl rfl))
  · obtain ⟨n,hn,⟨e⟩⟩ := hm
    exact inverted_three_map e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.injective
      (binaryHigher_exists_inverted_three n hn)
  · obtain ⟨σ,_,⟨e⟩⟩ := hm
    exact inverted_three_map e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.injective
      (alternatingSixSeven_exists_inverted_three 7 (Or.inr rfl))

/-- Transport the model witness through the actual component equivalence and use the original rank-two cover. -/
theorem component_centralizer_three_rank_le_one_of_constituentModel
    {P H A E : Type*} [Group P] [Finite P] [Group H] [Finite H] [Group A]
    [AddCommGroup E] [Module (ZMod 2) E]
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K : Subgroup H) (σ : Representation (ZMod 2) A E) (hm : ConstituentModel σ)
    (e : K ≃* A) :
    primeRank 3 (centralizer (K : Set H)) ≤ 1 := by
  obtain ⟨J,t,hJ,ht,htn,htc⟩ := inverted_three_map e.symm.toMonoidHom e.symm.injective
    (constituentModel_exists_inverted_three σ hm)
  have hc : (t : H) ∉ centralizer (J.map K.subtype : Set H) := by
    intro hc
    apply htc
    intro j hj
    exact Subtype.ext (hc (j : H) (mem_map_of_mem K.subtype hj))
  exact component_centralizer_three_rank_le_one_of_inverted_subgroup f hf hr K
    (J.map K.subtype) (map_subtype_le J)
    ((IsPGroup.of_card (p := 3) (n := 1) (by simpa only [pow_one] using hJ)).map K.subtype)
    t.val t.property ((orderOf_coe t).trans ht)
    (le_normalizer_map K.subtype (mem_map_of_mem K.subtype htn)) hc

private theorem perfect_center_coprime_three
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (hr : primeRank 3 H ≤ 1) : Nat.Coprime 3 (Nat.card (center H)) := by
  let P : Sylow 3 H := default
  let := P.isCyclic_of_odd_of_primeRank_le_one (by decide : Odd 3) hr
  have hh := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (center H)) (by rw [QuotientGroup.ker_mk']) P inferInstance
  rw [QuotientGroup.ker_mk'] at hh
  exact Nat.prime_three.coprime_iff_not_dvd.mpr hh

/-- At most one component with order divisible by three can lie in a subgroup of three-rank at most one. -/
theorem component_unique_in_three_rank_one
    {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) (hr : primeRank 3 C ≤ 1)
    (J D : Subgroup H) (hJ : IsComponent H J) (hD : IsComponent H D)
    (hJC : J ≤ C) (hDC : D ≤ C)
    (hJthree : 3 ∣ Nat.card J) (hDthree : 3 ∣ Nat.card D) : J = D := by
  by_contra hne
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple (J.subgroupOf C) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hJC).symm
  have hcomm : D ≤ centralizer (J : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hJ (Ne.symm hne))
  have hc : D.subgroupOf C ≤ centralizer (J.subgroupOf C : Set C) := by
    intro d hd j hj
    exact Subtype.ext (hcomm hd j.val hj)
  have hcop := perfect_center_coprime_three
    ((primeRank_subgroup_le 3 (J.subgroupOf C)).trans hr)
  have hs := (ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (D.subgroupOf C) (J.subgroupOf C) hc hcop).trans hr
  rw [primeRank_congr 3 (subgroupOfEquivOfLe hDC),
    primeRank_congr 3 (subgroupOfEquivOfLe hJC)] at hs
  have hJn : primeRank 3 J ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hJthree
  have hDn : primeRank 3 D ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hDthree
  omega

/-- Uniqueness inside the normal subgroup gives normality in the full ambient group. -/
theorem component_normal_of_le_normal_three_rank_one
    {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) [C.Normal] (hr : primeRank 3 C ≤ 1)
    (J : Subgroup H) (hJ : IsComponent H J) (hJC : J ≤ C)
    (hJthree : 3 ∣ Nat.card J) : J.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  have hDC : J.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨j,hj,rfl⟩
    exact (inferInstance : C.Normal).conj_mem j (hJC hj) g
  apply (component_unique_in_three_rank_one C hr J _ hJ (hJ.map_conj g)
    hJC hDC hJthree ?_).symm
  rwa [card_map_of_injective (MulAut.conj g).injective]

/-- A component of nonzero three-rank excludes a three-core in the same rank-one subgroup. -/
theorem three_core_eq_bot_of_component_in_rank_one
    {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) (hr : primeRank 3 C ≤ 1)
    (J : Subgroup H) (hJ : IsComponent H J) (hJC : J ≤ C)
    (hJthree : 3 ∣ Nat.card J) : pCore 3 C = ⊥ := by
  let J₀ := J.subgroupOf C
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple J₀ := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hJC).symm
  let : Group.IsNilpotent (pCore 3 C) := pCore_isNilpotent
  have hcomm : pCore 3 C ≤ centralizer (J₀ : Set C) :=
    le_centralizer_iff.mp ((hJ.subgroupOf hJC).le_centralizer_of_solvable_normal (pCore 3 C))
  have hcop := perfect_center_coprime_three ((primeRank_subgroup_le 3 J₀).trans hr)
  have hs := (ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (pCore 3 C) J₀ hcomm hcop).trans hr
  have he : primeRank 3 J₀ = primeRank 3 J := primeRank_congr 3 (subgroupOfEquivOfLe hJC)
  have hJn : primeRank 3 J ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hJthree
  have hz : primeRank 3 (pCore 3 C) = 0 := by omega
  have hd := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
  apply (eq_bot_iff_card _).mpr
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := C)).exists_card_eq
  have hn0 : n = 0 := by
    by_contra hne
    exact hd (hn ▸ dvd_pow_self 3 hne)
  rw [hn,hn0,pow_zero]

/-- The component orbit collapses to a single normal component, retaining
its exact rank and the trivial three-core of the containing subgroup. -/
theorem component_orbit_structure_of_three_rank_one
    {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) [C.Normal] (hr : primeRank 3 C ≤ 1)
    (J : Subgroup H) (hJ : IsComponent H J) (hJC : J ≤ C)
    (hJthree : 3 ∣ Nat.card J) (A : Subgroup H) :
    J.Normal ∧ componentOrbit J A = J ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥ := by
  let : J.Normal := component_normal_of_le_normal_three_rank_one C hr J hJ hJC hJthree
  have hJn : primeRank 3 J ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hJthree
  have hJr := (primeRank_mono 3 hJC).trans hr
  refine ⟨inferInstance,?_,by omega,three_core_eq_bot_of_component_in_rank_one C hr J hJ hJC hJthree⟩
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl
    (by rw [normalizer_eq_top]; exact le_top)) (le_componentOrbit J A)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
