module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Conjugacy.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.LeviQuotient
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.FactorNormalizer.StandardLevi
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Components of the canonical Suzuki-pair normalizer

Write A for the full fixed middle-node B₂ Levi, B for its specified Weyl
conjugate, J = A ⊔ B, and N = N_G(J). The seed projection identifies A with
the Suzuki matrix group at the same parameter. For m ≥ 1, the proved Suzuki
simplicity and nonsolvability give simple perfect factors.

If A and B commute, simplicity makes them disjoint. Their product order,
together with the separate geometric bound on |N_G(A)|, then gives
N_G(A) = J. In particular C_G(J) lies in J and is abelian. Both factors are
subnormal in N. The simple-subnormal dichotomy forces every other
C-component of N to centralize J, contradicting its nonsolvability.
The specified Suzuki Weyl word rᵦ lies in A, and rₐ rᵦ rₐ⁻¹ is the swap.
If J were normal, that swap would lie in J. But every element of J normalizes
A, whereas the swap sends A to its distinct commuting companion. This
proves N ≠ G without a further root-separation premise.

This is conditional assembly: the seed projection, factor-normalizer bound,
and root commutation remain geometric obligations.
No ambient simplicity, maximal-subgroup classification or placement of an
arbitrary component is assumed. The final unconditional theorem remains
owned here and cannot be asserted until those obligations are proved.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E, §2.2 and Proposition 2.3.
The subnormal argument uses Aschbacher–Smith A.3.3, printed pp.42–43.
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

open Subgroup BenderSuzuki.MatrixGroups LargeLocalSeeds
open Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity.FixedCollection SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

private theorem commuting_factor_subnormal_normalizer {G : Type*} [Group G]
    (A B : Subgroup G) (hc : ⁅A, B⁆ = ⊥) :
    (A.subgroupOf (normalizer ((A ⊔ B : Subgroup G) : Set G))).IsSubnormal := by
  let N := normalizer ((A ⊔ B : Subgroup G) : Set G)
  have hBA : B ≤ normalizer (A : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])).trans
      (centralizer_le_normalizer (A : Set G))
  have hJA : A ⊔ B ≤ normalizer (A : Set G) := sup_le A.le_normalizer hBA
  have hJnorm : ((A ⊔ B).subgroupOf N).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  have hAinN : A.subgroupOf N ≤ (A ⊔ B).subgroupOf N := comap_mono le_sup_left
  apply IsSubnormal.step _ _ hAinN hJnorm.isSubnormal
  apply normal_subgroupOf_of_le_normalizer
  intro x hx
  have hxn : (x : G) ∈ normalizer (A : Set G) := hJA hx
  apply (A.le_normalizer_comap N.subtype)
  exact hxn

private theorem component_eq_factor_or_le_centralizer {G : Type*} [Group G]
    (A B : Subgroup G) [IsSimpleGroup A] [IsSimpleGroup B]
    [Group.IsPerfect A] [Group.IsPerfect B] (hc : ⁅A, B⁆ = ⊥)
    (L : Subgroup (normalizer ((A ⊔ B : Subgroup G) : Set G)))
    (hL : L.IsCComponent) :
    L.map (normalizer ((A ⊔ B : Subgroup G) : Set G)).subtype = A ∨
    L.map (normalizer ((A ⊔ B : Subgroup G) : Set G)).subtype = B ∨
    L.map (normalizer ((A ⊔ B : Subgroup G) : Set G)).subtype ≤
      centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  let N := normalizer ((A ⊔ B : Subgroup G) : Set G)
  let A' := A.subgroupOf N
  let B' := B.subgroupOf N
  have hAN : A ≤ N := le_sup_left.trans (A ⊔ B).le_normalizer
  have hBN : B ≤ N := le_sup_right.trans (A ⊔ B).le_normalizer
  let eA : A' ≃* A := subgroupOfEquivOfLe hAN
  let eB : B' ≃* B := subgroupOfEquivOfLe hBN
  let : IsSimpleGroup A' := eA.isSimpleGroup
  let : IsSimpleGroup B' := eB.isSimpleGroup
  let : Group.IsPerfect A' :=
    Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  let : Group.IsPerfect B' :=
    Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hsA : A'.IsSubnormal := commuting_factor_subnormal_normalizer A B hc
  have hsB : B'.IsSubnormal := by
    change (B.subgroupOf (normalizer ((A ⊔ B : Subgroup G) : Set G))).IsSubnormal
    rw [sup_comm A B]
    exact commuting_factor_subnormal_normalizer B A (by rwa [commutator_comm])
  have hAc : A'.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hsA
  have hBc : B'.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hsB
  rcases simple_subnormal_dichotomy A' L hsA hL.subnormal with hAL | hcA
  · left
    rw [← hAc.eq_of_le hL hAL]
    exact map_subgroupOf_eq_of_le hAN
  rcases simple_subnormal_dichotomy B' L hsB hL.subnormal with hBL | hcB
  · right; left
    rw [← hBc.eq_of_le hL hBL]
    exact map_subgroupOf_eq_of_le hBN
  right; right
  have hAm : ⁅A, L.map N.subtype⁆ = ⊥ := by
    have he := congrArg (Subgroup.map N.subtype) hcA
    simpa only [map_commutator, A', map_subgroupOf_eq_of_le hAN, Subgroup.map_bot] using he
  have hBm : ⁅B, L.map N.subtype⁆ = ⊥ := by
    have he := congrArg (Subgroup.map N.subtype) hcB
    simpa only [map_commutator, B', map_subgroupOf_eq_of_le hBN, Subgroup.map_bot] using he
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm,
    commutator_eq_bot_iff_le_centralizer]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hAm)
    (commutator_eq_bot_iff_le_centralizer.mp hBm)

private theorem components_of_solvable_commonCentralizer {G : Type*} [Group G]
    (A B : Subgroup G) [IsSimpleGroup A] [IsSimpleGroup B]
    [Group.IsPerfect A] [Group.IsPerfect B] (hc : ⁅A, B⁆ = ⊥)
    [Group.IsSolvable (centralizer ((A ⊔ B : Subgroup G) : Set G))]
    (L : Subgroup (normalizer ((A ⊔ B : Subgroup G) : Set G)))
    (hL : L.IsCComponent) :
    L.map (normalizer ((A ⊔ B : Subgroup G) : Set G)).subtype = A ∨
    L.map (normalizer ((A ⊔ B : Subgroup G) : Set G)).subtype = B := by
  rcases component_eq_factor_or_le_centralizer A B hc L hL with hA | hB | hC
  · exact Or.inl hA
  · exact Or.inr hB
  let N := normalizer ((A ⊔ B : Subgroup G) : Set G)
  have hsolv : Group.IsSolvable (L.map N.subtype) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hC)
  let := hsolv
  exact (hL.not_isSolvable
    (Group.isSolvable_of_isSolvable_injective
      (f := (equivMapOfInjective L N.subtype N.subtype_injective).toMonoidHom)
      (equivMapOfInjective L N.subtype N.subtype_injective).injective)).elim

private theorem disjoint_of_simple_perfect_commuting {G : Type*} [Group G]
    (A B : Subgroup G) [IsSimpleGroup A] [Group.IsPerfect A]
    (hc : ⁅A, B⁆ = ⊥) : Disjoint A B := by
  have hc' := commutator_eq_bot_iff_le_centralizer.mp hc
  let : (B.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer
    (hc'.trans (centralizer_le_normalizer (B : Set G)))
  rcases (inferInstance : (B.subgroupOf A).Normal).eq_bot_or_eq_top with hb | ht
  · apply disjoint_def.mpr
    intro x hxA hxB
    have he : (⟨x, hxA⟩ : A) ∈ B.subgroupOf A := hxB
    rw [hb] at he
    exact congrArg Subtype.val (mem_bot.mp he)
  · have hAB : A ≤ B := subgroupOf_eq_top.mp ht
    exact (Group.IsPerfect.not_isMulCommutative A
      (le_centralizer_iff_isMulCommutative.mp
        (hc'.trans (centralizer_le hAB)))).elim

private theorem normalizer_eq_join_of_card {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [IsSimpleGroup A] [Group.IsPerfect A]
    (hc : ⁅A, B⁆ = ⊥)
    (hcard : Nat.card (normalizer (A : Set G)) ≤ Nat.card A * Nat.card B) :
    normalizer (A : Set G) = A ⊔ B := by
  have hjoin : A ⊔ B ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer
      ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])).trans
        (centralizer_le_normalizer (A : Set G)))
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B
    (disjoint_of_simple_perfect_commuting A B hc)
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hprod : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod]
  exact (eq_of_le_of_card_ge hjoin (hprod ▸ hcard)).symm

private theorem commonCentralizer_solvable_of_normalizer_card
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [IsSimpleGroup A] [Group.IsPerfect A]
    (hc : ⁅A, B⁆ = ⊥)
    (hcard : Nat.card (normalizer (A : Set G)) ≤ Nat.card A * Nat.card B) :
    Group.IsSolvable (centralizer ((A ⊔ B : Subgroup G) : Set G)) := by
  have hCJ : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ A ⊔ B := by
    exact ((centralizer_le
      (show (A : Set G) ⊆ (A ⊔ B : Subgroup G) from fun _ hx => mem_sup_left hx)).trans
        (centralizer_le_normalizer (A : Set G))).trans
      (normalizer_eq_join_of_card A B hc hcard).le
  exact Group.isSolvable_of_comm fun x y =>
    Subtype.ext (x.property y (hCJ y.property)).symm

private theorem suzuki_simple_perfect {m : ℕ} (hm : 1 ≤ m)
    {H : Type*} [Group H] (e : H ≃* SuzukiMatrixGroup m) :
    IsSimpleGroup H ∧ Group.IsPerfect H := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup H := e.isSimpleGroup
  refine ⟨inferInstance, ⟨?_⟩⟩
  rcases (inferInstance : (commutator H).Normal).eq_bot_or_eq_top with hb | ht
  · have hsolv : Group.IsSolvable H := ⟨⟨1, (derivedSeries_one H).trans hb⟩⟩
    let := hsolv
    exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
      (Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom)
        e.symm.injective)).elim
  · exact ht

private theorem linearWeyl_inv (m : ℕ) :
    (weylLift m .linear)⁻¹ = weylLift m .linear := by
  have hr (r : F4Chevalley.Root) (t : CoefficientField m) :
      (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r t := by
    apply Subtype.ext
    simp [F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  have hi (i : Fin 4) :
      (Parabolics.weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ =
        Parabolics.weylWord m (typeF4SimpleRootIndex i) 1 := by
    simp only [Parabolics.weylWord, mul_inv_rev, hr, mul_assoc]
  apply Subtype.ext
  have h := sideWord_fixed m .linear
  rw [reeTwist_simpleWord] at h
  change simpleWord m [3, 0] = simpleWord m [0, 3] at h
  change (simpleWord m (sideWord .linear))⁻¹ = simpleWord m (sideWord .linear)
  simpa only [sideWord, simpleWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_inv_rev, hi] using h

private theorem suzukiWeyl_mem_standardSuzukiLevi (m : ℕ) :
    weylLift m .suzuki ∈ standardSuzukiLevi m := by
  change simpleWord m (sideWord .suzuki) ∈ splitLevi m .suzuki
  exact relativeWeyl_mem_fixedLevi (canonicalLocalBlockInput m) .suzuki

private theorem suzukiFactorSwap_eq_conj_suzukiWeyl (m : ℕ) :
    suzukiFactorSwap m =
      weylLift m .linear * weylLift m .suzuki * (weylLift m .linear)⁻¹ := by
  rw [linearWeyl_inv]
  rfl

private theorem swap_not_mem_pair_of_commuting {m : ℕ}
    [IsSimpleGroup (standardSuzukiLevi m)] [Group.IsPerfect (standardSuzukiLevi m)]
    (hc : ⁅standardSuzukiLevi m, companionSuzukiLevi m⁆ = ⊥) :
    suzukiFactorSwap m ∉ suzukiLeviPair m := by
  have hJN : suzukiLeviPair m ≤ normalizer (standardSuzukiLevi m : Set (Model m)) :=
    sup_le (standardSuzukiLevi m).le_normalizer
      ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])).trans
        (centralizer_le_normalizer (standardSuzukiLevi m : Set (Model m))))
  intro hw
  have he : companionSuzukiLevi m = standardSuzukiLevi m :=
    mem_normalizer_iff_map_conj_eq.mp (hJN hw)
  rw [he, commutator_eq_self] at hc
  exact (nontrivial_iff_ne_bot _).mp inferInstance hc

/-- Commutation and the concrete normalizer bound identify the factor
normalizer with the join. Disjointness and the product order are proved
using the supplied full-parameter Suzuki equivalence. -/
theorem standardSuzukiLevi_normalizer_eq_pair_of_equiv_of_commuting_of_card
    {m : ℕ} (hm : 1 ≤ m)
    (e : standardSuzukiLevi m ≃* SuzukiMatrixGroup m)
    (hc : ⁅standardSuzukiLevi m, companionSuzukiLevi m⁆ = ⊥)
    (hcard : Nat.card (normalizer (standardSuzukiLevi m : Set (Model m))) ≤
      Nat.card (SuzukiMatrixGroup m) ^ 2) :
    normalizer (standardSuzukiLevi m : Set (Model m)) = suzukiLeviPair m := by
  obtain ⟨hs, hp⟩ := suzuki_simple_perfect hm e
  let := hs
  let := hp
  apply normalizer_eq_join_of_card _ _ hc
  have heB : Nat.card (companionSuzukiLevi m) = Nat.card (standardSuzukiLevi m) :=
    Nat.card_congr ((MulAut.conj (suzukiFactorSwap m)).subgroupMap
      (standardSuzukiLevi m)).symm.toEquiv
  simpa only [heB, Nat.card_congr e.toEquiv, pow_two] using hcard

/-- The full-parameter component equalities follow from the matrix
comparison, commutation, and the existing factor-normalizer bound. -/
theorem suzukiLeviPairNormalizer_components_of_equiv_of_commuting_of_card
    {m : ℕ} (hm : 1 ≤ m)
    (e : standardSuzukiLevi m ≃* SuzukiMatrixGroup m)
    (hc : ⁅standardSuzukiLevi m, companionSuzukiLevi m⁆ = ⊥)
    (hcard : Nat.card (normalizer (standardSuzukiLevi m : Set (Model m))) ≤
      Nat.card (SuzukiMatrixGroup m) ^ 2)
    (L : Subgroup (suzukiLeviPairNormalizer m)) (hL : L.IsCComponent) :
    L.map (suzukiLeviPairNormalizer m).subtype = standardSuzukiLevi m ∨
      L.map (suzukiLeviPairNormalizer m).subtype = companionSuzukiLevi m := by
  obtain ⟨hs, hp⟩ := suzuki_simple_perfect hm e
  let := hs
  let := hp
  let eB : companionSuzukiLevi m ≃* SuzukiMatrixGroup m :=
    ((MulAut.conj (suzukiFactorSwap m)).subgroupMap (standardSuzukiLevi m)).symm.trans e
  obtain ⟨hsB, hpB⟩ := suzuki_simple_perfect hm eB
  let := hsB
  let := hpB
  have hcard' : Nat.card (normalizer (standardSuzukiLevi m : Set (Model m))) ≤
      Nat.card (standardSuzukiLevi m) * Nat.card (companionSuzukiLevi m) := by
    simpa only [Nat.card_congr e.toEquiv, Nat.card_congr eB.toEquiv, pow_two] using hcard
  let := commonCentralizer_solvable_of_normalizer_card
    (standardSuzukiLevi m) (companionSuzukiLevi m) hc hcard'
  exact components_of_solvable_commonCentralizer _ _ hc L hL

/-- The outer Weyl word conjugates the Suzuki Weyl word to the swap.
Normality of the pair would place the swap inside the pair, contradicting
its interchange of the distinct commuting simple factors. -/
theorem suzukiLeviPairNormalizer_ne_top_of_equiv_of_commuting
    {m : ℕ} (hm : 1 ≤ m)
    (e : standardSuzukiLevi m ≃* SuzukiMatrixGroup m)
    (hc : ⁅standardSuzukiLevi m, companionSuzukiLevi m⁆ = ⊥) :
    suzukiLeviPairNormalizer m ≠ ⊤ := by
  obtain ⟨hs, hp⟩ := suzuki_simple_perfect hm e
  let := hs
  let := hp
  intro htop
  have hg : weylLift m .linear ∈ suzukiLeviPairNormalizer m := htop ▸ mem_top _
  apply swap_not_mem_pair_of_commuting hc
  rw [suzukiFactorSwap_eq_conj_suzukiWeyl]
  exact (mem_normalizer_iff.mp hg _).mp
    (mem_sup_left (suzukiWeyl_mem_standardSuzukiLevi m))

/-- Conditional assembly through the genuine seed projection and the
independent root commutation calculation. Properness is proved using the
actual Weyl words. The unconditional normalizer geometry still requires
all three displayed premises to be discharged. -/
theorem suzukiPairNormalizerGeometry_of_seedProjections_of_commuting_of_card
    (hprojections : ∀ m, 1 ≤ m →
      ∃ π : standardSeed (canonicalLocalBlockInput m) .suzuki →* SuzukiMatrixGroup m,
        Function.Surjective π ∧ π.ker = seedRadical (canonicalLocalBlockInput m) .suzuki)
    (hcard : FactorNormalizer.StandardLeviNormalizerCardBound)
    (hcomm : ∀ m, 1 ≤ m → ⁅standardSuzukiLevi m, companionSuzukiLevi m⁆ = ⊥) :
    SuzukiPairNormalizerGeometry := by
  intro m hm
  obtain ⟨π, hπ, hker⟩ := hprojections m hm
  let e : standardSuzukiLevi m ≃* SuzukiMatrixGroup m :=
    (localLeviEquiv (canonicalLocalBlockInput m)).symm.trans
      (fixedLeviEquivOfProjection (canonicalLocalBlockInput m) .suzuki π hπ hker)
  exact ⟨suzukiLeviPairNormalizer_ne_top_of_equiv_of_commuting hm e (hcomm m hm),
    fun L hL => suzukiLeviPairNormalizer_components_of_equiv_of_commuting_of_card
      hm e (hcomm m hm) (hcard m hm) L hL⟩

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
