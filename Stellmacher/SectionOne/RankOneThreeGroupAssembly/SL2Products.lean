module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.FixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaFixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.CyclicFixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Cardinality
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.QuadraticGenerators

/-!
# Independent centerless diagonal factors

Pairwise commuting centerless factors have trivial intersections with the joins of other factors. In support one, the local coordinates provide generators whose singleton supports select the corresponding order-three factors.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Distinct centerless subgroups which commute elementwise have trivial
intersection. -/
private theorem disjoint_of_center_eq_bot_of_commute
    {G : Type u} [Group G] (A B : Subgroup G)
    (hcenter : Subgroup.center A = ⊥)
    (hcomm : ∀ a : G, a ∈ A → ∀ b : G, b ∈ B → a * b = b * a) :
    Disjoint A B := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxcenter : (⟨x, hx.1⟩ : A) ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using hcomm (y : G) y.property x hx.2
  rw [hcenter] at hxcenter
  change x = 1
  exact congrArg Subtype.val hxcenter

/-- `SL₂(2)` is centerless. -/
public theorem center_eq_bot_of_isSL2Two
    {G : Type u} [Group G] [Finite G] (h : IsSL2Two G) :
    Subgroup.center G = ⊥ := by
  rcases h with ⟨e⟩
  ext x
  constructor
  · intro hx
    have hex : e x ∈ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa using congrArg e (Subgroup.mem_center_iff.mp hx z)
    have hcenter : Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro A hA
      revert hA
      decide +kernel +revert
    rw [hcenter] at hex
    have hexone : e x = 1 := hex
    exact e.injective (by simpa using hexone)
  · intro hx
    rw [hx]
    exact Subgroup.one_mem _

/-- A finite family of distinct centerless subgroups which commute
pairwise is an internal direct product of its join. -/
public theorem internalDirectProduct_image_of_iSup_centerless_commuting
    {G I : Type u} [Group G] [Fintype I] [DecidableEq (Subgroup G)]
    (H : Subgroup G) (E : I → Subgroup G)
    (hgen : H = ⨆ i, E i)
    (hcenter : ∀ i, Subgroup.center (E i) = ⊥)
    (hcomm : ∀ i j, i ≠ j →
      ∀ a : G, a ∈ E i → ∀ b : G, b ∈ E j → a * b = b * a) :
    IsInternalDirectProduct H (Finset.univ.image E) := by
  classical
  let F : Finset (Subgroup G) := Finset.univ.image E
  have hmem (i : I) : E i ∈ F := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hgenF : H = ⨆ K : {K : Subgroup G // K ∈ F}, (K : Subgroup G) := by
    apply le_antisymm
    · rw [hgen]
      apply iSup_le
      intro i
      exact le_iSup (fun K : {K : Subgroup G // K ∈ F} =>
        (K : Subgroup G)) ⟨E i, hmem i⟩
    · apply iSup_le
      rintro ⟨K, hKF⟩
      rw [Finset.mem_image] at hKF
      obtain ⟨i, _hi, rfl⟩ := hKF
      rw [hgen]
      exact le_iSup E i
  refine ⟨hgenF, ?_, ?_, ?_⟩
  · intro A hAF
    rw [Finset.mem_image] at hAF
    obtain ⟨i, _hi, rfl⟩ := hAF
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (by
      rw [hgen]
      exact le_iSup E i)).2
    rw [hgen]
    apply iSup_le
    intro j
    by_cases hji : j = i
    · subst j
      exact (E i).le_normalizer
    · have hcent : E j ≤ Subgroup.centralizer (E i : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        intro a ha b hb
        exact (hcomm i j (Ne.symm hji) a ha b hb).symm
      exact hcent.trans (Subgroup.centralizer_le_normalizer (E i : Set G))
  · intro A hAF B hBF hAB
    rw [Finset.mem_image] at hAF hBF
    obtain ⟨i, _hi, rfl⟩ := hAF
    obtain ⟨j, _hj, rfl⟩ := hBF
    apply disjoint_of_center_eq_bot_of_commute (E i) (E j) (hcenter i)
    exact hcomm i j (fun hij => hAB (congrArg E hij))
  · intro A hAF B hBF hAB
    rw [Finset.mem_image] at hAF hBF
    obtain ⟨i, _hi, rfl⟩ := hAF
    obtain ⟨j, _hj, rfl⟩ := hBF
    exact hcomm i j (fun hij => hAB (congrArg E hij))

/-- In the support-one generic case, choose the local order-two complements
so that each complement moves exactly its own lifted omega factor. -/
public theorem exists_local_coordinate_generators_singleton_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G) (A : Subgroup G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      (S : Subgroup G) ≤ Subgroup.normalizer F)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (a : S) (hAeq : A = Subgroup.zpowers (a : G))
    (hAmax : oneAmax (G := G) (V := V) (S : Subgroup G) A)
    (hAcard : Nat.card A = 2)
    (d : LocalGenericCoordinateFamily (G := G) (V := V)
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ (S : Subgroup G) A)
    (hsupportOne : (omegaSupport (G := G) (V := V)
      (S : Subgroup G) hnorm a).card = 1) :
    ∃ x : d.index → S,
      (∀ i, (x i : G) ∈ d.coordinate i) ∧
      (∀ i, (x i : G) ∉ A) ∧
      (∀ i, omegaSupport (G := G) (V := V)
        (S : Subgroup G) hnorm (x i) = {d.factor i}) := by
  classical
  let _ : Finite d.index := d.index_finite
  have hAS : A ≤ (S : Subgroup G) := hAmax.1
  have hWcent :
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
          (S : Subgroup G)⁆ ≤ Subgroup.centralizer (A : Set G) :=
    local_commutator_le_centralizer (S : Subgroup G) A hS hAS
  have hScardPow : Nat.card (S : Subgroup G) =
      2 ^ (Nat.card d.index + 1) :=
    local_generic_coordinate_family_sylow_card
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ (S : Subgroup G) A hS hAS hAcard
      hWcent hdecomp d
  have hOmegaCard := local_generic_coordinate_family_omega_card
    (S : Subgroup G) A hS hnorm hcoreEq hdecomp hW a hAeq d
  let C : Subgroup V := FixedPoints.subgroup (oddCore G) V
  let U : Subgroup V := commutatorAction (oddCore G) V
  let hWnormal : (oddCore G).Normal := by
    dsimp only [oddCore]
    exact pPrimeCore_normal
  let _ : (oddCore G).Normal := hWnormal
  let hCinvG : IsInvariant G V C := fixedPoints_isInvariant_of_normal (oddCore G)
  let hUinvG : IsInvariant G V U :=
    commutatorAction_isInvariant_of_normal_actor (oddCore G)
  let _ : IsInvariant G V C := hCinvG
  let _ : IsInvariant G V U := hUinvG
  let hCinvS : IsInvariant (S : Subgroup G) V C :=
    isInvariant_restrict_actor (S : Subgroup G) C
  let hUinvS : IsInvariant (S : Subgroup G) V U :=
    isInvariant_restrict_actor (S : Subgroup G) U
  let _ : IsInvariant (S : Subgroup G) V C := hCinvS
  let _ : IsInvariant (S : Subgroup G) V U := hUinvS
  have hcop : Nat.Coprime (Nat.card (oddCore G)) (Nat.card V) := by
    obtain ⟨r, hr⟩ := hWthree.exists_card_eq
    obtain ⟨q, hq⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hr, hq]
    exact Nat.Coprime.pow r q (by decide)
  have hcompl : IsCompl C U := by
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := oddCore G)
      (Group.isSolvable_of_comm (G := V)
        fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  have hfixedS : fixedQuotientCard (G := G) (V := V)
      (S : Subgroup G) U = (2 : ℚ) ^ (Nat.card d.index + 1) := by
    calc
      fixedQuotientCard (G := G) (V := V) (S : Subgroup G) U =
          2 ^ (oneOmegaFinset (G := G) (V := V)).card := by
        simpa only [U] using fixedQuotientCard_oddCore_eq_pow_card_oneOmega
          (S : Subgroup G) hS hnorm hcoreEq hdecomp hW
      _ = _ := by rw [hOmegaCard, hsupportOne]
  have hmAS : m (G := G) (V := V) A =
      m (G := G) (V := V) (S : Subgroup G) := by
    apply le_antisymm hAmax.2.1
    apply hmin A hAS
    intro hbot
    rw [hbot] at hAcard
    norm_num at hAcard
  choose x hxCoordinate hxNotA hpartner using fun i : d.index =>
    exists_outside_coordinate_with_minimal_partner_support
      (S : Subgroup G) A (d.coordinate i) hS
      (d.A_le_coordinate i) (d.coordinate_le_S i) hAcard
      (d.coordinate_card_four i) a hAeq hnorm
  have hxne (i : d.index) : x i ≠ 1 := by
    intro hxi
    apply hxNotA i
    rw [hxi]
    exact A.one_mem
  let B : d.index → Subgroup G := fun i => Subgroup.zpowers (x i : G)
  have hBcard (i : d.index) : Nat.card (B i) = 2 :=
    natCard_zpowers_eq_two_of_ne_one_of_elementary
      (S : Subgroup G) hS (x i) (hxne i)
  refine ⟨x, hxCoordinate, hxNotA, ?_⟩
  intro i
  let X := omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm (x i)
  let Z := omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a
  have hfactorLeI : d.factor i ≤
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ := by
    calc
      d.factor i ≤ ⨆ j, d.factor j := le_iSup d.factor i
      _ = _ := d.factor_generated.symm
  have hFnot : d.factor i ∉ Z :=
    oneOmega_not_mem_support_of_le_local_commutator
      (S : Subgroup G) hS hnorm a (d.factor i) (d.factor_omega i)
        (by simpa only [hAeq] using hfactorLeI)
  have hsdiff : X \ Z = {d.factor i} :=
    support_sdiff_eq_singleton_of_local_coordinate
      (S : Subgroup G) hnorm hcoreEq hdecomp hW a (x i)
        (d.coordinate i) (d.factor i) (hxCoordinate i)
        (d.factor_omega i) hFnot
        (d.point_coordinate i (x i : G) (hxCoordinate i) (hxNotA i)).1
        (by simpa only [hAeq] using d.local_commutator i)
  have hsupportPos : 0 < Z.card := by
    simpa only [Z, hsupportOne] using Nat.zero_lt_one
  obtain ⟨K, hKZ, hKnotX⟩ :=
    exists_mem_sdiff_of_card_pos_of_partner Z X (d.factor i)
      hsdiff (hpartner i) hsupportPos
  have hK : oneOmega (G := G) (V := V) K :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) K).mp
      (omegaSupport_subset_oneOmegaFinset (S : Subgroup G) hnorm a hKZ)
  have hmBA : m (G := G) (V := V) (B i) ≤
      m (G := G) (V := V) A :=
    m_zpowers_le_of_support_witness (S : Subgroup G) hnorm a (x i) A
      hAeq hAcard (hBcard i) K hK hKZ hKnotX
        (d.point_coordinate i (x i : G) (hxCoordinate i) (hxNotA i)).2
  have hBS : B i ≤ (S : Subgroup G) :=
    (Subgroup.zpowers_le).mpr (x i).property
  have hBne : B i ≠ ⊥ := by
    intro hbot
    have hBcard' := hBcard i
    rw [hbot] at hBcard'
    norm_num at hBcard'
  have hmBS : m (G := G) (V := V) (B i) =
      m (G := G) (V := V) (S : Subgroup G) :=
    le_antisymm (hmBA.trans hAmax.2.1) (hmin (B i) hBS hBne)
  have hXleZ : X.card ≤ Z.card :=
    card_le_of_sdiff_eq_singleton_of_exists_mem_sdiff
      Z X (d.factor i) K hsdiff hKZ hKnotX
  let hCinvB : IsInvariant (B i) V C := isInvariant_restrict_actor (B i) C
  let hUinvB : IsInvariant (B i) V U := isInvariant_restrict_actor (B i) U
  let _ : IsInvariant (B i) V C := hCinvB
  let _ : IsInvariant (B i) V U := hUinvB
  have hfixedB : fixedQuotientCard (G := G) (V := V) (B i) U =
      (2 : ℚ) ^ X.card := by
    simpa only [B, U, X] using
      fixedQuotientCard_oddCore_zpowers_eq_pow_support
        (S : Subgroup G) hS hnorm hcoreEq hdecomp (x i) (hxne i)
  have hZleX : Z.card ≤ X.card :=
    exponent_le_of_m_eq_of_pow_quotients
      (S : Subgroup G) (B i) C U hBS hcompl
      (Nat.card d.index) Z.card X.card hScardPow (hBcard i)
      hmBS (by simpa only [hsupportOne, Z] using hfixedS) hfixedB
  have hXcard : X.card = 1 := by
    rw [← hsupportOne]
    exact Nat.le_antisymm hXleZ hZleX
  obtain ⟨Y, hXY⟩ := Finset.card_eq_one.mp hXcard
  have hfactorX : d.factor i ∈ X := by
    have : d.factor i ∈ X \ Z := by rw [hsdiff]; simp
    exact (Finset.mem_sdiff.mp this).1
  have hYeq : Y = d.factor i := by
    rw [hXY] at hfactorX
    have hFY : d.factor i = Y := by simpa using hfactorX
    exact hFY.symm
  change X = {d.factor i}
  rw [hXY, hYeq]

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
