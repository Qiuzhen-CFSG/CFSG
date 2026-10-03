module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaNormalization
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaFixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SupportBound
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Cardinality
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.QuadraticGenerators
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.FixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaCounting
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.CyclicFixedIndices

/-!
# Generic fixed indices and quadraticity

The support-one/two dichotomy gives full odd-core fixed index |S| or 2|S|. Comparing offender ratios across the coprime central summand forces the generating involutions to have identical fixed spaces there, proving quadraticity on the full module.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- The numerical heart of the generic branch of (1.6).  A minimal
order-two `oneAmax` subgroup moves one or two complete omega factors.  The
simultaneous local coordinates account for all remaining factors and all
directions of `S/A`, giving respectively the fixed-quotient values in (d)
and (c). -/
public theorem generic_fixedQuotientCard_eq_card_or_twice
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hlocal : RankOneAssemblyLocalHypothesis
      (G := G) (V := V) (S : Subgroup G))
    (hgeneric : RankOneAssemblyGenericHypothesis
      (G := G) (V := V) (S : Subgroup G)) :
    fixedQuotientCard (G := G) (V := V) (S : Subgroup G)
        (commutatorAction (oddCore G) V) =
          (Nat.card (S : Subgroup G) : ℚ) ∨
      fixedQuotientCard (G := G) (V := V) (S : Subgroup G)
        (commutatorAction (oddCore G) V) =
          (2 * Nat.card (S : Subgroup G) : ℚ) := by
  classical
  have hlocalLe : ∀ A : Subgroup G,
      oneAmax (G := G) (V := V) (S : Subgroup G) A →
      Nat.card A = 2 →
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ ≤
          oneOmegaGenerated (G := G) (V := V) := by
    intro A hAmax hAcard
    exact local_commutator_le_oneOmegaGenerated_of_generic
      (S : Subgroup G) A hlocal hAmax hAcard
        (hgeneric A hAmax hAcard)
  have hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V) :=
    oddCore_eq_oneOmegaGenerated_of_local_commutators
      h S hS hScard hW hlocalLe
  have hdecomp := oneOmegaGenerated_decomposition h S hWthree
  have hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      (S : Subgroup G) ≤ Subgroup.normalizer F :=
    all_oneOmega_normalized_generic h S hS hScard hW hWthree hlocal hgeneric
  obtain ⟨a, hane, hAmax, hAcard, hminimal⟩ :=
    exists_minimal_oneAmax_omegaSupport h S hS hScard hnorm
  let A : Subgroup G := Subgroup.zpowers (a : G)
  obtain ⟨d⟩ := exists_local_generic_coordinate_family
    (S : Subgroup G) A hlocal hAmax hAcard
      (hgeneric A hAmax hAcard)
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
  have hindexPos : 0 < Nat.card d.index := by
    by_contra hnot
    have hzero : Nat.card d.index = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hScardPow
    norm_num at hScardPow
    omega
  let _ : Nonempty d.index := (Finite.card_pos_iff.mp hindexPos)
  let i : d.index := Classical.choice inferInstance
  have hfactorLe : d.factor i ≤
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ := by
    calc
      d.factor i ≤ ⨆ j, d.factor j := le_iSup d.factor i
      _ = _ := d.factor_generated.symm
  have hsupportLe :
      (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card ≤ 2 :=
    omegaSupport_card_le_two_of_local_coordinate_full
      (S : Subgroup G) A (d.coordinate i) (d.factor i) hS hnorm
      hcoreEq hdecomp hW hWthree hmin a rfl hAmax hAcard
      (d.A_le_coordinate i) (d.coordinate_le_S i)
      (d.coordinate_card_four i) (d.factor_omega i) hfactorLe
      (d.local_commutator i) (d.point_coordinate i) hminimal
  have hsupportPos : 0 <
      (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card :=
    omegaSupport_card_pos_of_ne_one h S hS hWthree hnorm hcoreEq hdecomp
      a hane
  have hOmegaCard := local_generic_coordinate_family_omega_card
    (S : Subgroup G) A hS hnorm hcoreEq hdecomp hW a rfl d
  have hfixedPow := fixedQuotientCard_oddCore_eq_pow_card_oneOmega
    (S : Subgroup G) hS hnorm hcoreEq hdecomp hW
  have hcases :
      (omegaSupport (G := G) (V := V)
          (S : Subgroup G) hnorm a).card = 1 ∨
        (omegaSupport (G := G) (V := V)
          (S : Subgroup G) hnorm a).card = 2 := by
    omega
  rcases hcases with hsupp | hsupp
  · left
    rw [hfixedPow, hOmegaCard, hsupp, hScardPow]
    norm_num [Nat.cast_pow]
  · right
    rw [hfixedPow, hOmegaCard, hsupp, hScardPow]
    push_cast
    ring

/-- In the generic branch, the complete omega-coordinate action is
quadratic on the whole module.  The central summand is controlled by the
minimal local complements, while each noncentral omega summand is the
standard quadratic four-point coordinate. -/
public theorem generic_commutatorAction₂_eq_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hlocal : RankOneAssemblyLocalHypothesis
      (G := G) (V := V) (S : Subgroup G))
    (hgeneric : RankOneAssemblyGenericHypothesis
      (G := G) (V := V) (S : Subgroup G)) :
    commutatorAction₂ (S : Subgroup G) V = ⊥ := by
  classical
  have hlocalLe : ∀ A : Subgroup G,
      oneAmax (G := G) (V := V) (S : Subgroup G) A →
      Nat.card A = 2 →
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ ≤
          oneOmegaGenerated (G := G) (V := V) := by
    intro A hAmax hAcard
    exact local_commutator_le_oneOmegaGenerated_of_generic
      (S : Subgroup G) A hlocal hAmax hAcard
        (hgeneric A hAmax hAcard)
  have hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V) :=
    oddCore_eq_oneOmegaGenerated_of_local_commutators
      h S hS hScard hW hlocalLe
  have hdecomp := oneOmegaGenerated_decomposition h S hWthree
  have hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      (S : Subgroup G) ≤ Subgroup.normalizer F :=
    all_oneOmega_normalized_generic h S hS hScard hW hWthree hlocal hgeneric
  obtain ⟨a, hane, hAmax, hAcard, hminimal⟩ :=
    exists_minimal_oneAmax_omegaSupport h S hS hScard hnorm
  let A : Subgroup G := Subgroup.zpowers (a : G)
  obtain ⟨d⟩ := exists_local_generic_coordinate_family
    (S : Subgroup G) A hlocal hAmax hAcard
      (hgeneric A hAmax hAcard)
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
  have hindexPos : 0 < Nat.card d.index := by
    by_contra hnot
    have hzero : Nat.card d.index = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hScardPow
    norm_num at hScardPow
    omega
  let _ : Nonempty d.index := Finite.card_pos_iff.mp hindexPos
  let i0 : d.index := Classical.choice inferInstance
  have hfactorLe : d.factor i0 ≤
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ := by
    calc
      d.factor i0 ≤ ⨆ j, d.factor j := le_iSup d.factor i0
      _ = _ := d.factor_generated.symm
  have hsupportLe :
      (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card ≤ 2 :=
    omegaSupport_card_le_two_of_local_coordinate_full
      (S : Subgroup G) A (d.coordinate i0) (d.factor i0) hS hnorm
      hcoreEq hdecomp hW hWthree hmin a rfl hAmax hAcard
      (d.A_le_coordinate i0) (d.coordinate_le_S i0)
      (d.coordinate_card_four i0) (d.factor_omega i0) hfactorLe
      (d.local_commutator i0) (d.point_coordinate i0) hminimal
  have hsupportPos : 0 <
      (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card :=
    omegaSupport_card_pos_of_ne_one h S hS hWthree hnorm hcoreEq hdecomp
      a hane
  have hOmegaCard := local_generic_coordinate_family_omega_card
    (S : Subgroup G) A hS hnorm hcoreEq hdecomp hW a rfl d
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
      (S : Subgroup G) U =
        (2 : ℚ) ^ (Nat.card d.index +
          (omegaSupport (G := G) (V := V)
            (S : Subgroup G) hnorm a).card) := by
    calc
      fixedQuotientCard (G := G) (V := V) (S : Subgroup G) U =
          2 ^ (oneOmegaFinset (G := G) (V := V)).card := by
        simpa only [U] using fixedQuotientCard_oddCore_eq_pow_card_oneOmega
          (S : Subgroup G) hS hnorm hcoreEq hdecomp hW
      _ = _ := by rw [hOmegaCard]
  have hmAS : m (G := G) (V := V) A =
      m (G := G) (V := V) (S : Subgroup G) := by
    apply le_antisymm hAmax.2.1
    apply hmin A hAS
    intro hbot
    have hAcard' : Nat.card A = 2 := by simpa only [A] using hAcard
    rw [hbot] at hAcard'
    norm_num at hAcard'
  let hCinvA : IsInvariant A V C := isInvariant_restrict_actor A C
  let hUinvA : IsInvariant A V U := isInvariant_restrict_actor A U
  let _ : IsInvariant A V C := hCinvA
  let _ : IsInvariant A V U := hUinvA
  have hfixedA : fixedQuotientCard (G := G) (V := V) A U =
      (2 : ℚ) ^ (omegaSupport (G := G) (V := V)
        (S : Subgroup G) hnorm a).card := by
    simpa only [A, U] using
      fixedQuotientCard_oddCore_zpowers_eq_pow_support
        (S : Subgroup G) hS hnorm hcoreEq hdecomp a hane
  have hCfixA : C ⊓ FixedPoints.subgroup (S : Subgroup G) V =
      C ⊓ FixedPoints.subgroup A V :=
    inf_fixedPoints_eq_of_m_eq_of_pow_quotients
      (S : Subgroup G) A C U hAS hcompl
      (Nat.card d.index)
      (omegaSupport (G := G) (V := V)
        (S : Subgroup G) hnorm a).card
      hScardPow hAcard hmAS hfixedS hfixedA
  choose x hxCoordinate hxNotA hpartner using fun i : d.index =>
    exists_outside_coordinate_with_minimal_partner_support
      (S : Subgroup G) A (d.coordinate i) hS
      (d.A_le_coordinate i) (d.coordinate_le_S i) hAcard
      (d.coordinate_card_four i) a rfl hnorm
  have hxne (i : d.index) : x i ≠ 1 := by
    intro hxi
    apply hxNotA i
    rw [hxi]
    exact A.one_mem
  let B : d.index → Subgroup G := fun i => Subgroup.zpowers (x i : G)
  have hBcard (i : d.index) : Nat.card (B i) = 2 := by
    exact natCard_zpowers_eq_two_of_ne_one_of_elementary
      (S : Subgroup G) hS (x i) (hxne i)
  have hCfixB (i : d.index) :
      C ⊓ FixedPoints.subgroup (S : Subgroup G) V =
        C ⊓ FixedPoints.subgroup (B i) V := by
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
          (by simpa only [A] using hfactorLeI)
    have hsdiff : X \ Z = {d.factor i} := by
      exact support_sdiff_eq_singleton_of_local_coordinate
        (S : Subgroup G) hnorm hcoreEq hdecomp hW a (x i)
          (d.coordinate i) (d.factor i) (hxCoordinate i)
          (d.factor_omega i) hFnot (d.point_coordinate i (x i : G)
            (hxCoordinate i) (hxNotA i)).1
          (by simpa only [A] using d.local_commutator i)
    obtain ⟨K, hKZ, hKnotX⟩ :=
      exists_mem_sdiff_of_card_pos_of_partner Z X (d.factor i)
        hsdiff (hpartner i) hsupportPos
    have hK : oneOmega (G := G) (V := V) K :=
      (mem_oneOmegaFinset_iff (G := G) (V := V) K).mp
        (omegaSupport_subset_oneOmegaFinset (S : Subgroup G) hnorm a hKZ)
    have hmBA : m (G := G) (V := V) (B i) ≤
        m (G := G) (V := V) A :=
      m_zpowers_le_of_support_witness (S : Subgroup G) hnorm a (x i) A
        rfl hAcard (hBcard i) K hK hKZ hKnotX
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
        hmBS hfixedS hfixedB
    have hcardEq : X.card = Z.card := Nat.le_antisymm hXleZ hZleX
    apply inf_fixedPoints_eq_of_m_eq_of_pow_quotients
      (S : Subgroup G) (B i) C U hBS hcompl
      (Nat.card d.index) Z.card hScardPow (hBcard i) hmBS hfixedS
    simpa only [hcardEq] using hfixedB
  have hgen : (S : Subgroup G) = A ⊔ ⨆ i, B i := by
    simpa only [B] using local_generic_coordinate_family_generated_by_points
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ (S : Subgroup G) A hS hAS hAcard d x
          hxCoordinate hxNotA
  have hCquad :
      let hCinvS' : IsInvariant (S : Subgroup G) V C :=
        isInvariant_restrict_actor (S : Subgroup G) C
      let _ : IsInvariant (S : Subgroup G) V C := hCinvS'
      commutatorAction₂ (S : Subgroup G) C = ⊥ :=
    commutatorAction₂_invariant_subgroup_eq_bot_of_card_two_generators
      (S : Subgroup G) A B C hgen hAcard hBcard hCfixA hCfixB
  let Ω := oneOmegaFinset (G := G) (V := V)
  let K : Option {F : Subgroup G // F ∈ Ω} → Subgroup V
    | none => C
    | some F => commutatorAction (F : Subgroup G) V
  have hKinv : ∀ j, IsInvariant (S : Subgroup G) V (K j) := by
    intro j
    cases j with
    | none => exact hCinvS
    | some F =>
        exact commutatorAction_isInvariant_of_normalizing_actor
          (S : Subgroup G) (F : Subgroup G)
          (hnorm F ((mem_oneOmegaFinset_iff (G := G) (V := V) F).mp
            F.property))
  have hUeq : U = Ω.sup (fun F => commutatorAction F V) := by
    calc
      U = commutatorAction (oneOmegaGenerated (G := G) (V := V)) V := by
        dsimp only [U]
        rw [hcoreEq]
      _ = ⨆ F : {F : Subgroup G // F ∈ Ω},
          commutatorAction (F : Subgroup G) V := by
        apply commutatorAction_eq_iSup_of_eq_iSup
        exact hdecomp.part_a.1
      _ = _ := (finset_sup_apply_eq_iSup_subtype Ω
        (fun F => commutatorAction F V)).symm
  have hKgen : (⊤ : Subgroup V) = ⨆ j, K j := by
    calc
      (⊤ : Subgroup V) = C ⊔ U := hcompl.sup_eq_top.symm
      _ = C ⊔ Ω.sup (fun F => commutatorAction F V) := by rw [← hUeq]
      _ = ⨆ j, K j := by simp only [K, iSup_option,
        finset_sup_apply_eq_iSup_subtype]
  have hKquad : ∀ j,
      let _ : IsInvariant (S : Subgroup G) V (K j) := hKinv j
      commutatorAction₂ (S : Subgroup G) (K j) = ⊥ := by
    intro j
    cases j with
    | none => exact hCquad
    | some F =>
        have hF := (mem_oneOmegaFinset_iff (G := G) (V := V)
          (F : Subgroup G)).mp F.property
        have hfull : ⁅(F : Subgroup G), (S : Subgroup G)⁆ =
            (F : Subgroup G) :=
          commutator_oneOmega_sylow_eq_self (S : Subgroup G) hnorm
            hcoreEq hdecomp hW (F : Subgroup G) hF
        exact (oneOmega_sylow_coordinate_module
          (S : Subgroup G) (F : Subgroup G) hS hnorm hF hfull).2
  exact commutatorAction₂_eq_bot_of_iSup_quadratic K hKinv hKgen hKquad

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
