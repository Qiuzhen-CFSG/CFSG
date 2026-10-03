module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Cardinality
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.QuadraticGenerators
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaNormalization
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaFixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SupportBound

/-!
# The generic support-one SL2 product

Pair each singleton-support involution with its omega factor. Their full commutator gives SL2(2); distinct pairs commute and are centerless, yielding the exact internal direct product of the odd core and Sylow subgroup.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- In the generic support-one case, pairing every complete omega factor
with its unique order-two coordinate gives the internal product of
`SL₂(2)` factors asserted in alternative (1.6)(d). -/
private theorem local_generic_support_one_sl2_product
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
    ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ (S : Subgroup G)) F := by
  classical
  let _ : Finite d.index := d.index_finite
  obtain ⟨x, hxCoordinate, hxNotA, hxSupport⟩ :=
    exists_local_coordinate_generators_singleton_support S A hS hnorm
      hcoreEq hdecomp hW hWthree hmin a hAeq hAmax hAcard d hsupportOne
  have hxne (i : d.index) : x i ≠ 1 := by
    intro hxi
    apply hxNotA i
    rw [hxi]
    exact A.one_mem
  let y : Option d.index → S
    | none => a
    | some i => x i
  let K : Option d.index → Subgroup G
    | none => Classical.choose (Finset.card_eq_one.mp hsupportOne)
    | some i => d.factor i
  let Q : Option d.index → Subgroup G := fun i => Subgroup.zpowers (y i : G)
  let E : Option d.index → Subgroup G := fun i => K i ⊔ Q i
  let F0 : Subgroup G := Classical.choose (Finset.card_eq_one.mp hsupportOne)
  have hsupportEq : omegaSupport (G := G) (V := V)
      (S : Subgroup G) hnorm a = {F0} :=
    Classical.choose_spec (Finset.card_eq_one.mp hsupportOne)
  have hF0support : F0 ∈ omegaSupport (G := G) (V := V)
      (S : Subgroup G) hnorm a := by
    rw [hsupportEq]
    simp
  have hF0omega : oneOmega (G := G) (V := V) F0 :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) F0).mp
      (omegaSupport_subset_oneOmegaFinset (S : Subgroup G) hnorm a hF0support)
  have hfactorLe (i : d.index) : d.factor i ≤
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ := by
    calc
      d.factor i ≤ ⨆ j, d.factor j := le_iSup d.factor i
      _ = _ := d.factor_generated.symm
  have hfactorNotSupport (i : d.index) : d.factor i ∉
      omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a := by
    apply oneOmega_not_mem_support_of_le_local_commutator
      (S : Subgroup G) hS hnorm a (d.factor i) (d.factor_omega i)
    simpa only [hAeq] using hfactorLe i
  have hF0neFactor (i : d.index) : F0 ≠ d.factor i := by
    intro heq
    apply hfactorNotSupport i
    rw [← heq]
    exact hF0support
  have hKomega (i : Option d.index) : oneOmega (G := G) (V := V) (K i) := by
    cases i with
    | none => simpa only [K, F0] using hF0omega
    | some i => simpa only [K] using d.factor_omega i
  have hKinj : Function.Injective K := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            exfalso
            exact hF0neFactor j (by simpa only [K, F0] using hij)
    | some i =>
        cases j with
        | none =>
            exfalso
            exact hF0neFactor i (by simpa only [K, F0] using hij.symm)
        | some j =>
            exact congrArg some (d.factor_injective (by simpa only [K] using hij))
  have hQleS (i : Option d.index) : Q i ≤ (S : Subgroup G) := by
    rw [Subgroup.zpowers_le]
    exact (y i).property
  have hQcard (i : Option d.index) : Nat.card (Q i) = 2 := by
    cases i with
    | none => simpa only [Q, y, hAeq] using hAcard
    | some i =>
        simpa only [Q, y] using
          natCard_zpowers_eq_two_of_ne_one_of_elementary
            (S : Subgroup G) hS (x i) (hxne i)
  have hQnorm (i : Option d.index) :
      Q i ≤ Subgroup.normalizer (K i : Set G) :=
    (hQleS i).trans (hnorm (K i) (hKomega i))
  have hKsupport (i : Option d.index) :
      omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm (y i) =
        {K i} := by
    cases i with
    | none => simpa only [y, K, F0] using hsupportEq
    | some i => simpa only [y, K] using hxSupport i
  have hfull (i : Option d.index) : ⁅K i, Q i⁆ = K i := by
    cases i with
    | none =>
        simpa only [K, Q, y, F0] using
          commutator_oneOmega_zpowers_eq_self_of_mem_support
            (S : Subgroup G) hnorm a F0 hF0omega hF0support
    | some i =>
        simpa only [K, Q, y] using
          (d.point_coordinate i (x i : G) (hxCoordinate i) (hxNotA i)).1
  have hEsl (i : Option d.index) : IsSL2Two (↑(E i)) := by
    simpa only [E] using
      isSL2Two_sup_of_card_three_card_two_full_commutator
        (K i) (Q i) (hKomega i).2.1 (hQcard i) (hQnorm i) (hfull i)
  have hderived (i : Option d.index) :
      (commutator (↑(E i))).map (E i).subtype = K i := by
    simpa only [E] using
      map_commutator_sup_eq_left_of_card_two_full_commutator
        (K i) (Q i) (hQcard i) (hQnorm i) (hfull i)
  have hKK (i j : Option d.index) (hij : i ≠ j) :
      ∀ k : G, k ∈ K i → ∀ l : G, l ∈ K j → k * l = l * k := by
    apply hdecomp.part_a.2.2.2 (K i)
      ((mem_oneOmegaFinset_iff (G := G) (V := V) (K i)).mpr (hKomega i))
      (K j) ((mem_oneOmegaFinset_iff (G := G) (V := V) (K j)).mpr (hKomega j))
    exact fun h => hij (hKinj h)
  have hQQ (i j : Option d.index) :
      ∀ q : G, q ∈ Q i → ∀ r : G, r ∈ Q j → q * r = r * q := by
    intro q hq r hr
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm
        (⟨q, hQleS i hq⟩ : (S : Subgroup G))
        (⟨r, hQleS j hr⟩ : (S : Subgroup G)))
  have hKQ (i j : Option d.index) (hij : i ≠ j) :
      ∀ k : G, k ∈ K i → ∀ q : G, q ∈ Q j → k * q = q * k := by
    have hnot : K i ∉ omegaSupport (G := G) (V := V)
        (S : Subgroup G) hnorm (y j) := by
      rw [hKsupport j]
      simpa only [Finset.mem_singleton] using fun h => hij (hKinj h)
    have hbot : ⁅K i, Q j⁆ = ⊥ := by
      simpa only [Q] using
        commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
          (S : Subgroup G) hnorm (y j) (K i) (hKomega i) hnot
    have hcent : K i ≤ Subgroup.centralizer (Q j : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro k hk q hq
    exact (Subgroup.mem_centralizer_iff.mp (hcent hk) q hq).symm
  have hEcomm (i j : Option d.index) (hij : i ≠ j) :
      ∀ e : G, e ∈ E i → ∀ f : G, f ∈ E j → e * f = f * e := by
    intro e he f hf
    change e ∈ K i ⊔ Q i at he
    change f ∈ K j ⊔ Q j at hf
    have he' : e ∈ ((K i ⊔ Q i : Subgroup G) : Set G) := he
    have hf' : f ∈ ((K j ⊔ Q j : Subgroup G) : Set G) := hf
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (K i) (Q i) (hQnorm i),
      Set.mem_mul] at he'
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (K j) (Q j) (hQnorm j),
      Set.mem_mul] at hf'
    obtain ⟨k, hk, q, hq, rfl⟩ := he'
    obtain ⟨l, hl, r, hr, rfl⟩ := hf'
    have hkl := hKK i j hij k hk l hl
    have hkr := hKQ i j hij k hk r hr
    have hlq := hKQ j i (Ne.symm hij) l hl q hq
    have hqr := hQQ i j q hq r hr
    calc
      k * q * (l * r) = k * (q * l) * r := by simp only [mul_assoc]
      _ = k * (l * q) * r := by rw [hlq]
      _ = (k * l) * (q * r) := by simp only [mul_assoc]
      _ = (l * k) * (r * q) := by rw [hkl, hqr]
      _ = l * (k * r) * q := by simp only [mul_assoc]
      _ = l * (r * k) * q := by rw [hkr]
      _ = l * r * (k * q) := by simp only [mul_assoc]
  have hWgen : oddCore G = ⨆ i, K i := by
    calc
      oddCore G = oneOmegaGenerated (G := G) (V := V) := hcoreEq
      _ = ⨆ F : {F : Subgroup G //
          F ∈ oneOmegaFinset (G := G) (V := V)}, (F : Subgroup G) :=
        hdecomp.part_a.1
      _ = ⨆ i, K i := by
        apply le_antisymm
        · apply iSup_le
          intro F
          have hFomega := (mem_oneOmegaFinset_iff (G := G) (V := V)
            (F : Subgroup G)).mp F.property
          by_cases hFsupport : (F : Subgroup G) ∈
              omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a
          · have hFF0 : (F : Subgroup G) = F0 := by
              rw [hsupportEq] at hFsupport
              simpa using hFsupport
            rw [hFF0]
            exact le_iSup K none
          · have hFle : (F : Subgroup G) ≤ ⨆ i, d.factor i := by
              rw [← d.factor_generated]
              have htemp := oneOmega_le_local_commutator_of_not_mem_support
                (S : Subgroup G) hnorm hcoreEq hdecomp hW a
                (F : Subgroup G) hFomega hFsupport
              rw [← hAeq] at htemp
              exact htemp
            obtain ⟨i, hi⟩ := oneOmega_eq_member_of_le_iSup
              hdecomp d.factor d.factor_omega (F : Subgroup G) hFomega hFle
            rw [hi]
            exact le_iSup K (some i)
        · apply iSup_le
          intro i
          rw [← hdecomp.part_a.1]
          exact le_iSup (fun F : {F : Subgroup G //
            F ∈ oneOmegaFinset (G := G) (V := V)} => (F : Subgroup G))
              ⟨K i, (mem_oneOmegaFinset_iff (G := G) (V := V) (K i)).mpr
                (hKomega i)⟩
  have hSgen0 : (S : Subgroup G) = A ⊔
      ⨆ i, Subgroup.zpowers (x i : G) :=
    local_generic_coordinate_family_generated_by_points
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ (S : Subgroup G) A hS hAmax.1 hAcard d x
        hxCoordinate hxNotA
  have hSgen : (S : Subgroup G) = ⨆ i, Q i := by
    calc
      (S : Subgroup G) = A ⊔ ⨆ i, Subgroup.zpowers (x i : G) := hSgen0
      _ = ⨆ i, Q i := by simp only [iSup_option, Q, y, hAeq]
  have hEgen : oddCore G ⊔ (S : Subgroup G) = ⨆ i, E i := by
    apply le_antisymm
    · apply sup_le
      · calc
          oddCore G = ⨆ i, K i := hWgen
          _ ≤ ⨆ i, E i := iSup_mono fun i => le_sup_left
      · calc
          (S : Subgroup G) = ⨆ i, Q i := hSgen
          _ ≤ ⨆ i, E i := iSup_mono fun i => le_sup_right
    · apply iSup_le
      intro i
      exact sup_le
        (calc K i ≤ ⨆ j, K j := le_iSup K i
          _ = oddCore G := hWgen.symm
          _ ≤ oddCore G ⊔ (S : Subgroup G) := le_sup_left)
        (calc Q i ≤ ⨆ j, Q j := le_iSup Q i
          _ = (S : Subgroup G) := hSgen.symm
          _ ≤ oddCore G ⊔ (S : Subgroup G) := le_sup_right)
  let _ : Fintype d.index := Fintype.ofFinite d.index
  let ℑ : Finset (Subgroup G) := Finset.univ.image E
  refine ⟨ℑ, ?_, ?_⟩
  · intro E' hE'
    rw [Finset.mem_image] at hE'
    obtain ⟨i, _hi, rfl⟩ := hE'
    exact ⟨hEsl i, by rw [hderived i]; exact hKomega i⟩
  · exact internalDirectProduct_image_of_iSup_centerless_commuting
      (oddCore G ⊔ (S : Subgroup G)) E hEgen
      (fun i => center_eq_bot_of_isSL2Two (hEsl i)) hEcomm

/-- The support-one product follows from the generic fixed-quotient value:
the alternative support size two would double that value. -/
public theorem generic_sl2_product_of_fixedQuotientCard_eq_card
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
      (G := G) (V := V) (S : Subgroup G))
    (hfixed : fixedQuotientCard (G := G) (V := V) (S : Subgroup G)
      (commutatorAction (oddCore G) V) =
        (Nat.card (S : Subgroup G) : ℚ)) :
    ∃ F : Finset (Subgroup G),
      (∀ E : Subgroup G, E ∈ F →
        IsSL2Two (↑E) ∧
          oneOmega (G := G) (V := V)
            ((commutator (↑E)).map E.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ (S : Subgroup G)) F := by
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
  have hcases :
      (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card = 1 ∨
        (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card = 2 := by
    omega
  rcases hcases with hsupportOne | hsupportTwo
  · exact local_generic_support_one_sl2_product S A hS hnorm hcoreEq
      hdecomp hW hWthree hmin a rfl hAmax hAcard d hsupportOne
  · have hOmegaCard := local_generic_coordinate_family_omega_card
      (S : Subgroup G) A hS hnorm hcoreEq hdecomp hW a rfl d
    have hfixedPow := fixedQuotientCard_oddCore_eq_pow_card_oneOmega
      (S : Subgroup G) hS hnorm hcoreEq hdecomp hW
    have htwice : fixedQuotientCard (G := G) (V := V) (S : Subgroup G)
        (commutatorAction (oddCore G) V) =
          (2 * Nat.card (S : Subgroup G) : ℚ) := by
      rw [hfixedPow, hOmegaCard, hsupportTwo, hScardPow]
      push_cast
      ring
    rw [hfixed] at htwice
    have hcardPos : (0 : ℚ) < Nat.card (S : Subgroup G) := by
      exact_mod_cast Nat.card_pos
    linarith

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
