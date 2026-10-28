module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaNormalization
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support

/-!
# Cardinality and generators of generic coordinate families

The complete omega family gives an internal product. Independent local binary characters count the Sylow subgroup and show that one point from each coordinate together with the distinguished point generates it.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- The product half of alternative (1.6)(c): if every local factor is in
the generic branch, the entire odd core is the internal direct product of
the complete ambient `oneOmega` family.  The later support count decides
between (c) and (d) and supplies the fixed-quotient formula. -/
public theorem omega_product_of_all_local_factors_generic
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hlocal : RankOneAssemblyLocalHypothesis
      (G := G) (V := V) (S : Subgroup G))
    (hgeneric : RankOneAssemblyGenericHypothesis
      (G := G) (V := V) (S : Subgroup G)) :
    ∃ F : Finset (Subgroup G),
      (∀ X : Subgroup G, X ∈ F → oneOmega (G := G) (V := V) X) ∧
      IsInternalDirectProduct (oddCore G) F := by
  have hlocalLe : ∀ A : Subgroup G,
      oneAmax (G := G) (V := V) (S : Subgroup G) A →
      Nat.card A = 2 →
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G),
        (S : Subgroup G)⁆ ≤
          oneOmegaGenerated (G := G) (V := V) := by
    intro A hAmax hAcard
    exact local_commutator_le_oneOmegaGenerated_of_generic
      (S : Subgroup G) A hlocal hAmax hAcard (hgeneric A hAmax hAcard)
  have hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V) :=
    oddCore_eq_oneOmegaGenerated_of_local_commutators
      h S hS_elem hScard hW hlocalLe
  have hdecomp := oneOmegaGenerated_decomposition h S hWthree
  refine ⟨oneOmegaFinset (G := G) (V := V), ?_, ?_⟩
  · intro X hX
    exact (mem_oneOmegaFinset_iff (G := G) (V := V) X).mp hX
  · rw [hcoreEq]
    exact hdecomp.part_a

/-- Independent order-two coordinates detected by independent characters
have the expected elementary-abelian order.  The extra subgroup `A` is
included in the induction: although pairwise-disjoint order-two subgroups
need not be jointly independent, the character belonging to the newly
adjoined coordinate kills `A` and all earlier coordinates but not the new
one, ruling out the diagonal obstruction. -/
private theorem natCard_eq_pow_of_coordinate_characters
    {S ι : Type*} [Group S] [Finite S] [IsMulCommutative S]
    [Finite ι] (Q : ι → Type*) [∀ i, Group (Q i)]
    (A : Subgroup S) (B : ι → Subgroup S) (χ : ∀ i, S →* Q i)
    (hAcard : Nat.card A = 2)
    (hBcard : ∀ i, Nat.card (B i) = 2)
    (hAker : ∀ i, A ≤ (χ i).ker)
    (hBker : ∀ i j, i ≠ j → B j ≤ (χ i).ker)
    (hBnot : ∀ i, ¬ B i ≤ (χ i).ker)
    (hgen : (⊤ : Subgroup S) = A ⊔ ⨆ i, B i) :
    Nat.card S = 2 ^ (Nat.card ι + 1) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hind : ∀ T : Finset ι,
      Nat.card (T.sup B : Subgroup S) = 2 ^ T.card ∧
        Disjoint A (T.sup B : Subgroup S) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
        have hCker : T.sup B ≤ (χ i).ker := by
          apply Finset.sup_le
          intro j hj
          exact hBker i j (fun hji => hi (hji ▸ hj))
        have hdisjBC : Disjoint (B i) (T.sup B) := by
          rw [Subgroup.disjoint_def]
          intro y hyB hyC
          by_contra hyne
          have hBeq : B i = Subgroup.zpowers y :=
            subgroup_card_two_eq_zpowers_of_mem_ne_one
              (B i) (hBcard i) hyB hyne
          apply hBnot i
          rw [hBeq, Subgroup.zpowers_le]
          exact hCker hyC
        have hcommBC : T.sup B ≤
            Subgroup.centralizer ((B i : Subgroup S) : Set S) := by
          rw [Subgroup.le_centralizer_iff]
          intro c hc b hb
          exact IsMulCommutative.is_comm.comm b c
        have hcardInsert : Nat.card ((insert i T).sup B : Subgroup S) =
            2 ^ (insert i T).card := by
          rw [Finset.sup_insert,
            natCard_sup_eq_mul_of_disjoint_of_le_centralizer
              (B i) (T.sup B) hdisjBC hcommBC,
            hBcard i, ih.1, Finset.card_insert_of_notMem hi, pow_succ,
            Nat.mul_comm]
        have hdisjA : Disjoint A ((insert i T).sup B) := by
          rw [Finset.sup_insert, Subgroup.disjoint_def]
          intro y hyA hyJoin
          let hBinormal : (B i).Normal :=
            Subgroup.normal_of_isMulCommutative (B i)
          let _ : (B i).Normal := hBinormal
          rcases Subgroup.mem_sup_of_normal_left.mp hyJoin with
            ⟨b, hb, c, hc, hbc⟩
          have hyker : y ∈ (χ i).ker := hAker i hyA
          have hcker : c ∈ (χ i).ker := hCker hc
          have hbker : b ∈ (χ i).ker := by
            have hbEq : b = y * c⁻¹ := by
              calc
                b = (b * c) * c⁻¹ := by simp
                _ = y * c⁻¹ := by rw [hbc]
            rw [hbEq]
            exact (χ i).ker.mul_mem hyker ((χ i).ker.inv_mem hcker)
          have hbone : b = 1 := by
            by_contra hbne
            apply hBnot i
            rw [show B i = Subgroup.zpowers b from
              subgroup_card_two_eq_zpowers_of_mem_ne_one
                (B i) (hBcard i) hb hbne,
              Subgroup.zpowers_le]
            exact hbker
          have hyC : y ∈ T.sup B := by
            have hcy : c = y := by simpa [hbone] using hbc
            rwa [← hcy]
          exact Subgroup.disjoint_def.mp ih.2 hyA hyC
        exact ⟨hcardInsert, hdisjA⟩
  have hall := hind Finset.univ
  have hjoinCard : Nat.card
      (A ⊔ (Finset.univ.sup B : Subgroup S) : Subgroup S) =
      2 ^ (Nat.card ι + 1) := by
    have hcomm : (Finset.univ.sup B : Subgroup S) ≤
        Subgroup.centralizer ((A : Subgroup S) : Set S) := by
      rw [Subgroup.le_centralizer_iff]
      intro b hb a ha
      exact IsMulCommutative.is_comm.comm a b
    rw [natCard_sup_eq_mul_of_disjoint_of_le_centralizer
        A (Finset.univ.sup B) hall.2 hcomm,
      hAcard, hall.1, Finset.card_univ, Nat.card_eq_fintype_card,
      pow_succ, Nat.mul_comm]
  calc
    Nat.card S = Nat.card (⊤ : Subgroup S) := Subgroup.card_top.symm
    _ = Nat.card
        (A ⊔ (Finset.univ.sup B : Subgroup S) : Subgroup S) := by
      rw [show (⊤ : Subgroup S) =
          A ⊔ (Finset.univ.sup B : Subgroup S) by
        simpa only [Finset.sup_univ_eq_iSup] using hgen]
    _ = 2 ^ (Nat.card ι + 1) := hjoinCard

/-- The simultaneous local coordinates have exactly one independent
order-two direction each, in addition to `A`.  Their characters are the
conjugation actions on the distinct lifted omega factors. -/
public theorem local_generic_coordinate_family_sylow_card
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (W S A : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hAS : A ≤ S)
    (hAcard : Nat.card A = 2)
    (hWcent : W ≤ Subgroup.centralizer (A : Set G))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (d : LocalGenericCoordinateFamily (G := G) (V := V) W S A) :
    Nat.card S = 2 ^ (Nat.card d.index + 1) := by
  classical
  let _ : Finite d.index := d.index_finite
  let _ : Fintype d.index := Fintype.ofFinite d.index
  have hcoordinateNotLe (i : d.index) : ¬ d.coordinate i ≤ A := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [d.coordinate_card_four i, hAcard] at hc
    omega
  choose xG hxCoordinate hxNotA using fun i : d.index =>
    Set.not_subset.mp (hcoordinateNotLe i)
  let x : d.index → S := fun i =>
    ⟨xG i, d.coordinate_le_S i (hxCoordinate i)⟩
  let AS : Subgroup S := A.subgroupOf S
  let B : d.index → Subgroup S := fun i => Subgroup.zpowers (x i)
  let χ : ∀ i : d.index, S →* MulAut (d.factor i) := fun i =>
    omegaFactorCharacter S (d.factor i) (d.factor_normalized i)
  have hAScard : Nat.card AS = 2 := by
    rw [natCard_subgroupOf_eq A S hAS]
    exact hAcard
  have hxne (i : d.index) : x i ≠ 1 := by
    intro hxi
    apply hxNotA i
    change (x i : G) ∈ A
    rw [hxi]
    exact A.one_mem
  have hBcard (i : d.index) : Nat.card (B i) = 2 := by
    have hpow : (x i) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hS.exponent_dvd_p (x i)
    dsimp only [B]
    rw [Nat.card_zpowers, orderOf_eq_prime hpow (hxne i)]
  have hfactorLeW (i : d.index) : d.factor i ≤ W := by
    calc
      d.factor i ≤ ⨆ j, d.factor j := le_iSup d.factor i
      _ = W := d.factor_generated.symm
  have hASker (i : d.index) : AS ≤ (χ i).ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply (omegaFactorCharacter_eq_one_iff_mem_centralizer
      S (d.factor i) (d.factor_normalized i) a).2
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact ((Subgroup.mem_centralizer_iff.mp
      (hWcent (hfactorLeW i hf))) (a : G) ha).symm
  have hBker (i j : d.index) (hij : i ≠ j) : B j ≤ (χ i).ker := by
    have hfactorNe : d.factor i ≠ d.factor j := fun h =>
      hij (d.factor_injective h)
    have hdisj : Disjoint (d.factor i) (d.factor j) :=
      hdecomp.part_a.2.2.1 (d.factor i)
        ((mem_oneOmegaFinset_iff (G := G) (V := V) _).mpr
          (d.factor_omega i))
        (d.factor j)
        ((mem_oneOmegaFinset_iff (G := G) (V := V) _).mpr
          (d.factor_omega j)) hfactorNe
    have hcommLeI : ⁅d.factor i, Subgroup.zpowers (x j : G)⁆ ≤
        d.factor i := by
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.zpowers_le).mpr
          (d.factor_normalized i (x j).property)))
    have hcommLeJ : ⁅d.factor i, Subgroup.zpowers (x j : G)⁆ ≤
        d.factor j := by
      calc
        ⁅d.factor i, Subgroup.zpowers (x j : G)⁆ ≤
            ⁅W, d.coordinate j⁆ :=
          Subgroup.commutator_mono (hfactorLeW i)
            ((Subgroup.zpowers_le).mpr (hxCoordinate j))
        _ = d.factor j := d.local_commutator j
    have hcommBot : ⁅d.factor i, Subgroup.zpowers (x j : G)⁆ = ⊥ := by
      apply le_antisymm
      · exact (le_inf hcommLeI hcommLeJ).trans hdisj.eq_bot.le
      · exact bot_le
    intro y hy
    rw [MonoidHom.mem_ker]
    apply (omegaFactorCharacter_eq_one_iff_mem_centralizer
      S (d.factor i) (d.factor_normalized i) y).2
    have hcent : Subgroup.zpowers (x j : G) ≤
        Subgroup.centralizer (d.factor i : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      exact hcommBot
    apply hcent
    have hymap : (y : G) ∈ (B j).map S.subtype := ⟨y, hy, rfl⟩
    rw [show (B j).map S.subtype = Subgroup.zpowers (x j : G) by
      change (Subgroup.zpowers (x j)).map S.subtype =
        Subgroup.zpowers (x j : G)
      rw [MonoidHom.map_zpowers]
      rfl] at hymap
    exact hymap
  have hBnot (i : d.index) : ¬ B i ≤ (χ i).ker := by
    intro hle
    have hxker : x i ∈ (χ i).ker := hle (Subgroup.mem_zpowers (x i))
    have hxcent : (x i : G) ∈
        Subgroup.centralizer (d.factor i : Set G) :=
      (omegaFactorCharacter_eq_one_iff_mem_centralizer
        S (d.factor i) (d.factor_normalized i) (x i)).1
        (MonoidHom.mem_ker.mp hxker)
    have hbot : ⁅d.factor i, Subgroup.zpowers (x i : G)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact hxcent
    have hfull := (d.point_coordinate i (x i : G) (hxCoordinate i)
      (hxNotA i)).1
    have hcard := (d.factor_omega i).2.1
    rw [hfull.symm.trans hbot] at hcard
    norm_num at hcard
  have hcoordinateEq (i : d.index) :
      d.coordinate i = A ⊔ Subgroup.zpowers (x i : G) := by
    have hBle : Subgroup.zpowers (x i : G) ≤ d.coordinate i :=
      (Subgroup.zpowers_le).mpr (hxCoordinate i)
    have hdisj : Disjoint A (Subgroup.zpowers (x i : G)) := by
      rw [Subgroup.disjoint_def]
      intro y hyA hyB
      by_contra hyne
      have hAeq : A = Subgroup.zpowers y :=
        subgroup_card_two_eq_zpowers_of_mem_ne_one A hAcard hyA hyne
      have hBeq : Subgroup.zpowers (x i : G) = Subgroup.zpowers y :=
        subgroup_card_two_eq_zpowers_of_mem_ne_one
          (Subgroup.zpowers (x i : G))
          (natCard_zpowers_eq_two_of_ne_one_of_elementary
            S hS (x i) (hxne i)) hyB hyne
      apply hxNotA i
      rw [hAeq, ← hBeq]
      exact Subgroup.mem_zpowers (x i : G)
    have hcomm : Subgroup.zpowers (x i : G) ≤
        Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      intro a ha b hb
      exact congrArg Subtype.val
        (hS.toIsMulCommutative.is_comm.comm
          ⟨a, hAS ha⟩
          ⟨b, (d.coordinate_le_S i) (hBle hb)⟩).symm
    have hcardSup : Nat.card
        (A ⊔ Subgroup.zpowers (x i : G) : Subgroup G) = 4 := by
      rw [natCard_sup_eq_mul_of_disjoint_of_le_centralizer
        A (Subgroup.zpowers (x i : G)) hdisj hcomm,
        hAcard]
      have hambientCard : Nat.card (Subgroup.zpowers (x i : G)) = 2 :=
        natCard_zpowers_eq_two_of_ne_one_of_elementary S hS (x i) (hxne i)
      rw [hambientCard]
    symm
    apply Subgroup.eq_of_le_of_card_ge
      (sup_le (d.A_le_coordinate i) hBle)
    rw [d.coordinate_card_four i, hcardSup]
  have hgen : (⊤ : Subgroup S) = AS ⊔ ⨆ i, B i := by
    apply Subgroup.map_injective S.subtype_injective
    calc
      (⊤ : Subgroup S).map S.subtype = S := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = A ⊔ ⨆ i, d.coordinate i := d.coordinate_generated
      _ = A ⊔ ⨆ i, (A ⊔ Subgroup.zpowers (x i : G)) := by
        simp_rw [hcoordinateEq]
      _ = A ⊔ ⨆ i, Subgroup.zpowers (x i : G) := by
        apply le_antisymm
        · apply sup_le le_sup_left
          apply iSup_le
          intro i
          apply sup_le le_sup_left
          exact (show Subgroup.zpowers (x i : G) ≤
              ⨆ j, Subgroup.zpowers (x j : G) from
            le_iSup (fun j => Subgroup.zpowers (x j : G)) i) |>.trans
              le_sup_right
        · apply sup_le le_sup_left
          apply iSup_le
          intro i
          exact (le_sup_right : Subgroup.zpowers (x i : G) ≤
              A ⊔ Subgroup.zpowers (x i : G)) |>.trans
            (le_iSup (fun j => A ⊔ Subgroup.zpowers (x j : G)) i) |>.trans
              le_sup_right
      _ = AS.map S.subtype ⊔ ⨆ i, (B i).map S.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hAS]
        apply congrArg (fun Z : Subgroup G => A ⊔ Z)
        apply congrArg iSup
        funext i
        symm
        change (Subgroup.zpowers (x i)).map S.subtype =
          Subgroup.zpowers (x i : G)
        rw [MonoidHom.map_zpowers]
        rfl
      _ = (AS ⊔ ⨆ i, B i).map S.subtype := by
        rw [Subgroup.map_sup, Subgroup.map_iSup]
  exact natCard_eq_pow_of_coordinate_characters
    (fun i => MulAut (d.factor i)) AS B χ hAScard hBcard
    hASker hBker hBnot hgen

/-- Choosing any point outside `A` in each local order-four coordinate
recovers the full Sylow subgroup from `A` and the cyclic point subgroups. -/
public theorem local_generic_coordinate_family_generated_by_points
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (W S A : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hAS : A ≤ S) (hAcard : Nat.card A = 2)
    (d : LocalGenericCoordinateFamily (G := G) (V := V) W S A)
    (x : d.index → S)
    (hxCoordinate : ∀ i, (x i : G) ∈ d.coordinate i)
    (hxNotA : ∀ i, (x i : G) ∉ A) :
    S = A ⊔ ⨆ i, Subgroup.zpowers (x i : G) := by
  have hxne (i : d.index) : x i ≠ 1 := by
    intro hxi
    apply hxNotA i
    rw [hxi]
    exact A.one_mem
  have hcoordinateEq (i : d.index) :
      d.coordinate i = A ⊔ Subgroup.zpowers (x i : G) := by
    have hBle : Subgroup.zpowers (x i : G) ≤ d.coordinate i :=
      (Subgroup.zpowers_le).mpr (hxCoordinate i)
    have hdisj : Disjoint A (Subgroup.zpowers (x i : G)) := by
      rw [Subgroup.disjoint_def]
      intro y hyA hyB
      by_contra hyne
      have hAeq : A = Subgroup.zpowers y :=
        subgroup_card_two_eq_zpowers_of_mem_ne_one A hAcard hyA hyne
      have hBeq : Subgroup.zpowers (x i : G) = Subgroup.zpowers y :=
        subgroup_card_two_eq_zpowers_of_mem_ne_one
          (Subgroup.zpowers (x i : G))
          (natCard_zpowers_eq_two_of_ne_one_of_elementary
            S hS (x i) (hxne i)) hyB hyne
      apply hxNotA i
      rw [hAeq, ← hBeq]
      exact Subgroup.mem_zpowers (x i : G)
    have hcomm : Subgroup.zpowers (x i : G) ≤
        Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      intro a ha b hb
      exact congrArg Subtype.val
        (hS.toIsMulCommutative.is_comm.comm
          ⟨a, hAS ha⟩
          ⟨b, (d.coordinate_le_S i) (hBle hb)⟩).symm
    have hcardSup : Nat.card
        (A ⊔ Subgroup.zpowers (x i : G) : Subgroup G) = 4 := by
      rw [natCard_sup_eq_mul_of_disjoint_of_le_centralizer
        A (Subgroup.zpowers (x i : G)) hdisj hcomm,
        hAcard,
        natCard_zpowers_eq_two_of_ne_one_of_elementary
          S hS (x i) (hxne i)]
    symm
    apply Subgroup.eq_of_le_of_card_ge
      (sup_le (d.A_le_coordinate i) hBle)
    rw [d.coordinate_card_four i, hcardSup]
  calc
    S = A ⊔ ⨆ i, d.coordinate i := d.coordinate_generated
    _ = A ⊔ ⨆ i, (A ⊔ Subgroup.zpowers (x i : G)) := by
      simp_rw [hcoordinateEq]
    _ = A ⊔ ⨆ i, Subgroup.zpowers (x i : G) := by
      apply le_antisymm
      · apply sup_le le_sup_left
        apply iSup_le
        intro i
        exact sup_le le_sup_left
          ((le_iSup (fun j => Subgroup.zpowers (x j : G)) i).trans
            le_sup_right)
      · apply sup_le le_sup_left
        apply iSup_le
        intro i
        exact (le_sup_right : Subgroup.zpowers (x i : G) ≤
          A ⊔ Subgroup.zpowers (x i : G)) |>.trans
            (le_iSup (fun j => A ⊔ Subgroup.zpowers (x j : G)) i) |>.trans
              le_sup_right

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
