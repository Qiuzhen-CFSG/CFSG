module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SupportCentralizers
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaCounting
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaNormalization

/-!
# Fixed indices on the complete omega action module

Every normalized omega factor contributes fixed index two. Independence of the four-point action modules and their fixed subgroups makes the total index a power of two.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Every normalized complete omega factor contributes one quadratic
two-dimensional coordinate to the Sylow action: its commutator module has
two fixed points under `S`, and the restricted `S`-action is quadratic. -/
public theorem oneOmega_sylow_coordinate_module
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S F : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hF : oneOmega (G := G) (V := V) F)
    (hcomm : ⁅F, S⁆ = F) :
    let U := commutatorAction F V
    let hUinv : IsInvariant S V U :=
      commutatorAction_isInvariant_of_normalizing_actor S F (hnorm F hF)
    let _ : IsInvariant S V U := hUinv
    Nat.card (↥(U ⊓ FixedPoints.subgroup S V)) = 2 ∧
      commutatorAction₂ S U = ⊥ := by
  classical
  let U := commutatorAction F V
  let hUinv : IsInvariant S V U :=
    commutatorAction_isInvariant_of_normalizing_actor S F (hnorm F hF)
  let _ : IsInvariant S V U := hUinv
  let _ : IsElementaryAbelian 2 U := isElementaryAbelian_subgroup U
  have hSnotCent : ¬ S ≤ Subgroup.centralizer (F : Set G) := by
    intro hcent
    have hbot : ⁅F, S⁆ = ⊥ := by
      rw [Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcent
    rw [hcomm] at hbot
    have hcard := hF.2.1
    rw [hbot] at hcard
    norm_num at hcard
  obtain ⟨sG, hsS, hsnotCent⟩ := Set.not_subset.mp hSnotCent
  let s : S := ⟨sG, hsS⟩
  have hsSupport : F ∈ omegaSupport (G := G) (V := V) S hnorm s :=
    (mem_omegaSupport_iff_not_mem_centralizer S hnorm s F hF).mpr
      hsnotCent
  have hsne : s ≠ 1 := by
    intro hsone
    apply hsnotCent
    rw [show sG = 1 from congrArg Subtype.val hsone]
    exact (Subgroup.centralizer (F : Set G)).one_mem
  let B : Subgroup G := Subgroup.zpowers (s : G)
  have hBcard : Nat.card B = 2 :=
    natCard_zpowers_eq_two_of_ne_one_of_elementary S hS s hsne
  have hBleS : B ≤ S := (Subgroup.zpowers_le).mpr s.property
  let hUinvB : IsInvariant B V U := by
    refine ⟨?_⟩
    intro b v
    exact IsInvariant.invariant (A := S) (G := V) (H := U)
      ⟨b, hBleS b.property⟩ v
  let _ : IsInvariant B V U := hUinvB
  have hBcomm : ⁅F, B⁆ = F := by
    exact commutator_oneOmega_zpowers_eq_self_of_mem_support
      S hnorm s F hF hsSupport
  have hBaction : commutatorAction B U ≠ ⊥ := by
    intro hbot
    have htriv : ActsTrivially (A := B) (G := U) :=
      actsTrivially_of_commutatorAction_eq_bot hbot
    have hBfix : B ≤ fixingSubgroup G (U : Set V) := by
      intro b hb
      rw [mem_fixingSubgroup_iff]
      intro u hu
      exact congrArg Subtype.val (htriv ⟨b, hb⟩ ⟨u, hu⟩)
    exact (Stellmacher.SectionOne.oneOmega_full_commutator_nontrivial
      F B hF hBcomm) hBfix
  have hBdata : Nat.card (FixedPoints.subgroup B U) = 2 ∧
      commutatorAction B U ≤ FixedPoints.subgroup B U :=
    cardTwo_action_fixed_card_two hBcard hF.2.2 hBaction
  have hfixNotSupport (t : S)
      (ht : F ∉ omegaSupport (G := G) (V := V) S hnorm t) :
      ∀ u : U, t • u = u := by
    intro u
    by_cases htone : t = 1
    · simp [htone]
    · let T : Subgroup G := Subgroup.zpowers (t : G)
      have hTcard : Nat.card T = 2 :=
        natCard_zpowers_eq_two_of_ne_one_of_elementary S hS t htone
      have hTcomm : ⁅F, T⁆ = ⊥ :=
        commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
          S hnorm t F hF ht
      have hTfix : T ≤ fixingSubgroup G (U : Set V) :=
        Stellmacher.SectionOne.oneOmega_card_two_centralizer_fixes_commutator
          F T hF hTcard hTcomm
      apply Subtype.ext
      exact ((mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp
        (hTfix (Subgroup.mem_zpowers (t : G)))) (u : V) u.property
  have hsameAction (t : S)
      (ht : F ∈ omegaSupport (G := G) (V := V) S hnorm t) :
      ∀ u : U, t • u = s • u := by
    intro u
    have hnotProd : F ∉
        omegaSupport (G := G) (V := V) S hnorm (t * s) := by
      rw [omegaSupport_mul S hnorm t s F]
      simp [ht, hsSupport]
    have hprodFix := hfixNotSupport (t * s) hnotProd u
    have htt : t * t = 1 := by
      simpa [pow_two] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hS.exponent_dvd_p t)
    calc
      t • u = t • ((t * s) • u) := by rw [hprodFix]
      _ = (t * (t * s)) • u := (mul_smul t (t * s) u).symm
      _ = s • u := by rw [← mul_assoc, htt, one_mul]
  have hfixedEq : FixedPoints.subgroup S U =
      FixedPoints.subgroup B U := by
    apply le_antisymm
    · intro u hu
      rw [FixedPoints.mem_subgroup]
      intro b
      have huS := (FixedPoints.mem_subgroup (M := S) (a := u)).mp hu
        ⟨b, hBleS b.property⟩
      apply Subtype.ext
      exact congrArg Subtype.val huS
    · intro u hu
      rw [FixedPoints.mem_subgroup]
      intro t
      by_cases ht : F ∈ omegaSupport (G := G) (V := V) S hnorm t
      · have hsfix := (FixedPoints.mem_subgroup (M := B) (a := u)).mp hu
          ⟨(s : G), Subgroup.mem_zpowers (s : G)⟩
        rw [hsameAction t ht u]
        apply Subtype.ext
        exact congrArg Subtype.val hsfix
      · exact hfixNotSupport t ht u
  have hfixedMap : (FixedPoints.subgroup S U).map U.subtype =
      U ⊓ FixedPoints.subgroup S V :=
    fixedPoints_subgroup_map_subtype_eq_inf U
  have hfixedCard : Nat.card (↥(U ⊓ FixedPoints.subgroup S V)) = 2 := by
    rw [← hfixedMap, Subgroup.card_map_of_injective U.subtype_injective,
      hfixedEq]
    exact hBdata.1
  have hcommEq : commutatorAction S U = commutatorAction B U := by
    apply le_antisymm
    · rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
      apply Subgroup.closure_mono
      rintro d ⟨t, u, rfl⟩
      by_cases ht : F ∈ omegaSupport (G := G) (V := V) S hnorm t
      · refine ⟨⟨(s : G), Subgroup.mem_zpowers (s : G)⟩, u, ?_⟩
        rw [hsameAction t ht u]
        rfl
      · refine ⟨1, u, ?_⟩
        rw [hfixNotSupport t ht u]
        simp
    · rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
      apply Subgroup.closure_mono
      rintro d ⟨b, u, rfl⟩
      refine ⟨⟨b, hBleS b.property⟩, u, ?_⟩
      rfl
  refine ⟨hfixedCard, ?_⟩
  apply commutatorAction₂_eq_bot_of_le_fixedPoints
  rw [hcommEq, hfixedEq]
  exact hBdata.2

/-- On the product of a finite family of complete omega action modules,
the Sylow fixed subgroup has one factor of order two for each module. -/
public theorem natCard_fixed_finset_sup_oneOmega_action
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (T : Finset (Subgroup G))
    (hT : ∀ F ∈ T, oneOmega (G := G) (V := V) F) :
    Nat.card (↥(T.sup (fun F => commutatorAction F V) ⊓
      FixedPoints.subgroup S V)) = 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert F T hFT ih =>
      have hF : oneOmega (G := G) (V := V) F := hT F (by simp)
      have hTrest : ∀ E ∈ T, oneOmega (G := G) (V := V) E := by
        intro E hE
        exact hT E (Finset.mem_insert_of_mem hE)
      let UF : Subgroup V := commutatorAction F V
      let UT : Subgroup V := T.sup (fun E => commutatorAction E V)
      have hdisjIndexed : Disjoint UF
          (⨆ E : {E : Subgroup G // E ∈ T},
            commutatorAction (E : Subgroup G) V) := by
        apply oneOmega_action_disjoint_iSup_of_distinct hdecomp F hF
          (fun E : {E : Subgroup G // E ∈ T} => (E : Subgroup G))
          (fun E => hTrest E E.property)
        intro E hEF
        exact hFT (hEF ▸ E.property)
      have hdisj : Disjoint UF UT := by
        dsimp only [UT]
        rw [finset_sup_apply_eq_iSup_subtype T]
        exact hdisjIndexed
      let hUFinv : IsInvariant S V UF :=
        commutatorAction_isInvariant_of_normalizing_actor S F (hnorm F hF)
      let hUTinv : IsInvariant S V UT :=
        isInvariant_finset_sup T (fun E => commutatorAction E V)
          (fun E hE =>
            commutatorAction_isInvariant_of_normalizing_actor S E
              (hnorm E (hTrest E hE)))
      let _ : IsInvariant S V UF := hUFinv
      let _ : IsInvariant S V UT := hUTinv
      have hfull : ⁅F, S⁆ = F :=
        commutator_oneOmega_sylow_eq_self S hnorm hcoreEq hdecomp hW F hF
      have hsingle : Nat.card (↥(UF ⊓ FixedPoints.subgroup S V)) = 2 :=
        (oneOmega_sylow_coordinate_module S F hS hnorm hF hfull).1
      have hproduct := natCard_inf_fixedPoints_sup_eq_mul
        (A := S) UF UT hdisj
      rw [Finset.sup_insert]
      change Nat.card (↥((UF ⊔ UT) ⊓ FixedPoints.subgroup S V)) =
        2 ^ (insert F T).card
      rw [hproduct, hsingle, ih hTrest,
        Finset.card_insert_of_notMem hFT, pow_succ, Nat.mul_comm]

/-- A finite family of normalized complete omega factors on which an
elementary abelian actor has full commutator contributes one fixed point
factor of order two per action module. -/
public theorem natCard_fixed_finset_sup_oneOmega_action_of_full_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (T : Finset (Subgroup G))
    (hT : ∀ F ∈ T, oneOmega (G := G) (V := V) F)
    (hfull : ∀ F ∈ T, ⁅F, S⁆ = F) :
    Nat.card (↑(T.sup (fun F => commutatorAction F V) ⊓
      FixedPoints.subgroup S V)) = 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert F T hFT ih =>
      have hF : oneOmega (G := G) (V := V) F := hT F (by simp)
      have hTrest : ∀ E ∈ T, oneOmega (G := G) (V := V) E := by
        intro E hE
        exact hT E (Finset.mem_insert_of_mem hE)
      let UF : Subgroup V := commutatorAction F V
      let UT : Subgroup V := T.sup (fun E => commutatorAction E V)
      have hdisjIndexed : Disjoint UF
          (⨆ E : {E : Subgroup G // E ∈ T},
            commutatorAction (E : Subgroup G) V) := by
        apply oneOmega_action_disjoint_iSup_of_distinct hdecomp F hF
          (fun E : {E : Subgroup G // E ∈ T} => (E : Subgroup G))
          (fun E => hTrest E E.property)
        intro E hEF
        exact hFT (hEF ▸ E.property)
      have hdisj : Disjoint UF UT := by
        dsimp only [UT]
        rw [finset_sup_apply_eq_iSup_subtype T]
        exact hdisjIndexed
      let hUFinv : IsInvariant S V UF :=
        commutatorAction_isInvariant_of_normalizing_actor S F (hnorm F hF)
      let hUTinv : IsInvariant S V UT :=
        isInvariant_finset_sup T (fun E => commutatorAction E V)
          (fun E hE =>
            commutatorAction_isInvariant_of_normalizing_actor S E
              (hnorm E (hTrest E hE)))
      let _ : IsInvariant S V UF := hUFinv
      let _ : IsInvariant S V UT := hUTinv
      have hsingle : Nat.card (↑(UF ⊓ FixedPoints.subgroup S V)) = 2 :=
        (oneOmega_sylow_coordinate_module S F hS hnorm hF
          (hfull F (by simp))).1
      have hproduct := natCard_inf_fixedPoints_sup_eq_mul
        (A := S) UF UT hdisj
      rw [Finset.sup_insert]
      change Nat.card (↑((UF ⊔ UT) ⊓ FixedPoints.subgroup S V)) =
        2 ^ (insert F T).card
      rw [hproduct, hsingle,
        ih hTrest (fun E hE => hfull E (Finset.mem_insert_of_mem hE)),
        Finset.card_insert_of_notMem hFT, pow_succ, Nat.mul_comm]

public theorem commutatorAction_eq_iSup_of_eq_iSup
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    {A : Subgroup G} {I : Sort*} (K : I → Subgroup G)
    (hA : A = ⨆ i, K i) :
    commutatorAction A V = ⨆ i, commutatorAction (K i) V := by
  apply le_antisymm
  · let U : Subgroup V := ⨆ i, commutatorAction (K i) V
    let P : Subgroup G :=
      { carrier := {a : G | ∀ w : V, w⁻¹ * (a • w) ∈ U}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb w
          have hbmem := hb w
          have hamem := ha (b • w)
          have hmul : w⁻¹ * ((a * b) • w) =
              (w⁻¹ * (b • w)) * ((b • w)⁻¹ * (a • (b • w))) := by
            simp [smul_smul, mul_assoc]
          rw [hmul]
          exact U.mul_mem hbmem hamem
        inv_mem' := by
          intro a ha w
          have hmem := ha (a⁻¹ • w)
          have hinv : w⁻¹ * (a⁻¹ • w) =
              ((a⁻¹ • w)⁻¹ * (a • (a⁻¹ • w)))⁻¹ := by
            simp [smul_smul]
          rw [hinv]
          exact U.inv_mem hmem }
    have hKleP (i : I) : K i ≤ P := by
      intro a ha w
      apply (show commutatorAction (K i) V ≤ U from
        le_iSup (fun j => commutatorAction (K j) V) i)
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨a, ha⟩, w, rfl⟩
    have hAleP : A ≤ P := by
      rw [hA]
      exact iSup_le hKleP
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := U)).2 ?_
    rintro x ⟨a, w, rfl⟩
    exact hAleP a.property w
  · refine iSup_le ?_
    intro i
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro x ⟨a, w, rfl⟩
    refine ⟨⟨a, ?_⟩, w, rfl⟩
    rw [hA]
    exact le_iSup (fun j => K j) i a.property

/-- The complete omega action module has fixed quotient `2^r`, where `r`
is the number of complete omega factors. -/
public theorem fixedQuotientCard_oddCore_eq_pow_card_oneOmega
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆) :
    fixedQuotientCard (G := G) (V := V) S
        (commutatorAction (oddCore G) V) =
      (2 : ℚ) ^ (oneOmegaFinset (G := G) (V := V)).card := by
  classical
  let Ω := oneOmegaFinset (G := G) (V := V)
  let U : Subgroup V := Ω.sup (fun F => commutatorAction F V)
  have hUeq : commutatorAction (oddCore G) V = U := by
    calc
      commutatorAction (oddCore G) V =
          commutatorAction (oneOmegaGenerated (G := G) (V := V)) V := by
        rw [hcoreEq]
      _ = ⨆ F : {F : Subgroup G // F ∈ Ω},
          commutatorAction (F : Subgroup G) V := by
        apply commutatorAction_eq_iSup_of_eq_iSup
        exact hdecomp.part_a.1
      _ = U := (finset_sup_apply_eq_iSup_subtype Ω
        (fun F => commutatorAction F V)).symm
  have hΩ (F : Subgroup G) (hFmem : F ∈ Ω) :
      oneOmega (G := G) (V := V) F :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) F).mp hFmem
  have hUcard : Nat.card U = 4 ^ Ω.card :=
    natCard_finset_sup_oneOmega_action hdecomp Ω hΩ
  have hfixedCard : Nat.card (↥(U ⊓ FixedPoints.subgroup S V)) =
      2 ^ Ω.card :=
    natCard_fixed_finset_sup_oneOmega_action
      S hS hnorm hcoreEq hdecomp hW Ω hΩ
  unfold fixedQuotientCard
  rw [hUeq, hUcard, hfixedCard]
  norm_num [Nat.cast_pow, ← div_pow]
  rfl

private theorem disjoint_sup_left_of_disjoint_sup_of_disjoint
    {V : Type u} [Group V] [IsMulCommutative V]
    (A B C : Subgroup V) (hA : Disjoint A (B ⊔ C))
    (hB : Disjoint B C) : Disjoint (A ⊔ B) C := by
  let _ : CommGroup V := IsMulCommutative.instCommGroup
  rw [Subgroup.disjoint_def]
  intro x hxAB hxC
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hxAB
  have haBC : a ∈ B ⊔ C := by
    have hxBC : x ∈ B ⊔ C := (show C ≤ B ⊔ C from le_sup_right) hxC
    have hbinvBC : b⁻¹ ∈ B ⊔ C :=
      (show B ≤ B ⊔ C from le_sup_left) (B.inv_mem hb)
    have hprod := (B ⊔ C).mul_mem hxBC hbinvBC
    have hprodEq : x * b⁻¹ = a := by rw [← hab]; simp
    exact hprodEq ▸ hprod
  have haone : a = 1 := Subgroup.disjoint_def.mp hA ha haBC
  have hbx : b = x := by simpa [haone] using hab
  have hbC : b ∈ C := hbx.symm ▸ hxC
  have hbone : b = 1 := Subgroup.disjoint_def.mp hB hb hbC
  rw [← hab, haone, hbone, mul_one]

/-- Disjoint subfamilies of the complete omega action coordinates generate
disjoint subgroups. -/
public theorem disjoint_finset_sup_oneOmega_action
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (T U : Finset (Subgroup G))
    (hT : ∀ F ∈ T, oneOmega (G := G) (V := V) F)
    (hU : ∀ F ∈ U, oneOmega (G := G) (V := V) F)
    (hTU : Disjoint T U) :
    Disjoint (T.sup (fun F => commutatorAction F V))
      (U.sup (fun F => commutatorAction F V)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert F T hFT ih =>
      have hF : oneOmega (G := G) (V := V) F := hT F (by simp)
      have hTrest : ∀ E ∈ T, oneOmega (G := G) (V := V) E := by
        intro E hE
        exact hT E (Finset.mem_insert_of_mem hE)
      have hFnotU : F ∉ U := by
        exact (Finset.disjoint_left.mp hTU) (by simp) 
      have hTdisjU : Disjoint T U := by
        rw [Finset.disjoint_left]
        intro E hET hEU
        exact (Finset.disjoint_left.mp hTU)
          (Finset.mem_insert_of_mem hET) hEU
      have hFnotUnion : F ∉ T ∪ U := by simp [hFT, hFnotU]
      have hrest : Disjoint
          (T.sup (fun E => commutatorAction E V))
          (U.sup (fun E => commutatorAction E V)) :=
        ih hTrest hTdisjU
      have hFall : ∀ E ∈ T ∪ U,
          oneOmega (G := G) (V := V) E := by
        intro E hE
        rw [Finset.mem_union] at hE
        exact hE.elim (hTrest E) (hU E)
      have hFdisj : Disjoint (commutatorAction F V)
          (T.sup (fun E => commutatorAction E V) ⊔
            U.sup (fun E => commutatorAction E V)) := by
        rw [← Finset.sup_union]
        rw [finset_sup_apply_eq_iSup_subtype (T ∪ U)]
        apply oneOmega_action_disjoint_iSup_of_distinct hdecomp F hF
          (fun E : {E : Subgroup G // E ∈ T ∪ U} => (E : Subgroup G))
          (fun E => hFall E E.property)
        intro E hEF
        exact hFnotUnion (hEF ▸ E.property)
      rw [Finset.sup_insert]
      exact disjoint_sup_left_of_disjoint_sup_of_disjoint
        (commutatorAction F V)
        (T.sup (fun E => commutatorAction E V))
        (U.sup (fun E => commutatorAction E V)) hFdisj hrest

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
