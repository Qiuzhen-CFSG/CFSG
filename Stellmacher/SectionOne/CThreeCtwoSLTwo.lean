module

public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# A three-group and an inverting involution generate `SL₂(2)`

Let `F` and `B` have orders three and two, with `B` normalizing `F` and
`[F,B] = F`.  Their join has order six.  Its action on the three left cosets
of `B` is faithful: a nontrivial core would make the order-two subgroup
normal, while the two normal complementary factors would then commute,
contrary to the full-commutator hypothesis.  Thus the join is the full
permutation group on three points.

For a concrete identification with `SL₂(2)`, the proof imports its faithful
three-point projective-line equivalence from the intrinsic Theory module
`Theory.GroupTheory.SpecificGroups.SLTwoPermThree`. This is the
order-six recognition step used in the support-one product assembly in
Stellmacher's Lemma (1.6), journal p. 18; see
`refs/latex/stellmacher-n-group.tex`, lines 487--506.
The resulting three-point permutation model is also exported explicitly
for the quotient-model conversion in the terminal classification of (8.2).
-/

open scoped Pointwise commutatorElement

namespace Stellmacher.SectionOne

universe u

private abbrev PLine2 := Projectivization (ZMod 2) (Fin 2 → ZMod 2)

open SLTwoPermThree (projectiveLineTwo_card sl2EquivPermProjectiveLine)

/-- The projective-line action identifies `SL₂(2)` with `S₃`. -/
public theorem sl2Two_equiv_perm_three :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3)) :=
  SLTwoPermThree.sl2Two_equiv_perm_three

/-- A normal order-three subgroup and an order-two subgroup acting with full
commutator generate a copy of `SL₂(2)`. -/
public theorem isSL2Two_sup_of_card_three_card_two_full_commutator
    {G : Type u} [Group G] [Finite G]
    (F B : Subgroup G)
    (hFcard : Nat.card F = 3)
    (hBcard : Nat.card B = 2)
    (hBnorm : B ≤ Subgroup.normalizer (F : Set G))
    (hcomm : ⁅F, B⁆ = F) :
    IsSL2Two (↥(F ⊔ B)) := by
  let E : Subgroup G := F ⊔ B
  let FE : Subgroup E := F.subgroupOf E
  let BE : Subgroup E := B.subgroupOf E
  have hFEcard : Nat.card FE = 3 := by
    rw [show Nat.card FE = Nat.card F from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
    exact hFcard
  have hBEcard : Nat.card BE = 2 := by
    rw [show Nat.card BE = Nat.card B from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact hBcard
  let _ : FE.Normal := by
    dsimp only [FE]
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact sup_le F.le_normalizer hBnorm
  have hdis : Disjoint FE BE := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hFEcard, hBEcard]
    decide
  have hsup : FE ⊔ BE = ⊤ := by
    calc
      FE ⊔ BE = (F ⊔ B).subgroupOf E :=
        (Subgroup.subgroupOf_sup le_sup_left le_sup_right).symm
      _ = E.subgroupOf E := rfl
      _ = ⊤ := Subgroup.subgroupOf_self E
  have hcomp : FE.IsComplement' BE := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul FE BE, hsup]
    rfl
  have hEcard : Nat.card E = 6 := by
    have hcard := hcomp.card_mul_card
    rw [hFEcard, hBEcard] at hcard
    norm_num at hcard ⊢
    exact hcard.symm
  have hmapFE : FE.map E.subtype = F := by
    exact Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hmapBE : BE.map E.subtype = B := by
    exact Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hBEnotNormal : ¬ BE.Normal := by
    intro hBEnormal
    let _ : BE.Normal := hBEnormal
    have hlocal : ⁅FE, BE⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_of_disjoint hdis
    have hambient : ⁅F, B⁆ = ⊥ := by
      calc
        ⁅F, B⁆ = ⁅FE.map E.subtype, BE.map E.subtype⁆ := by
          rw [hmapFE, hmapBE]
        _ = ⁅FE, BE⁆.map E.subtype :=
          (Subgroup.map_commutator FE BE E.subtype).symm
        _ = ⊥ := by rw [hlocal, Subgroup.map_bot]
    have hFbot : F = ⊥ := hcomm.symm.trans hambient
    rw [hFbot] at hFcard
    norm_num at hFcard
  have hcorebot : BE.normalCore = ⊥ := by
    let K : Subgroup BE := BE.normalCore.subgroupOf BE
    let hprime : Fact (Nat.Prime (Nat.card BE)) :=
      ⟨by rw [hBEcard]; decide⟩
    let _ : Fact (Nat.Prime (Nat.card BE)) := hprime
    rcases K.eq_bot_or_eq_top_of_prime_card with hKbot | hKtop
    · apply le_antisymm
      · intro x hx
        have hxBE : x ∈ BE := BE.normalCore_le hx
        have hxK : (⟨x, hxBE⟩ : BE) ∈ K := hx
        rw [hKbot] at hxK
        have hxone : (⟨x, hxBE⟩ : BE) = 1 := by simpa using hxK
        exact congrArg Subtype.val hxone
      · exact bot_le
    · have hcoreeq : BE.normalCore = BE := by
        apply le_antisymm BE.normalCore_le
        intro x hx
        have hxK : (⟨x, hx⟩ : BE) ∈ K := by
          rw [hKtop]
          exact Subgroup.mem_top _
        exact hxK
      apply False.elim
      apply hBEnotNormal
      exact hcoreeq ▸ BE.normalCore_normal
  let Q := E ⧸ BE
  let psi : E →* Equiv.Perm Q := MulAction.toPermHom E Q
  have hpsiker : psi.ker = ⊥ := by
    calc
      psi.ker = BE.normalCore := (Subgroup.normalCore_eq_ker BE).symm
      _ = ⊥ := hcorebot
  have hpsiinj : Function.Injective psi := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hpsiker
  have hQcard : Nat.card Q = 3 := by
    calc
      Nat.card Q = BE.index := (Subgroup.index_eq_card BE).symm
      _ = Nat.card FE := hcomp.index_eq_card
      _ = 3 := hFEcard
  let iQ : Fintype Q := Fintype.ofFinite Q
  let _ : Fintype Q := iQ
  let iP : Fintype PLine2 := Fintype.ofFinite PLine2
  let _ : Fintype PLine2 := iP
  let eQ : Q ≃ PLine2 := Fintype.equivOfCardEq (by
    rw [← @Nat.card_eq_fintype_card Q iQ,
      ← @Nat.card_eq_fintype_card PLine2 iP]
    exact hQcard.trans projectiveLineTwo_card.symm)
  let phi : E →* Equiv.Perm PLine2 :=
    eQ.permCongrHom.toMonoidHom.comp psi
  have hphiinj : Function.Injective phi :=
    eQ.permCongrHom.injective.comp hpsiinj
  have hphibij : Function.Bijective phi := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hphiinj, ?_⟩
    rw [hEcard, Nat.card_perm, projectiveLineTwo_card]
    norm_num
  let eE : E ≃* Equiv.Perm PLine2 := MulEquiv.ofBijective phi hphibij
  exact ⟨eE.trans sl2EquivPermProjectiveLine.symm⟩

/-- In the same order-three-by-order-two configuration, the derived subgroup
of the join maps to the order-three factor. -/
public theorem map_commutator_sup_eq_left_of_card_two_full_commutator
    {G : Type u} [Group G] [Finite G]
    (F B : Subgroup G)
    (hBcard : Nat.card B = 2)
    (hBnorm : B ≤ Subgroup.normalizer (F : Set G))
    (hcomm : ⁅F, B⁆ = F) :
    (commutator (↥(F ⊔ B))).map (F ⊔ B).subtype = F := by
  let E : Subgroup G := F ⊔ B
  let FE : Subgroup E := F.subgroupOf E
  let BE : Subgroup E := B.subgroupOf E
  let _ : FE.Normal := by
    dsimp only [FE]
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact sup_le F.le_normalizer hBnorm
  have hsup : FE ⊔ BE = ⊤ := by
    calc
      FE ⊔ BE = (F ⊔ B).subgroupOf E :=
        (Subgroup.subgroupOf_sup le_sup_left le_sup_right).symm
      _ = E.subgroupOf E := rfl
      _ = ⊤ := Subgroup.subgroupOf_self E
  have hBEcard : Nat.card BE = 2 := by
    rw [show Nat.card BE = Nat.card B from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact hBcard
  let htwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 2) := htwo
  let _ : IsMulCommutative BE :=
    (isCyclic_of_prime_card (p := 2) hBEcard).isMulCommutative
  have hupperLocal : commutator E ≤ FE :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      inferInstance
  have hmapFE : FE.map E.subtype = F :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_left
  apply le_antisymm
  · calc
      (commutator E).map E.subtype ≤ FE.map E.subtype :=
        Subgroup.map_mono hupperLocal
      _ = F := hmapFE
  · calc
      F = ⁅F, B⁆ := hcomm.symm
      _ ≤ ⁅E, E⁆ := Subgroup.commutator_mono le_sup_left le_sup_right
      _ = (commutator E).map E.subtype :=
        (Subgroup.map_subtype_commutator E).symm

end Stellmacher.SectionOne
