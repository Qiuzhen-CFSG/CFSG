module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Fourth
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The unresolved ambient action on the central four

For the full fourth alternative, C = C_[O₂(L),L](L) is normalized by
N_G(L). Its actual conjugation action by S has kernel C_S(C). The centrality
clause of C.1.34 proves that LR lies in C_G(C), so this action factors through
S/(S ∩ LR). The local Sylow constructed in `SourceCases.Sylow` has image
S ∩ LR; it need not have image S.

The four-group automorphism calculation bounds the image of this action by
two. Combining it with the already proved ambient center-rank obstruction
shows that a hypothetical fourth case must have image of order exactly two.
This is a reduction of the missing branch, not an exclusion of that branch:
no theorem below proves pointwise fixation or the case-(4) contradiction from
the genuine earlier source conclusions. In particular, characteristicity
only supplies normalization.

Source: Aschbacher–Smith, C.1.34(4), printed pp.136–137, and the rank comparison
in 15.3.23, printed p.1128. MS93's examples table, printed p.831, lists its
corresponding case (13) in F₄(2ⁿ) with an exceptional automorphism. That table
is not a counterexample to the full quasithin hypotheses, nor does it supply
the missing ambient action proof.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases.FixedFour
variable {G : Type*} [Group G]

/-- Component normalization preserves the actual central fixed subgroup. -/
theorem coreFixed_normalized (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (coreFixed L : Set G) :=
  (le_inf (normalizer_le_normalizer_commutatorCore L)
    (normalizer_le_normalizer_centralizer L)).trans inf_normalizer_le_normalizer_inf

/-- Conjugation by the ambient actor on the actual central fixed subgroup. -/
noncomputable def action (S L : Subgroup G) (hSL : S ≤ normalizer (L : Set G)) :
    S →* MulAut (coreFixed L) :=
  (coreFixed L).normalizerMonoidHom.comp (inclusion (hSL.trans (coreFixed_normalized L)))

/-- The kernel is the intrinsic copy of the ambient pointwise centralizer. -/
theorem action_ker (S L : Subgroup G) (hSL : S ≤ normalizer (L : Set G)) :
    (action S L hSL).ker = (centralizer (coreFixed L : Set G)).subgroupOf S := by
  ext s
  change (coreFixed L).normalizerMonoidHom
    ⟨(s : G), hSL.trans (coreFixed_normalized L) s.property⟩ = 1 ↔ _
  change (⟨(s : G), hSL.trans (coreFixed_normalized L) s.property⟩ :
    normalizer (coreFixed L : Set G)) ∈ (coreFixed L).normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

variable [Finite G] {L H : Subgroup G}

/-- The source centrality clause fixes C pointwise only for elements of H. -/
theorem local_centralizes (hLH : L ≤ H) (hcomp : (L.subgroupOf H).IsCComponent)
    {R : Subgroup H} {P : Sylow 2 H}
    {e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hf : FourthCase (L.subgroupOf H) R P e) :
    H ≤ centralizer (coreFixed L : Set G) := by
  intro h hh x hx
  rw [← sourceFixed_map hLH hcomp] at hx
  obtain ⟨x,hx,rfl⟩ := hx
  exact congrArg Subtype.val ((mem_center_iff.mp (hf.central hx) ⟨h,hh⟩).symm)

/-- The actual intersection S ∩ H lies in the kernel of the ambient action. -/
theorem localIntersection_le_ker (hLH : L ≤ H)
    (hcomp : (L.subgroupOf H).IsCComponent)
    {R : Subgroup H} {P : Sylow 2 H}
    {e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hf : FourthCase (L.subgroupOf H) R P e)
    (S : Subgroup G) (hSL : S ≤ normalizer (L : Set G)) :
    H.subgroupOf S ≤ (action S L hSL).ker := by
  rw [action_ker]
  exact fun _ hx => local_centralizes hLH hcomp hf hx

omit [Finite G] in
/-- S normalizes LR because it normalizes L and the defining two-core R. -/
theorem source_normalized (d : LocalData G) (L : Subgroup G)
    (hSL : d.S ≤ normalizer (L : Set G)) :
    d.S ≤ normalizer ((L ⊔ d.R : Subgroup G) : Set G) := by
  have hSR : d.S ≤ normalizer (d.R : Set G) :=
    le_sup_right.trans ((d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S)
        (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))))
  exact (le_inf hSL hSR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The remaining action descends to S/(S ∩ LR), with relative normality proved. -/
noncomputable def quotientAction (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I ∈ d.Hplus)
    (hSL : d.S ≤ normalizer (c.L : Set G))
    {P : Sylow 2 (c.L ⊔ d.R : Subgroup G)}
    {e : ((c.L.subgroupOf (c.L ⊔ d.R)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.R))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hf : FourthCase (c.L.subgroupOf (c.L ⊔ d.R)) (d.R.subgroupOf (c.L ⊔ d.R)) P e) :
    letI := normal_subgroupOf_of_le_normalizer (source_normalized d c.L hSL)
    (d.S ⧸ (c.L ⊔ d.R).subgroupOf d.S) →* MulAut (coreFixed c.L) := by
  letI := normal_subgroupOf_of_le_normalizer (source_normalized d c.L hSL)
  exact QuotientGroup.lift _ (action d.S c.L hSL)
    (localIntersection_le_ker le_sup_left (component_in_source d c hI) hf d.S hSL)

/-- The quotient action retains literal conjugation on representatives. -/
theorem quotientAction_mk (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I ∈ d.Hplus)
    (hSL : d.S ≤ normalizer (c.L : Set G))
    {P : Sylow 2 (c.L ⊔ d.R : Subgroup G)}
    {e : ((c.L.subgroupOf (c.L ⊔ d.R)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.R))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hf : FourthCase (c.L.subgroupOf (c.L ⊔ d.R)) (d.R.subgroupOf (c.L ⊔ d.R)) P e)
    (s : d.S) :
    letI := normal_subgroupOf_of_le_normalizer (source_normalized d c.L hSL)
    quotientAction d c hI hSL hf (QuotientGroup.mk s) = action d.S c.L hSL s := rfl

private theorem image_card {S C : Type*} [Group S] [Finite S] [Group C] [Finite C]
    [IsElementaryAbelian 2 C] (hc : Nat.card C = 4) (hs : IsPGroup 2 S)
    (f : S →* MulAut C) : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour C := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  have hd : Nat.card f.range ∣ 6 := (IsKleinFour.card_mulAut C) ▸ f.range.card_subgroup_dvd_card
  have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
  obtain ⟨n,hn⟩ := (hs.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra! h
    have ht : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
    omega
  interval_cases n
  · exact Or.inl hn
  · exact Or.inr hn
  · rw [hn] at hd
    norm_num at hd

/-- A two-group acting on the central four has image of order one or two. -/
theorem action_card (hLH : L ≤ H) (hcomp : (L.subgroupOf H).IsCComponent)
    {R : Subgroup H} {P : Sylow 2 H}
    {e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hf : FourthCase (L.subgroupOf H) R P e)
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSL : S ≤ normalizer (L : Set G)) :
    Nat.card (action S L hSL).range = 1 ∨ Nat.card (action S L hSL).range = 2 := by
  have helem : IsElementaryAbelian 2 (coreFixed L) := by
    rw [← sourceFixed_map hLH hcomp]
    exact hf.elementary.map H.subtype
  let := helem
  apply image_card _ hS
  rw [← sourceFixed_map hLH hcomp, card_map_of_injective H.subtype_injective]
  exact hf.order

omit [Finite G] in
/-- The order-one branch is exactly pointwise fixation by the ambient actor. -/
theorem action_card_one_iff (S L : Subgroup G) (hSL : S ≤ normalizer (L : Set G)) :
    Nat.card (action S L hSL).range = 1 ↔ S ≤ centralizer (coreFixed L : Set G) := by
  constructor
  · intro h s hs
    have hr := Subgroup.card_eq_one.mp h
    have hk : (⟨s,hs⟩ : S) ∈ (action S L hSL).ker := by
      have hm : action S L hSL ⟨s,hs⟩ ∈ (action S L hSL).range :=
        ⟨⟨s,hs⟩,rfl⟩
      change action S L hSL ⟨s,hs⟩ = 1
      rw [hr] at hm
      exact hm
    rw [action_ker] at hk
    exact hk
  · intro h
    apply Subgroup.card_eq_one.mpr
    apply eq_bot_iff.mpr
    rintro _ ⟨s,rfl⟩
    change s ∈ (action S L hSL).ker
    rw [action_ker]
    exact h s.property

/-- Under 15.3.8, a hypothetical fourth case must have nontrivial image of order two.
This does not exclude that remaining action or establish the source theorem. -/
theorem action_card_two_of_rank_bound (d : LocalData G)
    (hLH : L ≤ H) (hcomp : (L.subgroupOf H).IsCComponent)
    {R : Subgroup H} {P : Sylow 2 H}
    {e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hf : FourthCase (L.subgroupOf H) R P e)
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hSL : d.S ≤ normalizer (L : Set G)) :
    Nat.card (action d.S L hSL).range = 2 := by
  rcases action_card hLH hcomp hf d.S (d.T.isPGroup'.to_le inf_le_left) hSL with h | h
  · exact (fourthCase_impossible_of_ambient_action d hLH hcomp R P e hf
      hcore hR hindex hZ hZS hSL ((action_card_one_iff d.S L hSL).mp h)).elim
  · exact h

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases.FixedFour

end
