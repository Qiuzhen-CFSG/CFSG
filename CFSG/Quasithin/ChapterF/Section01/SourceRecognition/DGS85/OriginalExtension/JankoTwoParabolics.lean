module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwo
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Catalogue
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Original Hall–Janko profiles and inner parabolic restoration

A reduced S₅ core quotient would make its full Borel a Sylow two-group,
so the order-768 Aut(J₂) Borel cannot occur in the reduced pair. For the
J₂ row, the common extension index preserves the actual order-32 and
order-64 cores and gives original Borel orders 384 or 768. The original
Sylow order 128 forces equality with the reduced pair, restoring the
three given parabolic maps with their exact reduced restrictions.

Both orientations are retained. A proper enlargement has Sylow order
256 and Borel order 768; these orders do not identify its parabolics
with Aut(J₂). That remaining step is the outer-generator argument of
the source. No compatibility is imposed on a raw parabolic comparison.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231;
Aschbacher–Smith F.1.11–12, printed pp.262–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open SuzukiContainment GreenBook GreenBook.ExceptionalModels
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
private theorem s5_sylow_self_normalizing {H : Type*} [Group H] [Finite H]
    (f : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) (T : Sylow 2 H) :
    normalizer (T : Set H) = (T : Subgroup H) := by
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective, QuotientGroup.ker_mk']
  have hkT : q.ker ≤ (T : Subgroup H) := hk ▸ pCore_isPGroup.le_sylow_of_normal T
  apply map_injective_of_ker_le q (hkT.trans (T : Subgroup H).le_normalizer) hkT
  change (normalizer (T : Set H)).map q = (T : Subgroup H).map q
  rw [T.normalizer_map_surjective q hq]
  exact Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self
    (T.mapSurjective hq)

include h

/-- A reduced symmetric-five endpoint forces a two-group Borel. -/
theorem reduced_borel_eq_sylow_of_symmetric_quotient (i : Fin 2)
    (f : (parabolic L (reducedSylow L S) i ⧸ pCore 2 (parabolic L (reducedSylow L S) i)) ≃*
      Equiv.Perm (Fin 5)) :
    commonBorel L (reducedSylow L S) = reducedSylow L S := by
  let P := parabolic L (reducedSylow L S) i
  let R := reducedSylow L S
  let := (reduced_hypothesis h).finite_parabolic i
  obtain ⟨T,hT⟩ := (reduced_hypothesis h).sylow_parabolic i
  have ht : (T : Subgroup P) = R.subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (show R ≤ P from le_sup_right.trans le_sup_left)]
    exact hT
  have he := s5_sylow_self_normalizing f T
  change normalizer ((T : Subgroup P) : Set P) = (T : Subgroup P) at he
  rw [ht, ← subgroupOf_normalizer_eq (show R ≤ P from le_sup_right.trans le_sup_left)] at he
  apply le_antisymm _ le_sup_right
  intro b hb
  exact he.le (show (⟨b, commonBorel_le_parabolic i hb⟩ : P) ∈
    (normalizer (R : Set G)).subgroupOf P from
      ((reduced_commonBorel_le h).trans
        ((commonBorel L S).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))) hb)

/-- Full Aut(J₂) is not a reduced row: its Borel has order 768 while the
symmetric-five endpoint forces that Borel to be its order-256 Sylow. -/
theorem not_reduced_autJ2_endpoint (i : Fin 2)
    (f : parabolic L (reducedSylow L S) i ≃* HallJanko.autJ2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.autJ2Model.toMarking.B) : False := by
  let g := f.trans ((LocalCoreTransport.subgroupEquiv
    Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut
    (HallJanko.autJ2Model_P 0).symm).symm.trans
      (MulEquiv.subgroupCongr HallJanko.extensionModel_P_zero))
  have hq := (LocalCoreTransport.quotientEquiv 2 g).trans FirstParabolic.l₁s_quotient.some
  have hb := reduced_borel_eq_sylow_of_symmetric_quotient h i hq
  have hB := (Nat.card_congr b.toEquiv).trans HallJanko.card_autJ2Model_B
  have hP := (Nat.card_congr g.toEquiv).trans FirstParabolic.card_l₁s
  let := (reduced_hypothesis h).finite_parabolic i
  obtain ⟨T,hT⟩ := (reduced_hypothesis h).sylow_parabolic i
  have hS : Nat.card (reducedSylow L S) = Nat.card T :=
    (congrArg (fun A : Subgroup G => Nat.card A) hT).symm.trans
      (card_map_of_injective (parabolic L (reducedSylow L S) i).subtype_injective)
  rw [hb,hS,T.card_eq_multiplicity,hP] at hB
  have : 2 ^ (3840 : ℕ).factorization 2 = 256 := by decide +kernel
  omega

/-- The source reduction cannot contain the full outer Hall–Janko row in
either orientation. This excludes raw parabolic data, without assuming
compatibility of the overlap maps. -/
theorem not_reduced_autJ2_parabolicModels :
    ¬ (ParabolicModel .autJ2 (reducedAmalgam L S) ∨
      ParabolicModel .autJ2 (reducedAmalgam L S).reverse) := by
  rintro (he | he)
  · obtain ⟨e⟩ := he
    exact not_reduced_autJ2_endpoint h 0 e.left e.middle
  · obtain ⟨e⟩ := he
    exact not_reduced_autJ2_endpoint h 1 e.left e.middle

/-- The second original parabolic keeps the actual order-64 reduced core. -/
theorem original_second_core_card (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 1) :
    Nat.card (pCore 2 (parabolic L S i)) = 64 := by
  have he := LocalCoreTransport.core_card 2
    (e.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one))
  rw [(PairNormalizer.p₂_core_and_quotient SecondParabolic.l₂_core_card).1] at he
  calc
    _ = Nat.card (twoCore (parabolic L S i)) :=
      (card_map_of_injective (parabolic L S i).subtype_injective).symm
    _ = Nat.card (twoCore (parabolic L (reducedSylow L S) i)) :=
      congrArg (fun A : Subgroup G => Nat.card A) (reduced_parabolic_core h i).symm
    _ = Nat.card (pCore 2 (parabolic L (reducedSylow L S) i)) :=
      card_map_of_injective (parabolic L (reducedSylow L S) i).subtype_injective
    _ = 64 := he

/-- The full original Borel, including its odd part, has order 384 or 768. -/
theorem original_borel_card_cases (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B) :
    Nat.card (commonBorel L S) = 384 ∨ Nat.card (commonBorel L S) = 768 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    (commonBorel L (reducedSylow L S)) (commonBorel L S) bot_le (reduced_commonBorel_le h)
  rw [relIndex_bot_left,relIndex_bot_left,
    (Nat.card_congr b.toEquiv).trans HallJanko.card_j2Model_B] at hc
  rcases original_borel_index_cases h i e with hi | hi <;> rw [hi] at hc <;> omega

/-- A proper original enlargement has the full Borel order of Aut(J₂). -/
theorem original_borel_card_of_ne (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (hne : S ≠ reducedSylow L S) : Nat.card (commonBorel L S) = 768 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    (commonBorel L (reducedSylow L S)) (commonBorel L S) bot_le (reduced_commonBorel_le h)
  rw [relIndex_bot_left,relIndex_bot_left,
    (Nat.card_congr b.toEquiv).trans HallJanko.card_j2Model_B,
    original_borel_index_two_of_ne h i e hne] at hc
  exact hc.symm

/-- Both source orientations yield the original Sylow orders and full Borel
orders, and identify the same original cores as 32 and 64. -/
theorem original_profile_of_parabolicModels
    (he : ParabolicModel .j2 (reducedAmalgam L S) ∨
      ParabolicModel .j2 (reducedAmalgam L S).reverse) :
    (Nat.card S = 128 ∨ Nat.card S = 256) ∧
    (Nat.card (commonBorel L S) = 384 ∨ Nat.card (commonBorel L S) = 768) ∧
    ((Nat.card (pCore 2 (parabolic L S 0)) = 32 ∧
        Nat.card (pCore 2 (parabolic L S 1)) = 64) ∨
      (Nat.card (pCore 2 (parabolic L S 1)) = 32 ∧
        Nat.card (pCore 2 (parabolic L S 0)) = 64)) := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact ⟨original_sylow_card_cases h 0 e.left, original_borel_card_cases h 0 e.left e.middle,
      Or.inl ⟨original_core_card h 0 e.left,original_second_core_card h 1 e.right⟩⟩
  · obtain ⟨e⟩ := he
    exact ⟨original_sylow_card_cases h 1 e.left, original_borel_card_cases h 1 e.left e.middle,
      Or.inr ⟨original_core_card h 1 e.left,original_second_core_card h 0 e.right⟩⟩

/-- The size-128 branch restores the three given parabolic maps. No overlap
compatibility is added to the raw J₂ source conclusion. -/
@[expose] def originalParabolicEquiv
    (e : ParabolicEquiv (reducedAmalgam L S) HallJanko.j2Model.toMarking.amalgam)
    (hs : Nat.card S = 128) :
    ParabolicEquiv (originalAmalgam L S) HallJanko.j2Model.toMarking.amalgam :=
  (NativeRestoration.originalIsoReduced
    ((sylow_eq_reduced_iff_card h 0 e.left).mpr hs)).toParabolicEquiv.trans e

omit h in
private theorem parabolic_restrictions {Y : Type*} [Group Y]
    {A B C A' B' C' : Subgroup Y}
    (hA : B ≤ A) (hC : B ≤ C) (hA' : B' ≤ A') (hC' : B' ≤ C')
    (eA : A = A') (eB : B = B') (eC : C = C')
    {X D Z : Type*} [Group X] [Group D] [Group Z]
    {γ : RankTwoAmalgam X D Z}
    (f : ParabolicEquiv (ofSubgroups A' B' C' hA' hC') γ)
    (jA : A' ≤ A) (jB : B' ≤ B) (jC : C' ≤ C) :
    (∀ x : A', ((NativeRestoration.subgroupCongrIso hA hC hA' hC' eA eB eC).toParabolicEquiv.trans f).left (inclusion jA x) = f.left x) ∧
    (∀ x : B', ((NativeRestoration.subgroupCongrIso hA hC hA' hC' eA eB eC).toParabolicEquiv.trans f).middle (inclusion jB x) = f.middle x) ∧
    (∀ x : C', ((NativeRestoration.subgroupCongrIso hA hC hA' hC' eA eB eC).toParabolicEquiv.trans f).right (inclusion jC x) = f.right x) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The restored parabolic maps agree on every literal reduced inclusion. -/
theorem originalParabolicEquiv_restrictions
    (e : ParabolicEquiv (reducedAmalgam L S) HallJanko.j2Model.toMarking.amalgam)
    (hs : Nat.card S = 128) :
    (∀ x : parabolic L (reducedSylow L S) 0,
      (originalParabolicEquiv h e hs).left (inclusion (reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ x : commonBorel L (reducedSylow L S),
      (originalParabolicEquiv h e hs).middle (inclusion (reduced_commonBorel_le h) x) = e.middle x) ∧
    (∀ x : parabolic L (reducedSylow L S) 1,
      (originalParabolicEquiv h e hs).right (inclusion (reduced_parabolic_le h 1) x) = e.right x) :=
  parabolic_restrictions _ _ _ _ _ _ _ e
    (reduced_parabolic_le h 0) (reduced_commonBorel_le h) (reduced_parabolic_le h 1)

/-- The inner branch is fully restored in either orientation. The remaining
outer branch has proved original sizes; its endpoint recognition is not
inferred from those sizes. -/
theorem original_parabolicModels_or_outer_sizes
    (he : ParabolicModel .j2 (reducedAmalgam L S) ∨
      ParabolicModel .j2 (reducedAmalgam L S).reverse) :
    (ParabolicModel .j2 (originalAmalgam L S) ∨
      ParabolicModel .j2 (originalAmalgam L S).reverse) ∨
    (Nat.card S = 256 ∧ Nat.card (commonBorel L S) = 768) := by
  by_cases hs : S = reducedSylow L S
  · left
    let f := NativeRestoration.originalIsoReduced hs
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨f.toParabolicEquiv.trans e⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨f.reverse.toParabolicEquiv.trans e⟩
  · right
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact ⟨original_sylow_card_of_ne h 0 e.left hs,
        original_borel_card_of_ne h 0 e.left e.middle hs⟩
    · obtain ⟨e⟩ := he
      exact ⟨original_sylow_card_of_ne h 1 e.left hs,
        original_borel_card_of_ne h 1 e.left e.middle hs⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
