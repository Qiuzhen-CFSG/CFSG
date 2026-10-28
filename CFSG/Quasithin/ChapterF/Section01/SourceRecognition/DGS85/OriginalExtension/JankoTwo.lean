module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.J2Core
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Overlap
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension

/-!
# Original cores and outer index over a reduced Hall–Janko endpoint

A reduced first J₂ endpoint is perfect. The solvable quotient by its
unchanged original local factor therefore makes that factor the entire
reduced endpoint. The opposite local Borel already lies there, so its
original enlargement is precisely LᵢS. Reduction preserves the embedded
two-core, and the five-point action identifies the enlarged core quotient
with A₅ or S₅. Its order gives the common extension index one or two and
the original Sylow order 128 or 256.

The core equivalence retains the literal inclusion of the reduced core.
Only finite stabilizers are used. The reduced endpoint marking is explicit;
no original model, original size bound, or automorphism-extension action
is assumed. Identifying the outer endpoint itself with the Aut(J₂) model
still requires the generator relations of the source.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231;
Aschbacher–Smith F.1.12(I)(10)–(11), printed p.263.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open SuzukiContainment GreenBook
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (i : Fin 2)
  (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)

include h e in
theorem local_eq_reduced : L i = parabolic L (reducedSylow L S) i :=
  NoncommutingProfile.source_local_eq_parabolic_of_j2_first (reduced_hypothesis h) i e

include h e in
theorem original_first_eq_sup : parabolic L S i = L i ⊔ S := by
  have hb : borel (L (other i)) S ≤ L i := by
    rw [local_eq_reduced h i e, ← reduced_borel h (other i)]
    exact le_sup_right
  exact sup_eq_left.mpr (hb.trans le_sup_left)

@[expose] def localEquiv : L i ≃* Seed.l₁ :=
  ((MulEquiv.subgroupCongr (local_eq_reduced h i e)).trans e).trans
    (MulEquiv.subgroupCongr HallJanko.j2Model_P_zero)

@[expose] def localQuotientEquiv : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5) :=
  (LocalCoreTransport.quotientEquiv 2 (localEquiv h i e)).trans FirstParabolic.l₁_quotient.some

include h e in
theorem original_core_eq_local : twoCore (parabolic L S i) = twoCore (L i) := by
  rw [← reduced_parabolic_core h i, ← local_eq_reduced h i e]

include h e in
theorem local_core_card : Nat.card (pCore 2 (L i)) = 32 :=
  NoncommutingProfile.source_j2_core_card (reduced_hypothesis h) i e

include h e in
theorem original_core_card : Nat.card (pCore 2 (parabolic L S i)) = 32 := by
  calc
    _ = Nat.card (twoCore (parabolic L S i)) :=
      (card_map_of_injective (parabolic L S i).subtype_injective).symm
    _ = Nat.card (twoCore (L i)) := congrArg (fun A : Subgroup G => Nat.card A)
      (original_core_eq_local h i e)
    _ = Nat.card (pCore 2 (L i)) := card_map_of_injective (L i).subtype_injective
    _ = 32 := local_core_card h i e

include h e in
theorem original_first_quotient :
    Nonempty ((parabolic L S i ⧸ pCore 2 (parabolic L S i)) ≃* alternatingGroup (Fin 5)) ∨
    Nonempty ((parabolic L S i ⧸ pCore 2 (parabolic L S i)) ≃* Equiv.Perm (Fin 5)) := by
  rw [original_first_eq_sup h i e]
  exact Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    (L i) S (h.S_normalizes i) h.S_isP (localQuotientEquiv h i e)

include e in
theorem reduced_first_card : Nat.card (parabolic L (reducedSylow L S) i) = 1920 :=
  (Nat.card_congr (e.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_zero)).toEquiv).trans
    FirstParabolic.card_l₁

include h e in
theorem original_first_card_cases : Nat.card (parabolic L S i) = 1920 ∨
    Nat.card (parabolic L S i) = 3840 := by
  have hc := (pCore 2 (parabolic L S i)).card_mul_index
  rw [original_core_card h i e, index_eq_card] at hc
  rcases original_first_quotient h i e with hf | hf
  · obtain ⟨f⟩ := hf
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    exact Or.inl hc.symm
  · obtain ⟨f⟩ := hf
    rw [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc
    exact Or.inr hc.symm

include h e in
theorem original_borel_index_cases :
    (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) = 1 ∨
    (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) = 2 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G)
    (parabolic L (reducedSylow L S) i) (parabolic L S i) bot_le (reduced_parabolic_le h i)
  rw [relIndex_bot_left, relIndex_bot_left, reduced_first_card i e,
    parabolic_extension_index h i] at hc
  rcases original_first_card_cases h i e with ha | ha <;> rw [ha] at hc <;> omega

include h e in
theorem reduced_sylow_card : Nat.card (reducedSylow L S) = 128 := by
  let := (reduced_hypothesis h).finite_parabolic i
  obtain ⟨T,hT⟩ := (reduced_hypothesis h).sylow_parabolic i
  calc
    _ = Nat.card T := (congrArg (fun A : Subgroup G => Nat.card A) hT).symm.trans
      (card_map_of_injective (parabolic L (reducedSylow L S) i).subtype_injective)
    _ = 2 ^ (Nat.card (parabolic L (reducedSylow L S) i)).factorization 2 :=
      T.card_eq_multiplicity
    _ = 128 := by rw [reduced_first_card i e]; decide +kernel

include h e in
theorem original_sylow_card_cases : Nat.card S = 128 ∨ Nat.card S = 256 := by
  rw [original_sylow_card h, reduced_sylow_card h i e]
  rcases original_borel_index_cases h i e with he | he <;> rw [he] <;> omega

include h e in
theorem original_borel_index_two_of_ne (hne : S ≠ reducedSylow L S) :
    (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) = 2 := by
  rcases original_borel_index_cases h i e with hi | hi
  · exfalso
    apply hne
    apply le_antisymm _ (reducedSylow_le h)
    rw [← reduced_borel_inf_sylow h]
    exact le_inf (le_sup_right.trans (relIndex_eq_one.mp hi)) le_rfl
  · exact hi

include h e in
theorem original_sylow_card_of_ne (hne : S ≠ reducedSylow L S) : Nat.card S = 256 := by
  rw [original_sylow_card h, reduced_sylow_card h i e, original_borel_index_two_of_ne h i e hne]

include h e in
theorem original_first_quotient_of_ne (hne : S ≠ reducedSylow L S) :
    Nonempty ((parabolic L S i ⧸ pCore 2 (parabolic L S i)) ≃* Equiv.Perm (Fin 5)) := by
  rcases original_first_quotient h i e with he | he
  · exfalso
    obtain ⟨f⟩ := he
    have hc := (pCore 2 (parabolic L S i)).card_mul_index
    rw [original_core_card h i e, index_eq_card, Nat.card_congr f.toEquiv,
      nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
      (parabolic L (reducedSylow L S) i) (parabolic L S i) bot_le (reduced_parabolic_le h i)
    rw [relIndex_bot_left, relIndex_bot_left, reduced_first_card i e,
      parabolic_extension_index h i, original_borel_index_two_of_ne h i e hne] at hi
    omega
  · exact he

include h e in
theorem sylow_le_local_iff : S ≤ L i ↔ S = reducedSylow L S := by
  constructor
  · intro hs
    apply le_antisymm _ (reducedSylow_le h)
    rw [← reduced_parabolic_inf_sylow h i, ← local_eq_reduced h i e]
    exact le_inf hs le_rfl
  · intro he
    rw [he, local_eq_reduced h i e]
    exact le_sup_right.trans le_sup_left

include h in
private theorem original_core_map_eq :
    (pCore 2 (parabolic L S i)).map (parabolic L S i).subtype =
      (pCore 2 (parabolic L (reducedSylow L S) i)).map
        (parabolic L (reducedSylow L S) i).subtype :=
  (reduced_parabolic_core h i).symm

/-- The core restriction agrees with the actual reduced inclusion. -/
def originalCoreEquiv : pCore 2 (parabolic L S i) ≃* FirstParabolic.radical :=
  (((pCore 2 (parabolic L S i)).equivMapOfInjective _
    (parabolic L S i).subtype_injective).trans
    (MulEquiv.subgroupCongr (original_core_map_eq h i))).trans
      (((pCore 2 (parabolic L (reducedSylow L S) i)).equivMapOfInjective _
        (parabolic L (reducedSylow L S) i).subtype_injective).symm.trans
          (NoncommutingProfile.j2FirstCoreEquiv e))

include h e in
theorem originalCoreEquiv_reduced (x : pCore 2 (parabolic L (reducedSylow L S) i)) :
    originalCoreEquiv h i e
      ⟨inclusion (reduced_parabolic_le h i) x.val, by
        rw [← mem_map_iff_mem (f := (parabolic L S i).subtype)
          (parabolic L S i).subtype_injective]
        change (x.val : G) ∈ twoCore (parabolic L S i)
        rw [← reduced_parabolic_core h i]
        exact mem_map_of_mem _ x.property⟩ = NoncommutingProfile.j2FirstCoreEquiv e x := by
  simp only [originalCoreEquiv, MulEquiv.trans_apply]
  apply congrArg (NoncommutingProfile.j2FirstCoreEquiv e)
  apply ((pCore 2 (parabolic L (reducedSylow L S) i)).equivMapOfInjective _
    (parabolic L (reducedSylow L S) i).subtype_injective).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

include h e in
/-- The size-128 case is exactly the case with no original enlargement. -/
theorem sylow_eq_reduced_iff_card : S = reducedSylow L S ↔ Nat.card S = 128 := by
  constructor
  · intro he
    rw [he, reduced_sylow_card h i e]
  · intro hc
    by_contra hn
    have hh := original_sylow_card_of_ne h i e hn
    omega

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
