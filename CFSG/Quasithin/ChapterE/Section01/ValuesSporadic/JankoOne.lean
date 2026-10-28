module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoOne.SimpleMembers
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoOne.Extension
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoOne.CentralizerMember
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.SpecificGroups.Janko1.Model.NormalizerCentralizerGeneration

/-!
# The J₁ rank-two E-generation bound

The source allows all finite SQTK groups with simple L = F*(G), G = LT,
and an actual equivalence L ≃ J₁. The extension reduction proves L = G.
For the concrete model, a proper elementary subgroup of its Sylow eight
has rank at most two, so a nontrivial such subgroup makes the whole group
an E-member. A family with no such member either has trivial weak closure
or contains the whole Sylow subgroup. In the latter case a single local
rank-two E-member K with ⟨K,N(T)⟩ = G suffices.

The concrete calculations prove that the standard involution centralizer C(a)
is an E-member for A = T and that C(a) together with N(T) generates J₁.
The actual identification C(a) ≃ C₂ × A₅ gives rank two in its radical
quotient; checked words in the matrix generators give the generation equality.
The final assembly discharges both premises of the retained conditional
theorems and proves the source bound n(G) ≤ 2 for every permitted extension.

Source: Aschbacher--Smith, E.1.14(5), printed p.214, citing Aschbacher,
GF(2)-representations of finite groups (1982), Lemma 4.9; E.1.2 uses the
corrected local tau on printed pp.209--210. GLS3, Table 5.3f records the
involution centralizer and Sylow normalizer of J₁.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoOne
open Subgroup Theory.GroupTheory ValuesEvenClassical.RankOneUpper

/-- Proper elementary subgroups of a J₁ Sylow two-subgroup have rank at most two. -/
theorem proper_rank_le_two (T : Sylow 2 Janko1.Model)
    (A : Subgroup Janko1.Model) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup Janko1.Model)) (hne : A ≠ (T : Subgroup Janko1.Model)) :
    Group.rank A ≤ 2 := by
  let := hA
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2) A
  have hd : Nat.card A ∣ 8 := by simpa [Janko1.SylowTwo.card] using card_dvd_of_le hAT
  have he : Nat.card A ≠ 8 := by
    intro he
    apply hne
    exact eq_of_le_of_card_ge hAT (by rw [he, Janko1.SylowTwo.card])
  have hp := Nat.card_pos (α := A)
  have hbound := Nat.le_of_dvd (by decide : 0 < 8) hd
  interval_cases h : Nat.card A <;> norm_num [h] at *

/-- A local rank-two member for the full Sylow subgroup supplies the sole
case not settled by proper elementary subgroups. -/
theorem generated_at_of_local_member (T : Sylow 2 Janko1.Model)
    (K : Subgroup Janko1.Model)
    (hK : IsEMemberAt 2 (T : Subgroup Janko1.Model) (T : Subgroup Janko1.Model) K)
    (hgen : K ⊔ normalizer (T : Set Janko1.Model) = ⊤) : IsEGeneratedAt 2 T := by
  classical
  intro Ω hΩ
  by_cases hsmall : ∃ A : Subgroup Janko1.Model, A ∈ Ω ∧ A ≤ (T : Subgroup Janko1.Model) ∧
      A ≠ ⊥ ∧ A ≠ (T : Subgroup Janko1.Model)
  · obtain ⟨A, hA, hAT, hn, hproper⟩ := hsmall
    have hm := isEMemberAt_top_of_component_and_rank T A (hΩ.1 A hA) hAT
      (top_component (T : Subgroup Janko1.Model) A hn)
      (proper_rank_le_two T A (hΩ.1 A hA) hAT hproper)
    apply top_unique
    exact (show (⊤ : Subgroup Janko1.Model) ≤ eSubgroup 2 (T : Subgroup Janko1.Model) A from
      le_sSup hm).trans ((le_iSup (fun B : {B : Subgroup Janko1.Model //
        B ∈ Ω ∧ B ≤ (T : Subgroup Janko1.Model)} => eSubgroup 2 (T : Subgroup Janko1.Model) B.1)
        ⟨A, hA, hAT⟩).trans le_sup_left)
  · by_cases hT : (T : Subgroup Janko1.Model) ∈ Ω
    · apply top_unique
      rw [← hgen]
      apply sup_le
      · exact (show K ≤ eSubgroup 2 (T : Subgroup Janko1.Model) (T : Subgroup Janko1.Model) from
          le_sSup hK).trans ((le_iSup (fun B : {B : Subgroup Janko1.Model //
            B ∈ Ω ∧ B ≤ (T : Subgroup Janko1.Model)} => eSubgroup 2 (T : Subgroup Janko1.Model) B.1)
            ⟨T, hT, le_rfl⟩).trans le_sup_left)
      · exact (normalizer_le_weakClosure_normalizer (T : Subgroup Janko1.Model) hΩ).trans le_sup_right
    · have hw : weakClosure (T : Subgroup Janko1.Model) Ω = ⊥ := by
        apply weakClosure_eq_bot_of_members_eq_bot
        intro A hA hAT
        by_contra hn
        have hne : A ≠ (T : Subgroup Janko1.Model) := fun he => hT (he ▸ hA)
        exact hsmall ⟨A, hA, hAT, hn, hne⟩
      rw [hw, normalizer_eq_top, sup_top_eq]

/-- Conditional assembly for all source-allowed extensions: only the
concrete local member and its generation with the Sylow normalizer remain. -/
theorem generated_of_local_member {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hL : L = generalizedFitting G) (e : L ≃* Janko1.Model)
    (T : Sylow 2 Janko1.Model) (K : Subgroup Janko1.Model)
    (hK : IsEMemberAt 2 (T : Subgroup Janko1.Model) (T : Subgroup Janko1.Model) K)
    (hgen : K ⊔ normalizer (T : Set Janko1.Model) = ⊤) : IsEGenerated 2 G := by
  let f : G ≃* Janko1.Model := (topEquiv.symm.trans
    (MulEquiv.subgroupCongr (socle_eq_top L hL e).symm)).trans e
  exact (generated_at_of_local_member T K hK hgen).isEGenerated.map_equiv f.symm

/-- The two independent concrete centralizer calculations feed the full
ambient statement, with a Sylow subgroup containing the standard involution
constructed here. Neither calculation is assumed as a source theorem. -/
theorem generated_of_centralizer_calculations {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hL : L = generalizedFitting G) (e : L ≃* Janko1.Model)
    (hmember : ∀ T : Sylow 2 Janko1.Model, Janko1.a ∈ (T : Subgroup Janko1.Model) →
      IsEMemberAt 2 (T : Subgroup Janko1.Model) (T : Subgroup Janko1.Model)
        (centralizer ({Janko1.a} : Set Janko1.Model)))
    (hgenerate : ∀ T : Sylow 2 Janko1.Model, Janko1.a ∈ (T : Subgroup Janko1.Model) →
      centralizer ({Janko1.a} : Set Janko1.Model) ⊔
        normalizer (T : Set Janko1.Model) = ⊤) : IsEGenerated 2 G := by
  have hp : IsPGroup 2 (zpowers Janko1.a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Janko1.orderOf_a]
    rfl)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have ha : Janko1.a ∈ (T : Subgroup Janko1.Model) := hT (mem_zpowers Janko1.a)
  exact generated_of_local_member L hL e T _ (hmember T ha) (hgenerate T ha)

/-- A finite group with generalized Fitting subgroup isomorphic to the actual
J₁ model is rank-two E-generated. Both concrete local calculations are discharged. -/
theorem isEGenerated_of_generalizedFitting {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hL : L = generalizedFitting G) (e : L ≃* Janko1.Model) :
    IsEGenerated 2 G :=
  generated_of_centralizer_calculations L hL e
    CentralizerMember.isEMemberAt_centralizer Janko1.centralizer_sup_normalizer_eq_top

/-- The J₁ upper-generation clause of E.1.14(5), retaining all source inputs.
The generalized Fitting subgroup equivalence already implies the stronger theorem above. -/
theorem isEGenerated_of_source {G : Type*} [Group G] [Finite G]
    {K : GroupClass} (_hSQTK : IsSQTK K G)
    (L : Subgroup G) (hL : L = generalizedFitting G) [IsSimpleGroup L]
    (T : Sylow 2 G) (_hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Janko1.Model) : IsEGenerated 2 G :=
  isEGenerated_of_generalizedFitting L hL e

/-- The numerical J₁ conclusion of E.1.14(5), obtained from actual E-generation. -/
theorem generationParameter_le_two_of_source {G : Type*} [Group G] [Finite G]
    {K : GroupClass} (hSQTK : IsSQTK K G)
    (L : Subgroup G) (hL : L = generalizedFitting G) [IsSimpleGroup L]
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Janko1.Model) : generationParameter G ≤ 2 :=
  generationParameter_le (by decide) (isEGenerated_of_source hSQTK L hL T hgen e)

end CFSG.Quasithin.ChapterE.JankoOne
