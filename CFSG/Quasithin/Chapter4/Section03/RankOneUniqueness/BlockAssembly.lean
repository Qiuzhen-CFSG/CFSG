module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesG2
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatives
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Exclusion
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThree
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalUniqueness

/-!
# Block-exclusion assembly in the original rank-one source argument

The actual B.5 star action supplies all module markings. The linear, finite,
alternating, nonbinary symplectic and large-G₂ exclusions now discharge every
row under the original source hypotheses. `SourceConfiguration.false_of_block`
proves original 4.3.7 with the same K, L and full moved module W.

The final uniqueness and literal Chapter 12 preparation adapters discharge
hblock internally. Configuration selection, the ordinary and nonblock
exclusions, and the independent right factor retain their existing producers;
the global uniqueness owner assembles those inputs. Earlier conditional
interfaces are preserved for callers, including the concrete C.4.1 alternatives.

Source: Aschbacher–Smith, original4.3.7, printed pp.615–616.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02 ChapterC ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All three concrete source branches are excluded, retaining the actual block models. -/
theorem source_block_false_of_concrete_alternatives
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hc : IsSL3EvenBlock c.K n ∨
      (n = 2 ∧ (IsAlternatingBlock c.K 7 ∨ IsSp4FourBlock c.K))) : False := by
  rcases hc with hl | ⟨hn2,ha | hs⟩
  · exact c.false_of_linearThree_block D hn hf hb hl
  · exact c.false_of_alternating_block_four D h (by simpa [hn2] using hpsl) hf ha
  · exact c.false_of_sp4Four_block D hf hb hs

/-- Consumer of the finite-row exclusions. Only the four displayed C.4.1
row implications remain; the final block-exclusion owner must prove them. -/
theorem source_block_false_of_four_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False)
    (halt : ∀ m : ℕ, (m = 7 ∨ m = 8) →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        alternatingGroup (Fin m)) → n = 2 ∧ IsAlternatingBlock c.K 7)
    (hfive :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) → False) : False := by
  exact source_block_false_of_concrete_alternatives D h.toHypothesis1221 hn hpsl c hf hb
    (source_block_alternatives_of_four_star_rows D h hmany hn hpsl c hf hb
      hsymplectic hg2 halt hfive)


/-- The actual binary-linear exclusions leave only Sp₄, large G₂ and A₇.
All three remaining implications belong to this task's final C.4.1 assembly. -/
theorem source_block_false_of_three_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False)
    (hseven :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        alternatingGroup (Fin 7)) → n = 2 ∧ IsAlternatingBlock c.K 7) :
    False := by
  exact source_block_false_of_concrete_alternatives D h.toHypothesis1221 hn hpsl c hf hb
    (source_block_alternatives_of_three_star_rows D h hmany hn hpsl c hf hb
      hsymplectic hg2 hseven)

/-- The actual binary-linear exclusions leave only Sp₄ and large G₂.
Both remaining implications belong to this task's final C.4.1 assembly. -/
theorem source_block_false_of_two_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False) : False := by
  exact source_block_false_of_three_star_rows D h hmany hn hpsl c hf hb
    hsymplectic hg2 (c.alternatingSeven_block_of_star_group hn hpsl hf hb)


/-- Original 4.3.7 with the actual K, L and full moved module. All source
representation rows and their local markings are discharged internally. -/
theorem SourceConfiguration.false_of_block
    (c : SourceConfiguration T L)
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K) : False := by
  exact source_block_false_of_largeG2_natural_row D h hn hpsl c hf hb (by
    intro F hF hm
    exact c.false_of_g2_model (inferInstance : Finite G) D hf hb hF hm)

/-- The proved block exclusion removes hblock from the source uniqueness
assembly. Configuration selection, 4.3.6 and 4.3.8–16 remain with their existing
producers and are discharged by the global uniqueness assembly owner. -/
theorem uniqueness_of_remaining_source_exclusions
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_source_exclusions hselect hordinary
    (fun c hf hb => c.false_of_block D h hmany hn hpsl hf hb) hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal preparation consumer: the proved branch exclusions discharge hblock
once the concrete C.4.1 alternatives are supplied. Selection, the ordinary and
nonblock branches, and the independent right factor retain their original owners. -/
theorem rankOne_global_preparation_of_concrete_block_alternatives
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hcases : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ChapterC.IsBlock c.K →
        ChapterC.IsSL3EvenBlock c.K n ∨
          (n = 2 ∧ (ChapterC.IsAlternatingBlock c.K 7 ∨ ChapterC.IsSp4FourBlock c.K)))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_source_exclusions h hmany hn hpsl hH hgen hN
    hselect hordinary
    (fun c hf hb => source_block_false_of_concrete_alternatives D h hn hpsl c hf hb
      (hcases c hf hb)) hnonblock hright

/-- The literal Chapter 12 preparation now needs only the large-G₂ block
exclusion. The symplectic action row and all finite and linear rows are
proved internally. The remaining G₂ premise is owned by the block assembly. -/
theorem rankOne_global_preparation_of_largeG2_block_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hg2 : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ChapterC.IsBlock c.K →
      ∀ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree →
        ChapterC.IsLinearBlockModel c.K (ChapterB.QuasisimpleSource.binaryG2 F) → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_source_exclusions h.toHypothesis1221 hmany hn hpsl hH hgen hN
    hselect hordinary
    (fun c hf hb => source_block_false_of_largeG2_natural_row D h hn hpsl c hf hb
      (hg2 c hf hb)) hnonblock hright


/-- Literal Chapter 12 application of original 4.3.7. It has no block-row,
module-marking or block-exclusion premise. The independent source selection,
ordinary and nonblock exclusions and right factor retain their original
owners; qt-d-1222-rankone-global-uniqueness assembles those inputs. -/
theorem rankOne_global_preparation_of_remaining_source_exclusions
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_source_exclusions h.toHypothesis1221 hmany hn hpsl hH hgen hN
    hselect hordinary (fun c hf hb => c.false_of_block D h hmany hn hpsl hf hb) hnonblock hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
