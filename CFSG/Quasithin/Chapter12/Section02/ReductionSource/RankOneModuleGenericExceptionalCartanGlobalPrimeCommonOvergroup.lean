module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeCommonOvergroup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The common overgroup in the original changed-Sylow argument

The chosen-module input constructs the actual changed Sylow in G₀T₀B.
Its local group R T₁ has nontrivial two-core, escapes the original M, and
lies in the common overgroup ⟨N_G(T₀),H⟩. A unique containing C-component
there has a normal T-orbit containing both original and changed residuals.
The original residual cannot have quotient PSL₂(4).

The last theorem applies the explicit source 5.1.13 implication to G₀T₀B,
once the changed source hypotheses and equality of residuals are supplied.
Those comparisons, the smaller-Sylow exclusion and the final normalization
remain with qt-d-1222-rankone-cartan-local-to-global. This is a conditional
source application, not the full 5.2.2 theorem.

Source: Aschbacher--Smith 5.2.2, pp.648--649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- The literal changed Sylow and both residuals are placed in the same
normal component orbit of the source common overgroup. -/
theorem rankOne_prime_changedSylow_common_overgroup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      let H₀ := R ⊔ T₁
      let X := normalizer (normalizingSylow T R : Set G) ⊔ H
      normalizingSylow T R ≤ T₁ ∧
      (T₁ = normalizingSylow T R ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) ∧
      H₀ ∈ Chapter1.HOver G (T₁ : Set G) ∧
      extension T L H B D R ∈ Chapter1.HOver G (H₀ : Set G) ∧
      X ∈ Chapter1.HOver G (H₀ : Set G) ∧
      ¬ H₀ ≤ normalizer (L : Set G) ∧ T₁ ≤ normalizer (L : Set G) ∧
      ∃ I : Subgroup G, R ≤ I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
        normalizingSylow T R ≤ normalizer (I : Set G) ∧
        (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
        let Kplus := conjugateSpanBy I (T : Subgroup G)
        residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
          T₁ ≤ normalizer (Kplus : Set G) ∧
          residual H₀ = conjugateSpanBy R T₁ ∧ residual H₀ ≤ Kplus := by
  have hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨P,hTP,_,hcases⟩ := d.exists_changedSylow hH.1.1.2 c hd hz
  obtain ⟨hlocal,hE,hX,hout,hM⟩ := d.changedSylow_overgroups hi hH c hd hz P hTP
  obtain ⟨I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hN,hspan⟩ :=
    d.changedSylow_common_component hi hH c hd hz P hTP
  have he := d.changedSylow_residual_eq_conjugateSpan hi hH P
  exact ⟨P,hTP,hcases,hlocal,hE,hX,hout,hM,I,hRI,hIX,hI,hTI,hu,
    hKJ,hJX,hJn,hN,he,he.le.trans hspan⟩

/-- The actual proper right factor excludes the L₂(4) residual alternative. -/
theorem rankOne_prime_residual_not_linear_four
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ¬ ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H)) 2 4 :=
  d.residual_not_linear_four (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz

/-- The local 5.1.13 application uses the original prime actor and the
literal changed overgroup. The source comparison premises remain explicit. -/
theorem rankOne_prime_changedSylow_escape_impossible
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    {U : Sylow 2 G} (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (h513 : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    {W₁ B₁ : Subgroup G} (h₁ : Input KnownSimple.IsKnownSimple U L W₁ n)
    (hH₀ : R ⊔ (U : Subgroup G) ∈ Chapter3.HStar (U : Subgroup G) (normalizer (L : Set G)))
    (hk₀ : 1 < ChapterE.generationParameter (R ⊔ (U : Subgroup G) : Subgroup G))
    (c₀ : CartanPair U L (R ⊔ (U : Subgroup G)) A B₁)
    (hres : residual (R ⊔ (U : Subgroup G)) = residual H) : False :=
  d.changedSylow_escape_impossible (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hz P hTP hU h513 h₁ hH₀ hk₀ c₀ hres

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
