module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModulePreparation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleExceptional

/-!+# Preparing and splitting the original generic rank-one source application

The source input is constructed on the entire R₂(LT). For each actual outside
H, its embedded two-residual generates H together with T and escapes N_G(L).
The source Cartan normalizes that residual exactly when the full relative
normalizer N_L(T∩L) does; this keeps the split independent of Cartan choices.

The final theorem is a conditional assembly, not a proof of 5.2.3. Its three
remaining premises are 5.1.14 (the linear-three residual), 5.2.2 (Cartan
escape), and the normalized amalgam/completion argument. The first two belong
to `qt-d-1222-rankone-generic-exceptional`; the third belongs to
`qt-d-1222-rankone-generic-global`. The strict global exponent is retained:
5.2.6--7 give q>2 in the remaining amalgams, with the separate U₅(4) row.

Source: Aschbacher--Smith, 5.1.9, 5.1.14, 5.2.2--3 and §§5.2--5.3,
printed pp.634,638--661; the Chapter 12 application is on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
include D

/-- Every earlier source hypothesis is supplied by the original chosen setup,
including reducedness of the whole subgroup and the genuine outside guard. -/
theorem rankOne_generic_input_of_many
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n := by
  obtain ⟨hM, hTM, _⟩ := RankOneModule.normalizer_configuration D h
  exact ⟨h.simpleQTKE, RankOneModule.faithfulMaximalFamily_of_hypothesis h,
    hn, hpsl, hM, hTM, RankOneModule.wholeReduced_mem,
    D.rankOne_commutatorLayer_ne_bot, D.rankOne_hasMaximalOutside_of_many h hmany⟩

/-- The actual outside residual has the source supplement, escape and Sylow
normalization properties. The Borel Sylow is exactly T∩L. -/
theorem rankOne_generic_residual_configuration {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    residual H ⊔ (T : Subgroup G) = H ∧
    ¬ residual H ≤ normalizer (L : Set G) ∧
    (T : Subgroup G) ≤ normalizer (residual H : Set G) ∧
    ∃ S : Sylow 2 (localBorel T L),
      (S : Subgroup (localBorel T L)).map (localBorel T L).subtype =
        (T : Subgroup G) ⊓ L := by
  exact ⟨residual_sup_sylow T H hH.1.1.2,
    residual_not_le T H _ hH.1.1.2 D.sylow_normalizes_component hH.1.2,
    hH.1.1.2.trans (le_normalizer_residual H),
    exists_sylow_localBorel T L D.sylow_normalizes_component⟩

/-- The literal source Cartans give both intersection products and the exact
equivalence between the Cartan and relative-normalizer branch conditions.
Existence of the compatible Cartans remains with the source branch producers. -/
theorem rankOne_generic_cartan_configuration {H A B : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) :
    ((T : Subgroup G) ⊓ L) ⊔ A = localBorel T L ∧
    (T : Subgroup G) ⊔ B = normalizer (L : Set G) ⊓ H ∧
    (A ≤ normalizer (residual H : Set G) ↔
      (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
        normalizer (residual H : Set G)) ∧
    (A ≤ normalizer (residual H : Set G) →
      A ⊔ (T : Subgroup G) ⊔ B ≤ normalizer (residual H : Set G)) := by
  refine ⟨c.left_sup_intersection D.sylow_normalizes_component,
    c.sylow_sup_right D.sylow_normalizes_component hH.1.1.2, ?_,
    c.generated_normalizes_residual hH.1.1.2⟩
  simpa only [localBorel_eq_map] using
    c.normalizes_residual_iff D.sylow_normalizes_component hH.1.1.2

/-- Assemble precisely the source residual branches on the whole reduced
subgroup. All three earlier implications are explicit unfinished inputs;
neither the module model nor a global identification is assumed outright. -/
theorem rankOne_genericConfigurationExit_of_residual_branches_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hlinear : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        RankOneModule.ExceptionalExit T L H)
    (hescape : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
          normalizer (residual H : Set G) →
        RankOneModule.ExceptionalExit T L H)
    (hnormalized : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
          normalizer (residual H : Set G) →
        RankOneModule.GlobalExit G) :
    RankOneModule.GenericConfigurationExit T L := by
  classical
  have hs := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  intro _ H hH hgen
  by_cases hthree : ClassicalGroup.IsPSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4
  · exact Or.inl (hlinear hs H hH hgen hthree)
  by_cases hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G)
  · exact Or.inr (hnormalized hs H hH hgen hthree hN)
  · exact Or.inl (hescape hs H hH hgen hthree hN)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
