module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.CentralElimination
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.FullCenter

/-!
# Transport the full linear MS sections to extension-core coordinates

A section with trivial denominator is the whole original subgroup.
Removing that denominator equivariantly turns C.1.34(1)–(2) into the actual
abelian-core coordinates and (3) into coordinates on the actual Z(Q).
Every construction retains the original quotient equivalence L/O₂(L).
The third case also retains both dual summands with that same actor.

These transports do not choose the V₂-plane inside a natural constituent.
That geometric marking is the remaining model-construction obligation.

Source: Aschbacher–Smith, C.1.34(1)–(3), printed pp.136–137, and
15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover CentralCover.LinearModels
universe u
variable {G : Type u} [Group G]

private theorem whole_model_of_section {A V F : Type*} [Group A] [AddCommGroup V]
    [Field F] [Module F V] {L D : Subgroup G} {a : L →* A}
    {ρ : Representation F A V} (h : HasSectionModel L D ⊥ a ρ) :
    ∃ e : D ≃* Multiplicative V, ∀ (l : L) (x y : D),
      (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
        e y = Multiplicative.ofAdd (ρ (a l) (e x).toAdd) := by
  obtain ⟨_, _, _, hn, e, he⟩ := h
  let := hn
  let q : D ≃* (D ⧸ (⊥ : Subgroup G).subgroupOf D) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf D).symm)
  refine ⟨q.trans e, ?_⟩
  intro l x y hy
  exact congrArg Multiplicative.ofAdd (he l x y hy)

theorem abelianCore_of_section {A V : Type*} [Group A] [AddCommGroup V]
    [Module (ZMod 2) V] {L : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* A) (ρ : Representation (ZMod 2) A V)
    (h : HasSectionModel L (extensionCore L) ⊥
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ρ) :
    ∃ m : AbelianCore L ρ, m.quotientIso = e := by
  obtain ⟨f, hf⟩ := whole_model_of_section h
  exact ⟨⟨e, f, hf⟩, rfl⟩

theorem fullCenter_of_section {A V : Type*} [Group A] [AddCommGroup V]
    [Module (ZMod 2) V] {L : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* A) (ρ : Representation (ZMod 2) A V)
    (h : HasSectionModel L (coreCenter L) ⊥
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) ρ) :
    ∃ m : FullCenter L ρ, m.quotientIso = e := by
  obtain ⟨f, hf⟩ := whole_model_of_section h
  exact ⟨⟨e, f, fun l z => hf l z (centerConjugate L l z) rfl⟩, rfl⟩

theorem centerIn_extensionCore_eq (L : Subgroup G) :
    CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (extensionCore L) = coreCenter L := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.property, mem_centralizer_iff.mpr ?_⟩
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hq ⟨x, hx⟩)
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, mem_center_iff.mpr (fun q =>
      Subtype.ext (mem_centralizer_iff.mp hc q q.property)), rfl⟩

/-- The same quotient actor survives all three linear cases, including the
full dual section in the third case. No submodule or central quotient is dropped. -/
theorem linearModels_of_survivors {L S : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hQ : extensionCore L = msQ L S) (h : MarkedMS.LinearThreeSurvivors L S e) :
    (∃ m : AbelianCore L LinearThree.natural, m.quotientIso = e) ∨
    ((∃ m : AbelianCore L (LinearThree.natural.prod LinearThree.natural),
      m.quotientIso = e) ∧ MSNotCentralizerCore L S S) ∨
    ((∃ m : FullCenter L LinearThree.natural, m.quotientIso = e) ∧
      HasSectionModel L (extensionCore L) (coreCenter L) (linearThreeActor e)
        (LinearThree.natural.dual.prod LinearThree.natural.dual) ∧
      MSNotCentralizerCore L S S) := by
  rcases h with h | h | h
  · apply Or.inl
    apply abelianCore_of_section e LinearThree.natural
    simpa only [← hQ, linearThreeActor] using h.2.2
  · apply Or.inr ∘ Or.inl
    refine ⟨?_, h.2⟩
    apply abelianCore_of_section e (LinearThree.natural.prod LinearThree.natural)
    simpa only [← hQ, linearThreeActor] using h.1
  · apply Or.inr ∘ Or.inr
    refine ⟨?_, ?_, h.2.2⟩
    · apply fullCenter_of_section e LinearThree.natural
      simpa only [← hQ, centerIn_extensionCore_eq, linearThreeActor] using h.1
    · simpa only [← hQ, centerIn_extensionCore_eq] using h.2.1

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

end
