module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Excluding the two central linear-three MS cases

For the application (LS,S), MS3 forbids the nontrivial characteristic subgroup
Ω₁(Z(S)) from being normal in LS. A central elementary four-group lies in
this omega center, and the order bound from 15.3.8 forces equality. This
excludes C.1.34(4) directly from its central subgroup, retaining the complete
layered alternative in the input. Case (5) explicitly asserts the forbidden
centrality and is excluded as well.

The surviving disjunction preserves the actual natural representations,
the duals of the same chosen natural module, and the centralizer-core
exclusions. It is conditional on the complete C.1.34 classification output;
this module does not establish that classification or the marked V₂-line.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G]

private theorem subgroupOf_centerIn_le {I C : Subgroup G}
    (hc : C ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn I) : C.subgroupOf I ≤ center I := by
  intro x hx
  obtain ⟨y, hy, he⟩ := hc hx
  exact (Subtype.ext he : y = x) ▸ hy

private theorem normal_of_central {H : Type*} [Group H] {C : Subgroup H}
    (hc : C ≤ center H) : C.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have h := (Subgroup.mem_center_iff.mp (hc hx) g)
  simpa only [h, mul_inv_cancel_right] using hx

/-- MS3 forbids centrality of the nontrivial first omega center of S. -/
theorem omegaCenter_not_central {L S : Subgroup G}
    (hms : MSNoCharacteristicNormal L S)
    (hne : 1 < Nat.card (omegaCenterIn S)) :
    ¬ omegaCenterIn S ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ S) := by
  intro hc
  let O : Subgroup S := (omega₁ (center S) (p := 2)).map (center S).subtype
  let : (omega₁ (center S) (p := 2)).Characteristic := omega₁_characteristic _
  have hn : ((O.map S.subtype).subgroupOf (L ⊔ S)).Normal :=
    normal_of_central (subgroupOf_centerIn_le hc)
  have he := hms O inferInstance hn
  have hz : omegaCenterIn S = ⊥ := by
    change O.map S.subtype = ⊥
    rw [he, Subgroup.map_bot]
  simp [hz] at hne

/-- A central elementary subgroup of a Sylow overgroup lies in its omega center. -/
theorem central_elementary_le_omegaCenter {L S C : Subgroup G}
    (hS : CFSG.Quasithin.Chapter1.IsSylowIn 2 S (L ⊔ S))
    [IsElementaryAbelian 2 C] (hc : C ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ S)) :
    C ≤ omegaCenterIn S := by
  let I := L ⊔ S
  have hCI : C ≤ I := hc.trans (map_subtype_le _)
  have hcentral : C.subgroupOf I ≤ center I := subgroupOf_centerIn_le hc
  let : (C.subgroupOf I).Normal := normal_of_central hcentral
  have hp : IsPGroup 2 (C.subgroupOf I) :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := C)).of_equiv
      (subgroupOfEquivOfLe hCI).symm
  obtain ⟨P, hP⟩ := hS
  have hCS : C ≤ S := by
    have hle := map_mono (f := I.subtype) (hp.le_sylow_of_normal P)
    rwa [map_subgroupOf_eq_of_le hCI, hP] at hle
  intro c hcC
  have hcz : (⟨c, hCS hcC⟩ : S) ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact congrArg (fun x : I => (x : G))
      (mem_center_iff.mp (hcentral (show (⟨c, hCI hcC⟩ : I) ∈ C.subgroupOf I from hcC))
        ⟨s, mem_sup_right s.property⟩)
  refine ⟨⟨c, hCS hcC⟩, ⟨⟨⟨c, hCS hcC⟩, hcz⟩, subset_closure ?_, rfl⟩, rfl⟩
  change (⟨⟨c, hCS hcC⟩, hcz⟩ : center S) ^ (2 ^ 1) = 1
  apply Subtype.ext
  apply Subtype.ext
  simpa using elemPow_eq_one_of_isElementaryAbelian c hcC (p := 2)

/-- The surviving C.1.34 cases, with one common actor marking for every
natural module and dual. Central submodules are retained in the sections. -/
def LinearThreeSurvivors (L S : Subgroup G)
    (e : CFSG.Quasithin.Chapter1.XiQuotient L ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop :=
    let Q := msQ L S
    let Z := CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
    let a := linearThreeActor e
    let v := Representation.specialLinearNatural (k := ZMod 2) 3
    (CFSG.Quasithin.ChapterC.IsBlock (L.subgroupOf (L ⊔ S)) ∧
      CFSG.Quasithin.ChapterC.IsSL3EvenBlock L 1 ∧ HasSectionModel L Q ⊥ a v) ∨
    (HasSectionModel L Q ⊥ a (v.prod v) ∧ MSNotCentralizerCore L S S) ∨
    (HasSectionModel L Z ⊥ a v ∧ HasSectionModel L Q Z a (v.dual.prod v.dual) ∧
      MSNotCentralizerCore L S S)

variable [Finite G]

/-- MS3 and the small central-omega bound exclude any central E4. -/
theorem no_central_four {L S C : Subgroup G}
    (hS : CFSG.Quasithin.Chapter1.IsSylowIn 2 S (L ⊔ S))
    (hms : MSNoCharacteristicNormal L S)
    (hbound : Nat.card (omegaCenterIn S) ≤ 4)
    [IsElementaryAbelian 2 C] (hcard : Nat.card C = 4)
    (hc : C ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ S)) : False := by
  have he : C = omegaCenterIn S :=
    eq_of_le_of_card_ge (central_elementary_le_omegaCenter hS hc) (hcard ▸ hbound)
  have hne : 1 < Nat.card (omegaCenterIn S) := by rw [← he, hcard]; decide
  exact omegaCenter_not_central hms hne (he ▸ hc)


/-- The complete C.1.34 disjunction reduces to cases (1)--(3) when R=S and
its central omega has order four. The input retains every module layer of
(4), and the actual point stabilizer of (5). This is an elimination lemma,
not a proof of the classification supplying that disjunction. -/
theorem linearThree_survivors {L S : Subgroup G}
    (hS : CFSG.Quasithin.Chapter1.IsSylowIn 2 S (L ⊔ S))
    (hms : MSNoCharacteristicNormal L S)
    (hcard : Nat.card (omegaCenterIn S) = 4)
    (e : CFSG.Quasithin.Chapter1.XiQuotient L ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcases : MSModuleAlternatives L S S 1 (ZMod 2) e) :
    LinearThreeSurvivors L S e := by
  rcases hcases with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · let := h.1
    exact (no_central_four hS hms hcard.le (by simpa using h.2.1) h.2.2.1).elim
  · exact (omegaCenter_not_central hms (by omega) h.2.2.2.1).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
