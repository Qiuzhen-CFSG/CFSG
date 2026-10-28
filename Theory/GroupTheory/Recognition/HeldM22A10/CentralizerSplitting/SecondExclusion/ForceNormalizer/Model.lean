module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Fusion

/-!
# Finite model interfaces for the remaining Held subgroup calculation

The two word enumerations give direct finite enumerations of the Sylow and its
transfer kernel. These avoid testing subgroup membership on every element of
the larger group during subsequent finite calculations. `CandidateProperty`
states the exact remaining intrinsic-radical assertion for the proposed
transfer proof of Huppert--Blackburn III, XII.1.18(b), p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion
open Subgroup

namespace Model

@[expose] public def sylowElement (i : Fin 128) : sylowSubgroup :=
  ⟨element (sylowIndex i), sylow_element_mem i⟩

public theorem sylowElement_bijective : Function.Bijective sylowElement := by
  constructor
  · intro i j h
    have hinj : Function.Injective sylowIndex :=
      (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel :
        ∀ i : Fin 127, sylowIndex i.castSucc < sylowIndex i.succ)).injective
    exact hinj (element_bijective.1 (congrArg Subtype.val h))
  · intro x
    obtain ⟨i, hi⟩ := exists_sylow_element x x.property
    exact ⟨i, Subtype.ext hi⟩

public instance instFintypeSylowSubgroup : Fintype sylowSubgroup :=
  Fintype.ofBijective sylowElement sylowElement_bijective

@[expose] public def transferElement (i : Fin 64) : transferSubgroup :=
  ⟨element (transferIndex i), transfer_element_mem i⟩

public theorem transferElement_bijective : Function.Bijective transferElement := by
  constructor
  · intro i j h
    have hinj : Function.Injective transferIndex :=
      (Fin.strictMono_iff_lt_succ.mpr (by decide +kernel :
        ∀ i : Fin 63, transferIndex i.castSucc < transferIndex i.succ)).injective
    exact hinj (element_bijective.1 (congrArg Subtype.val h))
  · intro x
    obtain ⟨i, hi⟩ := exists_transfer_element x x.property
    exact ⟨i, Subtype.ext hi⟩

public instance instFintypeTransferSubgroup : Fintype transferSubgroup :=
  Fintype.ofBijective transferElement transferElement_bijective

end Model

namespace ForceNormalizer

/-- The precise remaining concrete assertion: intersections with the transfer
kernel are characteristic in every centric intrinsic-radical subgroup except
the specified exceptional subgroup. -/
@[expose] public def CandidateProperty : Prop :=
  ∀ U : Subgroup NonsplitModels.Second, U ≤ Model.sylowSubgroup →
    (Model.sylowSubgroup ⊓ centralizer (U : Set NonsplitModels.Second)) ≤ U →
    IntrinsicRadicalIn Model.sylowSubgroup U →
    (Model.transferSubgroup.subgroupOf U).Characteristic ∨ U = Model.exceptionalSubgroup

end ForceNormalizer
end Theory.GroupTheory.HeldM22A10.SecondExclusion
