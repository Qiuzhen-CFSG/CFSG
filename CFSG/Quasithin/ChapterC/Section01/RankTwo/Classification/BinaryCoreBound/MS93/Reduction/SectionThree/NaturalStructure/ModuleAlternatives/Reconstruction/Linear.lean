module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Conventions
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Linear coordinates for source subgroups of X

The subgroup/subspace correspondence preserves joins and the full fixed part.
Literal conjugation through the specified quotient identifies subgroup
commutators with spans of action differences. These comparisons do not assume
that [X,Ltilde] equals U.
Source: Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Reconstruction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
local instance : IsElementaryAbelian 2 (X R (alpha R)) := X_elementary R (alpha R)

noncomputable abbrev space (H : Subgroup (FreeAmalgam R)) :
    Submodule (ZMod 2) (Additive (X R (alpha R))) :=
  AddSubgroup.toZModSubmodule 2 (H.subgroupOf (X R (alpha R))).toAddSubgroup

abbrev lattice : Subgroup (X R (alpha R)) ≃o
    Submodule (ZMod 2) (Additive (X R (alpha R))) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

noncomputable abbrev ambient (W : Submodule (ZMod 2) (Additive (X R (alpha R)))) :
    Subgroup (FreeAmalgam R) := (lattice.symm W).map (X R (alpha R)).subtype

omit [Finite M] in
theorem ambient_space {H : Subgroup (FreeAmalgam R)} (hH : H ≤ X R (alpha R)) :
    ambient (space H) = H := map_subgroupOf_eq_of_le hH

omit [Finite M] in
theorem space_injective {H K : Subgroup (FreeAmalgam R)}
    (hH : H ≤ X R (alpha R)) (hK : K ≤ X R (alpha R)) (h : space H = space K) : H = K := by
  simpa only [ambient_space hH, ambient_space hK] using congrArg ambient h

omit [Finite M] in
theorem space_sup {H K : Subgroup (FreeAmalgam R)}
    (hH : H ≤ X R (alpha R)) (hK : K ≤ X R (alpha R)) :
    space (H ⊔ K) = space H ⊔ space K := by
  change lattice ((H ⊔ K).subgroupOf _) = _
  rw [subgroupOf_sup hH hK, lattice.map_sup]
  rfl

theorem space_fixed (source : LocalSource L R) :
    space (fixedPart R) = fixedSpace (Offenders.linearize (xAction source)) ⊤ := by
  ext v
  have hf := layerAction_fixed_iff source (X R (alpha R))
    (X_normalized R (alpha R)) (Q_le_centralizer_X R (alpha R)) v.toMul
  constructor
  · intro hv g
    exact congrArg Additive.ofMul (hf.mpr hv.2 g.val)
  · intro hv
    exact ⟨v.toMul.property, hf.mp (fun g => congrArg Additive.toMul (hv ⟨g, mem_top g⟩))⟩

noncomputable def subrepresentation (source : LocalSource L R)
    (H : Subgroup (FreeAmalgam R))
    (hn : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R))) :
    Subrepresentation (Offenders.linearize (xAction source)) where
  toSubmodule := space H
  apply_mem_toSubmodule g v hv := by
    obtain ⟨m, rfl⟩ := source.projection_surjective g
    change (xAction source (source.projection m) v.toMul : FreeAmalgam R) ∈ H
    rw [xAction, layerAction_apply]
    exact (mem_normalizer_iff.mp (hn (baseEquiv (R := R) m).property) _).mp hv

omit [Finite M] in
theorem commutator_le_X (H : Subgroup (FreeAmalgam R)) (hH : H ≤ X R (alpha R)) :
    ⁅H, Ltilde R (alpha R)⁆ ≤ X R (alpha R) :=
  (commutator_mono hH le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer _).trans (X_normalized R _)))

theorem space_commutator (source : LocalSource L R)
    (H : Subgroup (FreeAmalgam R)) (hH : H ≤ X R (alpha R))
    (hn : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R))) :
    space ⁅H, Ltilde R (alpha R)⁆ =
      subspaceCommutator (Offenders.linearize (xAction source)) (space H) ⊤ := by
  let ρ := Offenders.linearize (xAction source)
  let W := subspaceCommutator ρ (space H) ⊤
  apply le_antisymm
  · have hc : ⁅H, Ltilde R (alpha R)⁆ ≤ ambient W := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l hl h hh
      obtain ⟨m, hm⟩ := (baseEquiv (R := R)).surjective
        ⟨l, Ltilde_le_stabilizer (alpha R) hl⟩
      have hm' : embedM R m = l := congrArg Subtype.val hm
      let v : X R (alpha R) := ⟨h, hH hh⟩
      refine ⟨(ρ (source.projection m) (Additive.ofMul v) - Additive.ofMul v).toMul, ?_, ?_⟩
      · change ρ (source.projection m) (Additive.ofMul v) - Additive.ofMul v ∈ W
        exact Submodule.subset_span ⟨_, mem_top _, _, hh, rfl⟩
      · change (xAction source (source.projection m) v : FreeAmalgam R) / h = _
        rw [div_eq_mul_inv, xAction, layerAction_apply, hm']
        rfl
    intro v hv
    obtain ⟨w, hw, he⟩ := hc hv
    have hwv : w = v.toMul := Subtype.ext he
    subst w
    exact hw
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, hv, rfl⟩
    obtain ⟨m, rfl⟩ := source.projection_surjective g
    change (xAction source (source.projection m) v.toMul : FreeAmalgam R) /
      (v.toMul : FreeAmalgam R) ∈ ⁅H, Ltilde R (alpha R)⁆
    rw [div_eq_mul_inv, xAction, layerAction_apply]
    have he : ⁅H, Ltilde R (alpha R)⁆ = ⁅H, stabilizer R (alpha R)⁆ :=
      commutator_eq_of_centralizing_sup
        (by rw [sup_comm]; exact source.local_generation (alpha R) rfl)
        ((Q_le_centralizer_X R (alpha R)).trans (centralizer_le hH))
        ((Ltilde_le_stabilizer _).trans hn)
    rw [he, commutator_comm]
    exact commutator_mem_commutator (baseEquiv (R := R) m).property hv


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Reconstruction
