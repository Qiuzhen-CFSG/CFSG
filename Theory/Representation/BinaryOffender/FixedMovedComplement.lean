module

public import Theory.Representation.GoldschmidtONan.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Order.CompleteLattice.Finset


/-!
# Fixed complements assembled from natural supports

An odd normal subgroup whose fixed space misses a support gives an invariant
fixed complement whenever every displacement lies in that support. Distinct
supports which fix one another can then be assembled by finite induction.
This is the linear splitting used for the concrete binary factors in
Aschbacher–Smith B.1.8 and 14.1.7 (printed pp.70 and 977).
-/

public section

open Subgroup Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem isCompl_support_fixed_of_normal_odd
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal] [Finite N]
    (hodd : Odd (Nat.card N)) (W : Submodule (ZMod 2) V)
    (hmove : ∀ g v, ρ g v - v ∈ W)
    (hdis : Disjoint W (fixedSpace ρ N)) : IsCompl W (fixedSpace ρ ⊤) := by
  have hfixed : fixedSpace ρ N = fixedSpace ρ ⊤ := by
    apply le_antisymm ?_ (fun v hv n => hv ⟨n, Subgroup.mem_top _⟩)
    intro v hv g
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hdis
    · exact hmove g v
    · exact (fixedSpace ρ N).sub_mem (Representation.le_comap_invariants ρ N g hv) hv
  rw [← hfixed]
  refine ⟨hdis, ?_⟩
  have hs := (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd).symm
  apply codisjoint_iff.mpr
  apply top_unique
  rw [← hs.sup_eq_top]
  apply sup_le_sup_right
  apply Submodule.span_le.mpr
  rintro _ ⟨g, _, v, _, rfl⟩
  exact hmove g v

end Representation

namespace Submodule
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem isCompl_sup_inf_of_cross_le (A B C D : Submodule R V)
    (hA : IsCompl A B) (hC : IsCompl C D) (hAD : A ≤ D) (hCB : C ≤ B) :
    IsCompl (A ⊔ C) (B ⊓ D) := by
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hv hf
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    have haB : a ∈ B := by
      have h := B.sub_mem hf.1 (hCB hc)
      simpa only [add_sub_cancel_right] using h
    have ha0 := Submodule.disjoint_def.mp hA.disjoint a ha haB
    have hcD : c ∈ D := by
      have h := D.sub_mem hf.2 (hAD ha)
      simpa only [add_sub_cancel_left] using h
    have hc0 := Submodule.disjoint_def.mp hC.disjoint c hc hcD
    simp [ha0,hc0]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp
      (show v ∈ A ⊔ B by rw [hA.sup_eq_top]; trivial)
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp
      (show b ∈ C ⊔ D by rw [hC.sup_eq_top]; trivial)
    have hdB : d ∈ B := by
      have h := B.sub_mem hb (hCB hc)
      rw [← hcd] at h
      simpa only [add_sub_cancel_left] using h
    refine Submodule.mem_sup.mpr ⟨a+c, Submodule.add_mem _
      (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hc), d, ⟨hdB,hd⟩, ?_⟩
    rw [add_assoc,hcd,he]

theorem isCompl_iSup_iInf_of_cross_le {ι : Type*} [Finite ι]
    (W F : ι → Submodule R V) (hc : ∀ i, IsCompl (W i) (F i))
    (hcross : ∀ i j, i ≠ j → W i ≤ F j) : IsCompl (⨆ i, W i) (⨅ i, F i) := by
  classical
  let := Fintype.ofFinite ι
  have hs (s : Finset ι) : IsCompl (⨆ i ∈ s, W i) (⨅ i ∈ s, F i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompl_bot_top : IsCompl (⊥ : Submodule R V) ⊤)
    | @insert i s hi ih =>
      rw [Finset.iSup_insert, Finset.iInf_insert]
      apply isCompl_sup_inf_of_cross_le (W i) (F i) _ _ (hc i) ih
      · exact le_iInf fun j => le_iInf fun hj => hcross i j (by rintro rfl; exact hi hj)
      · exact iSup_le fun j => iSup_le fun hj => hcross j i (by rintro rfl; exact hi hj)
  simpa using hs Finset.univ

end Submodule
