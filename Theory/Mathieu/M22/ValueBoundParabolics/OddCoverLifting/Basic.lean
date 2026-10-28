module

public import Theory.Mathieu.M22.ValueBoundParabolics.CoverGeneration
public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Odd central kernels and local Sylow overgroups

A characteristic complement inside the normal inner subgroup remains normal
under the outer two-group. Adjoining the specified Sylow two-subgroup does
not reintroduce the odd kernel: after quotienting by the inner complement,
the kernel has odd order and the Sylow image is a two-group.

`OddCentralSplitting` states the separate local splitting obligation. These
interfaces concern arbitrary finite central extensions, including nonsplit
ambient covers; they do not assume a universal-cover model.

Source: Aschbacher–Smith, E.4.3(2), printed pp. 241–242, combined manuscript
of 1 March 2004. The centrality required by the assembly is only inside L.
-/

public section
namespace Sporadic.Mathieu.M22ValueBound.OddCoverLifting
open Subgroup

/-- Adjoining a Sylow two-subgroup to a normal complement preserves disjointness
from an odd normal kernel. -/
theorem complement_adjoin_sylow {G : Type*} [Group G] [Finite G] (C D : Subgroup G) [C.Normal] [D.Normal]
    (hodd : Odd (Nat.card C)) (hCD : Disjoint C D) (T : Sylow 2 G)
    (hgen : C ⊔ D ⊔ (T : Subgroup G) = ⊤) :
    C.IsComplement' (D ⊔ (T : Subgroup G)) := by
  let q := QuotientGroup.mk' D
  have hdis : Disjoint (C.map q) ((T : Subgroup G).map q) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (T.isPGroup'.map q).exists_card_eq
    rw [hn]
    exact (hodd.coprime_two_right.coprime_dvd_left (C.card_map_dvd q)).pow_right n
  have hd : Disjoint C (D ⊔ (T : Subgroup G)) := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxC, hxH⟩
    have hxq : q x ∈ (T : Subgroup G).map q := by
      have hm := mem_map_of_mem q hxH
      simpa only [Subgroup.map_sup, (D.map_eq_bot_iff (f := q)).mpr (by simp [q]), bot_sup_eq] using hm
    have hq : q x = 1 := hdis.le_bot ⟨mem_map_of_mem q hxC, hxq⟩
    exact hCD.le_bot ⟨hxC, (QuotientGroup.eq_one_iff x).mp hq⟩
  apply isComplement'_of_disjoint_and_mul_eq_univ hd
  rw [← normal_mul, ← sup_assoc, hgen, coe_top]

/-- A characteristic complement in a normal subgroup extends across an outer
two-group to a complement containing the prescribed Sylow subgroup. -/
theorem exists_complement_containing_sylow
    {G : Type*} [Group G] [Finite G] (L C : Subgroup G) [L.Normal] [C.Normal]
    (hCL : C ≤ L) (hodd : Odd (Nat.card C)) (T : Sylow 2 G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (D : Subgroup L) [D.Characteristic] (hD : (C.subgroupOf L).IsComplement' D) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ C.IsComplement' H := by
  let D' := D.map L.subtype
  have hsup : C ⊔ D' = L := by
    have h := congrArg (Subgroup.map L.subtype) hD.sup_eq_top
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hCL, ← MonoidHom.range_eq_map, range_subtype] using h
  have hdis : Disjoint C D' := by
    have h := Subgroup.disjoint_map L.subtype_injective hD.disjoint
    simpa only [map_subgroupOf_eq_of_le hCL] using h
  refine ⟨D' ⊔ (T : Subgroup G), le_sup_right, ?_⟩
  exact complement_adjoin_sylow C D' hodd hdis T (by rw [hsup, hgen])

universe u

/-- The elementary symmetric-group splitting obligation. This only asks for
a complement; its characteristic property after adjoining a normal two-core
is supplied by the canonical two-element generation argument. -/
@[expose] def SymmetricOddCentralSplitting (n : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E]
    (f : E →* Equiv.Perm (Fin n)), Function.Surjective f →
    f.ker ≤ center E → Odd (Nat.card f.ker) →
    ∃ D : Subgroup E, f.ker.IsComplement' D

/-- The local splitting obligation for an odd central extension of a group
whose intrinsic two-core quotient is Sₙ. Existence is proved separately. -/
@[expose] def OddCentralSplitting (n : ℕ) : Prop :=
  ∀ (E F : Type u) [Group E] [Group F] [Finite E] [Finite F]
    (f : E →* F), Function.Surjective f → f.ker ≤ center E → Odd (Nat.card f.ker) →
    (F ⧸ pCore 2 F) ≃* Equiv.Perm (Fin n) →
    ∃ D : Subgroup E, D.Characteristic ∧ f.ker.IsComplement' D


end Sporadic.Mathieu.M22ValueBound.OddCoverLifting
