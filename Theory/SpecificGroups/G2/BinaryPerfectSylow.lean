module
public import Theory.SpecificGroups.G2.BinarySolvableSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.GroupTheory.SolvableSylowOvergroupLifts
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Perfect subgroups normalized by a full binary G₂ Sylow

A nontrivial perfect subgroup lies in the derived group. The supplied full
Sylow restricts to a Sylow there, so the solvability of proper Sylow
overgroups forces the subgroup to be the entire derived group. Its order
6048 excludes intrinsic two-core quotient orders 168 and 20160.

This is the actual G₂(2) comparison used in Aschbacher--Smith 12.9.4,
printed p.859. The split-octonion carrier and finite calculations retain
the ATLAS attribution in the imported modules and LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinaryPerfectSylow

/-- A nontrivial perfect subgroup normalized by the full Sylow is G₂(2)′. -/
theorem eq_derived (B : Subgroup (Model (ZMod 2))) [Group.IsPerfect B]
    (hne : B ≠ ⊥) (S : Sylow 2 (Model (ZMod 2)))
    (hn : (S : Subgroup (Model (ZMod 2))) ≤ normalizer (B : Set _)) :
    B = commutator (Model (ZMod 2)) := by
  let D := commutator (Model (ZMod 2))
  have hBD : B ≤ D := by
    calc B = ⁅B,B⁆ := commutator_eq_self.symm
         _ ≤ D := commutator_mono le_top le_top
  let e := subgroupOfEquivOfLe hBD
  let : Group.IsPerfect (B.subgroupOf D) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hne
  let : Nontrivial (B.subgroupOf D) := e.surjective.nontrivial
  let : Group.IsPerfect D := by
    let := BinaryException.H_isPerfect
    let a : BinaryException.H ≃* D :=
      MulEquiv.subgroupCongr BinaryParabolicPair.commutator_eq_longRootClosure.symm
    exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal D
  have hnorm : (R : Subgroup D) ≤ normalizer (B.subgroupOf D : Set D) := by
    intro r hr b
    rw [hR] at hr
    exact hn hr (b : Model (ZMod 2))
  have he := BinaryDerived.solvableSylowOvergroups.eq_top_of_sylow_normalizes R
    (B.subgroupOf D) hnorm (Group.IsPerfect.not_isSolvable _)
  exact le_antisymm hBD (subgroupOf_eq_top.mp he)

/-- Neither original binary point-residual quotient can occur in G₂(2). -/
theorem core_card_excluded (B : Subgroup (Model (ZMod 2))) [Group.IsPerfect B]
    (S : Sylow 2 (Model (ZMod 2)))
    (hn : (S : Subgroup (Model (ZMod 2))) ≤ normalizer (B : Set _))
    (hc : Nat.card (B ⧸ pCore 2 B) = 168 ∨ Nat.card (B ⧸ pCore 2 B) = 20160) : False := by
  have hne : B ≠ ⊥ := by
    intro he
    have hh := Nat.le_of_dvd (Nat.card_pos (α := B)) (card_quotient_dvd_card (pCore 2 B))
    have hcB : Nat.card B = 1 := he ▸ card_bot
    rcases hc with hc | hc <;> rw [hc] at hh <;> omega
  have hcard : Nat.card B = 6048 := by
    rw [eq_derived B hne S hn]
    exact LieAutomorphismExtensions.card_binaryDerived
  have hm := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hcard] at hm
  rcases hc with hc | hc
  · rw [hc] at hm
    have h3 : 3 ∣ Nat.card (pCore 2 B) := by omega
    obtain ⟨k,hk⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 B)).exists_card_eq
    rw [hk] at h3
    exact (by decide : ¬ 3 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3)) h3)
  · rw [hc] at hm
    have hp := Nat.card_pos (α := pCore 2 B)
    omega
end Atlas.G2.BinaryPerfectSylow

