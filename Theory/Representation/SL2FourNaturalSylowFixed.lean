module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Sylow fixed lines in the restricted natural S₅ module

The actual SL₂(4) marking makes S₅ transitive on the fifteen nonzero
vectors. Their stabilizers have order eight and hence are Sylow subgroups.
The Sylow two-subgroups of S₅ are self-normalizing, so each fixes exactly
one nonzero vector. The proof uses the given binary action; it does not
choose semilinear coordinates for the odd permutations.

This supplies the point-stabilizer and fixed-line calculations used in
Aschbacher–Smith, 14.7.67 and 14.7.70, printed pp.1070 and 1074.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNaturalSylowFixed
open Subgroup SL2FourNatural

abbrev S5 := Equiv.Perm (Fin 5)

private def doubleSwap : S5 := Equiv.swap 0 1 * Equiv.swap 2 3
private def firstSwap : S5 := Equiv.swap 0 1
private def crossSwap : S5 := Equiv.swap 0 2 * Equiv.swap 1 3
private def eight : Subgroup S5 := centralizer ({doubleSwap} : Set S5)

private theorem mem_eight (g : S5) : g ∈ eight ↔ doubleSwap * g = g * doubleSwap := by
  simp only [eight, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

private theorem eight_card : Nat.card eight = 8 := by
  let e : eight ≃ {g : S5 // doubleSwap * g = g * doubleSwap} :=
    Equiv.subtypeEquivRight mem_eight
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

private theorem eight_normalizer : normalizer (eight : Set S5) = eight := by
  have hc : ∀ g : S5,
      doubleSwap * (g * firstSwap * g⁻¹) = (g * firstSwap * g⁻¹) * doubleSwap →
      doubleSwap * (g * crossSwap * g⁻¹) = (g * crossSwap * g⁻¹) * doubleSwap →
      doubleSwap * g = g * doubleSwap := by decide +kernel
  apply le_antisymm
  · intro g hg
    apply (mem_eight g).mpr
    apply hc g
    · apply (mem_eight _).mp
      exact (mem_normalizer_iff.mp hg firstSwap).mp ((mem_eight _).mpr (by decide +kernel))
    · apply (mem_eight _).mp
      exact (mem_normalizer_iff.mp hg crossSwap).mp ((mem_eight _).mpr (by decide +kernel))
  · exact le_normalizer

private def standardSylow : Sylow 2 S5 := Sylow.ofCard eight (by
  rw [eight_card, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]
  decide +kernel)

private theorem sylow_normalizer (P : Sylow 2 S5) :
    normalizer (P : Set S5) = (P : Subgroup S5) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S5 P standardSylow
  have he : (P : Subgroup S5).map (MulAut.conj g).toMonoidHom = eight :=
    congrArg (fun Q : Sylow 2 S5 => (Q : Subgroup S5)) hg
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  exact (map_equiv_normalizer_eq (P : Subgroup S5) (MulAut.conj g)).trans
    (by rw [he, eight_normalizer])

/-- The stabilizer retains the supplied action and the original vector. -/
def vectorStabilizer (ρ : Representation (ZMod 2) S5 V) (v : V) : Subgroup S5 where
  carrier := {g | ρ g v = v}
  one_mem' := by change ρ 1 v = v; simp
  mul_mem' := by
    intro g h hg hh
    change ρ g v = v at hg
    change ρ h v = v at hh
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g v = v at hg
    change ρ g⁻¹ v = v
    have h := congrArg (ρ g⁻¹) hg
    simpa only [ρ.inv_self_apply] using h.symm

private abbrev action (ρ : Representation (ZMod 2) S5 V) : MulAction S5 V where
  smul g v := ρ g v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul g h v := by
    change ρ (g * h) v = ρ g (ρ h v)
    simp [Module.End.mul_apply]

private theorem stabilizer_action (ρ : Representation (ZMod 2) S5 V) (g : S5) (v : V) :
    vectorStabilizer ρ (ρ g v) =
      (vectorStabilizer ρ v).map (MulAut.conj g).toMonoidHom := by
  let := action ρ
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g v

variable (ρ : Representation (ZMod 2) S5 V)
  (e : SL ≃* alternatingGroup (Fin 5))
  (he : ∀ g v, ρ (e g) v = SL2FourNatural.action g v)

include e he

private theorem transitive (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : S5, ρ g v = w := by
  obtain ⟨g, hg⟩ := transitive_nonzero v w hv hw
  exact ⟨e g, (he g v).trans hg⟩

/-- The point stabilizer has the full Sylow two-order of S₅. -/
theorem vectorStabilizer_card (v : V) (hv : v ≠ 0) :
    Nat.card (vectorStabilizer ρ v) = 8 := by
  classical
  let := action ρ
  have ho : MulAction.orbit S5 v = {w : V | w ≠ 0} := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩ hz
      change ρ g v = 0 at hz
      exact hv (by simpa only [ρ.inv_self_apply, map_zero] using congrArg (ρ g⁻¹) hz)
    · exact transitive ρ e he v w hv
  have hc : Nat.card (MulAction.orbit S5 v) = 15 := by
    rw [ho, Nat.card_eq_fintype_card]
    change Fintype.card {w : V // ¬ w = 0} = 15
    rw [Fintype.card_subtype_compl, Fintype.card_unique (α := {w : V // w = 0}),
      card_vector]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S5 v)
  rw [Nat.card_prod, hc] at h
  change 15 * Nat.card (vectorStabilizer ρ v) = Nat.card S5 at h
  rw [Nat.card_eq_fintype_card (α := S5), Fintype.card_perm] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 15) h

/-- The actual nonzero-vector stabilizer, as a Sylow subgroup. -/
def pointSylow (v : V) (hv : v ≠ 0) : Sylow 2 S5 :=
  Sylow.ofCard (vectorStabilizer ρ v) (by
    rw [vectorStabilizer_card ρ e he v hv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
    decide +kernel)

theorem pointSylow_coe (v : V) (hv : v ≠ 0) :
    (pointSylow ρ e he v hv : Subgroup S5) = vectorStabilizer ρ v := rfl

/-- If a Sylow fixes a nonzero vector, it is precisely that vector's stabilizer. -/
theorem vectorStabilizer_eq_of_fixed (P : Sylow 2 S5) (v : V) (hv : v ≠ 0)
    (hfix : ∀ g : P, ρ g v = v) : vectorStabilizer ρ v = (P : Subgroup S5) := by
  exact P.is_maximal' (pointSylow ρ e he v hv).isPGroup' (fun g hg => hfix ⟨g, hg⟩)

/-- Each Sylow fixes exactly one nonzero vector of this literal action. -/
theorem exists_unique_nonzero_fixed (P : Sylow 2 S5) :
    ∃! v : V, v ≠ 0 ∧ ∀ g : P, ρ g v = v := by
  let v₀ : V := ![1, 0]
  have hv₀ : v₀ ≠ 0 := by simp [v₀]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S5 (pointSylow ρ e he v₀ hv₀) P
  let v := ρ g v₀
  have hv : v ≠ 0 := by
    intro hz
    change ρ g v₀ = 0 at hz
    apply hv₀
    simpa only [ρ.inv_self_apply, map_zero] using congrArg (ρ g⁻¹) hz
  have hs : vectorStabilizer ρ v = (P : Subgroup S5) := by
    rw [stabilizer_action]
    exact congrArg (fun Q : Sylow 2 S5 => (Q : Subgroup S5)) hg
  have hfix : ∀ a : P, ρ a v = v := by
    intro a
    change a.val ∈ vectorStabilizer ρ v
    rw [hs]
    exact a.property
  refine ⟨v, ⟨hv, hfix⟩, ?_⟩
  intro w hw
  obtain ⟨a, ha⟩ := transitive ρ e he v w hv hw.1
  have hsw := vectorStabilizer_eq_of_fixed ρ e he P w hw.1 hw.2
  have hn : a ∈ normalizer (P : Set S5) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (P : Subgroup S5).map (MulAut.conj a).toMonoidHom =
          (vectorStabilizer ρ v).map (MulAut.conj a).toMonoidHom := by rw [hs]
      _ = vectorStabilizer ρ (ρ a v) := (stabilizer_action ρ a v).symm
      _ = (P : Subgroup S5) := by rw [ha, hsw]
  have hp : a ∈ P := by
    change a ∈ (P : Subgroup S5)
    rw [← sylow_normalizer P]
    exact hn
  exact ha.symm.trans (hfix ⟨a, hp⟩)

/-- The binary fixed subspace of each actual Sylow has dimension one. -/
theorem fixed_finrank (P : Sylow 2 S5) :
    Module.finrank (ZMod 2) (Representation.invariants (ρ.comp (P : Subgroup S5).subtype)) = 1 := by
  obtain ⟨v, hv, hu⟩ := exists_unique_nonzero_fixed ρ e he P
  let w : Representation.invariants (ρ.comp (P : Subgroup S5).subtype) := ⟨v, hv.2⟩
  apply finrank_eq_one w (fun h => hv.1 (congrArg Subtype.val h))
  intro x
  by_cases hx : x.val = 0
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    exact Subtype.ext hx.symm
  · refine ⟨1, ?_⟩
    rw [one_smul]
    exact Subtype.ext (hu x.val ⟨hx, x.property⟩).symm

end Representation.SL2FourNaturalSylowFixed
