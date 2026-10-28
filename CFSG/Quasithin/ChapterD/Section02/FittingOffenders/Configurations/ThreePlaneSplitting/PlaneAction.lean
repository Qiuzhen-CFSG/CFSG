module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Fixed and moved lines in invariant support planes

In the reduced D.2.14 action, an invariant order-three subgroup has a
core-invariant support. If the actor fixed this support, `[P,A]=P` would
make the core fix it too, contradicting the coprime fixed/moved splitting.
On a binary plane a nontrivial elementary two-action has equal fixed and
moved lines. The proof uses rank-nullity for an involution and transports
both spaces through the actual support inclusion into the original module.

Source: Aschbacher--Smith, D.2.14(7)(ii), final paragraph on printed p.187.
-/

public section

open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem plane_involution (σ : Representation (ZMod 2) G W)
    (hdim : Module.finrank (ZMod 2) W = 2) (a : G) (ha : a * a = 1)
    (hne : σ a ≠ 1) :
    Module.finrank (ZMod 2) (σ a - 1).range = 1 ∧
      (σ a - 1).range = (σ a - 1).ker := by
  have hle : (σ a - 1).range ≤ (σ a - 1).ker := by
    rintro _ ⟨v, rfl⟩
    change σ a (σ a v - v) - (σ a v - v) = 0
    exact sub_eq_zero.mpr (involution_fixes_displacement σ ha v)
  have hpos : Module.finrank (ZMod 2) (σ a - 1).range ≠ 0 := by
    intro hz
    exact hne (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  have hsum := (σ a - 1).finrank_range_add_finrank_ker
  have hbound := Submodule.finrank_mono hle
  refine ⟨by omega, Submodule.eq_of_le_of_finrank_eq hle (by omega)⟩

omit [FiniteDimensional (ZMod 2) W] in
private theorem fixes_binary_line (σ : Representation (ZMod 2) G W)
    (L : Submodule (ZMod 2) W) (hL : Module.finrank (ZMod 2) L = 1)
    (a : G) (hstable : ∀ v ∈ L, σ a v ∈ L) : ∀ v ∈ L, σ a v = v := by
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have he := eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (he ▸ hstable v hv)
  have hc0 : c ≠ 0 := by
    intro hz
    have hzero : σ a v = 0 := by simpa [hz] using hc.symm
    have hh := congrArg (σ a⁻¹) hzero
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hh
    exact hv0 hh
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

private theorem elementary_plane_data [IsElementaryAbelian 2 G]
    (σ : Representation (ZMod 2) G W) (hdim : Module.finrank (ZMod 2) W = 2)
    (hne : ∃ a, σ a ≠ 1) :
    Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ ⊤) = 1 ∧
      Module.finrank (ZMod 2) (fixedSpace σ ⊤) = 1 := by
  obtain ⟨a, ha⟩ := hne
  have hsquare (g : G) : g * g = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 G) g
  obtain ⟨hr, hrk⟩ := plane_involution σ hdim a (hsquare a) ha
  let L := (σ a - 1).range
  have hfixed : L ≤ fixedSpace σ ⊤ := by
    intro v hv b
    apply fixes_binary_line σ L hr b.val ?_ v hv
    rintro _ ⟨w, rfl⟩
    refine ⟨σ b w, ?_⟩
    change σ a (σ b w) - σ b w = σ b (σ a w - w)
    rw [map_sub]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  have hfixeq : fixedSpace σ ⊤ = L := by
    apply le_antisymm ?_ hfixed
    intro v hv
    rw [show L = (σ a - 1).ker from hrk]
    exact sub_eq_zero.mpr (hv ⟨a, Subgroup.mem_top a⟩)
  have hmove : subspaceCommutator σ ⊤ ⊤ = L := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, _, v, _, rfl⟩
      by_cases hb : σ b = 1
      · simp [hb]
      obtain ⟨hbr, hbk⟩ := plane_involution σ hdim b (hsquare b) hb
      have hlk : L ≤ (σ b - 1).ker := by
        intro w hw
        exact sub_eq_zero.mpr (hfixed hw ⟨b, Subgroup.mem_top b⟩)
      have he : L = (σ b - 1).ker := Submodule.eq_of_le_of_finrank_eq hlk
        (by rw [← hbk]; exact hr.trans hbr.symm)
      rw [he, ← hbk]
      exact ⟨v, rfl⟩
    · rintro _ ⟨v, rfl⟩
      exact Submodule.subset_span ⟨a, Subgroup.mem_top a, v, Submodule.mem_top, rfl⟩
  exact ⟨hmove ▸ hr, hfixeq ▸ hr⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite G] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original support of an invariant core line has one moved dimension
and one fixed dimension under the original actor. -/
theorem Reduced.invariant_plane_data {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 2) :
    A ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Z) ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator ρ (subspaceCommutator ρ ⊤ Z) A) = 1 ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1 := by
  let U := subspaceCommutator ρ ⊤ Z
  change Module.finrank (ZMod 2) U = 2 at hdim
  have htop (X : Subgroup G) : X ≤ subspaceStabilizer ρ ⊤ :=
    le_subspaceStabilizer ρ ⊤ (by intros; trivial)
  have hA : A ≤ subspaceStabilizer ρ U :=
    subspaceCommutator_invariant_normalizer ρ (htop A) hZ.2.2
  let : IsElementaryAbelian 3 P := h.elementary
  have hP : P ≤ subspaceStabilizer ρ U := by
    apply subspaceCommutator_invariant_normalizer ρ (htop P)
    exact ((Subgroup.le_centralizer P).trans (Subgroup.centralizer_le hZ.1)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hn : ¬ U ≤ fixedSpace ρ A := by
    intro hf
    have hfixP : U ≤ fixedSpace ρ P := by
      rw [← h.core_commutator]
      exact le_fixedSpace_commutator_of_invariant ρ hP hf
    have hfixZ : U ≤ fixedSpace ρ Z :=
      hfixP.trans (fixedSpace_antitone ρ hZ.1)
    have hb : U = ⊥ :=
      ((odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))).disjoint.eq_bot ▸
        (inf_eq_left.mpr hfixZ).symm)
    have hz : Module.finrank (ZMod 2) U = 0 := Submodule.finrank_eq_zero.mpr hb
    omega
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let σ : Representation (ZMod 2) A U :=
    (stabilizerRepresentation ρ U).comp (Subgroup.inclusion hA)
  have hne : ∃ a, σ a ≠ 1 := by
    by_contra! he
    apply hn
    intro v hv a
    exact congrArg Subtype.val (LinearMap.congr_fun (he a) ⟨v, hv⟩)
  obtain ⟨hm, hf⟩ := elementary_plane_data σ hdim hne
  have hmmap : (subspaceCommutator σ ⊤ ⊤).map U.subtype =
      subspaceCommutator ρ U A := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨a, _, v, _, rfl⟩
      exact Submodule.subset_span ⟨a, a.property, v, v.property, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, v, hv, rfl⟩
      refine ⟨σ ⟨a, ha⟩ ⟨v, hv⟩ - ⟨v, hv⟩, ?_, rfl⟩
      exact Submodule.subset_span
        ⟨⟨a, ha⟩, Subgroup.mem_top _, ⟨v, hv⟩, Submodule.mem_top, rfl⟩
  have hfmap : (fixedSpace σ ⊤).map U.subtype = U ⊓ fixedSpace ρ A := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property, fun a => congrArg Subtype.val (hu ⟨a, Subgroup.mem_top a⟩)⟩
    · rintro ⟨hv, hf⟩
      refine ⟨⟨v, hv⟩, ?_, rfl⟩
      intro a
      exact Subtype.ext (hf a.val)
  refine ⟨hA, ?_, ?_⟩
  · rw [← hmmap, Submodule.finrank_map_subtype_eq]
    exact hm
  · rw [← hfmap, Submodule.finrank_map_subtype_eq]
    exact hf

end CFSG.Quasithin.ChapterD.FittingConfigurations
