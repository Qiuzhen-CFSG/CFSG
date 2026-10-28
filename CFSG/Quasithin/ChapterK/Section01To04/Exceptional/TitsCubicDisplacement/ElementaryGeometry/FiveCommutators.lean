module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Conjugacy
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.RepresentativeGeneration.Packed
import all Theory.SpecificGroups.Tits.FiveFrobenius

/-!
# Five-element commutators for both marked Tits involutions

An explicit word conjugates the certified five-element u to an element inverted
by s1. A second word conjugates s4 to the actual quaternion square r², which
inverts u. For an inverted element x, the commutator is x⁻². Transport through
the certified Parrott–ATLAS equivalence gives witnesses in the literal
`Tits.fiveKernel`, and identifies the literal `fiveInverter` with the s4 class.

Each word equality is checked at the certified faithful three-point base.
Packed point maps keep the kernel reductions small; no external calculation
is used as a proof. Sources: the ATLAS five-local words in `FiveFrobenius`;
GM04 Lemma 8.8, internal p.57. Discovery and remaining bounds are in `Source.md`.

The private import accesses only the defining pullback of `fiveKernel` for
the internal transport proof. Its existing public boundary is unchanged;
the ATLAS kernel's closure is accessed through its public specification.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open Subgroup Tits Tits.FiveFrobenius Tits.Atlas1600ParrottData
open Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Tits.MinimumIndexFiveOvergroups.RepresentativeGeneration

private def a : Atlas1600Group := ⟨atlas1600A, atlas1600A_mem⟩
private def b : Atlas1600Group := ⟨atlas1600B, atlas1600B_mem⟩
private def longWord {G : Type*} [Group G] (a b : G) : G :=
  a * b * a * b ^ 2 * a * b ^ 2 * a * b * a * b ^ 2
private def w : Atlas1600Group := longWord a b
private def fastW : Equiv.Perm (Fin 1600) := longWord (Packed.perm 0) (Packed.perm 1)
private theorem w_val : w.val = fastW := by
  change longWord atlas1600A atlas1600B = _
  unfold fastW
  rw [Packed.perm_eq, Packed.perm_eq]
  rfl

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_inv (x : Atlas1600Group) : x⁻¹.val = x.val⁻¹ := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl
private theorem u_fast : u.val = Packed.perm 3 := u_val.trans (Packed.perm_eq 3).symm

set_option maxRecDepth 20000 in
private theorem long_inverts : atlas1600ParrottAssignment .s1 * (w * u * w⁻¹) *
    (atlas1600ParrottAssignment .s1)⁻¹ = (w * u * w⁻¹)⁻¹ := by
  apply threePoint_ext <;>
    simp only [val_mul, val_inv, w_val, u_fast, atlas1600ParrottAssignment_val] <;>
    decide +kernel

private def inverterWord {G : Type*} [Group G] (a b : G) : G :=
  b * a * b⁻¹ * a * b * a * b * a * b⁻¹ * a * b⁻¹ * a * b⁻¹ * a *
    b * a * b * a * b * a * b * a * b⁻¹ * a * b * a
private def wi : Atlas1600Group := inverterWord a b
private theorem wi_val : wi.val = inverterWord (Packed.perm 0) (Packed.perm 1) := by
  change inverterWord atlas1600A atlas1600B = _
  rw [Packed.perm_eq, Packed.perm_eq]
  rfl

set_option maxRecDepth 20000 in
private theorem inverter_conjugacy :
    wi * atlas1600ParrottAssignment .s4 * wi⁻¹ = r ^ 2 := by
  apply threePoint_ext <;>
    simp only [val_mul, val_inv, val_pow, wi_val, r_val,
      atlas1600ParrottAssignment_val] <;>
    decide +kernel

set_option maxRecDepth 20000 in
private theorem inverter_inverts : r ^ 2 * u * (r ^ 2)⁻¹ = u⁻¹ := by
  apply threePoint_ext <;>
    simp only [val_mul, val_inv, val_pow, r_val, u_fast] <;>
    decide +kernel

/-- The actual five-inverter lies in the root-marked s4 class. -/
theorem s4_isConj_fiveInverter : IsConj (parrottGenerator .s4) fiveInverter := by
  have h : IsConj (atlas1600ParrottAssignment .s4) (r ^ 2) :=
    isConj_iff.mpr ⟨wi, inverter_conjugacy⟩
  have hh := parrottFiniteImageEquiv.symm.toMonoidHom.map_isConj h
  simpa only [MulEquiv.coe_toMonoidHom, ← parrottFiniteImageEquiv_generator,
    MulEquiv.symm_apply_apply, fiveInverter] using hh

private theorem u_mem : u ∈ kernel := by
  rw [MinimumIndexFiveOvergroups.kernel_eq_closure]
  exact subset_closure (by simp)
private theorem u_inv_square_ne_one : u⁻¹ * u⁻¹ ≠ 1 := by
  intro he
  have hp := congrArg (fun x : Atlas1600Group => x.val 0) he
  change (u.val⁻¹ * u.val⁻¹) 0 = 0 at hp
  rw [u_val] at hp
  exact (by decide +kernel : (up⁻¹ * up⁻¹) 0 ≠ 0) hp

private theorem atlas_commutator_of_inverts (a w : Atlas1600Group)
    (h : a * (w * u * w⁻¹) * a⁻¹ = (w * u * w⁻¹)⁻¹) :
    ∃ x k : Atlas1600Group, k ∈ kernel ∧ k ≠ 1 ∧
      IsConj k (a * x * a⁻¹ * x⁻¹) := by
  refine ⟨w * u * w⁻¹, u⁻¹ * u⁻¹,
    mul_mem (inv_mem u_mem) (inv_mem u_mem), u_inv_square_ne_one, ?_⟩
  rw [h]
  exact isConj_iff.mpr ⟨w, by group⟩

private theorem parrott_commutator (a : Atlas1600Group)
    (h : ∃ x k : Atlas1600Group, k ∈ kernel ∧ k ≠ 1 ∧
      IsConj k (a * x * a⁻¹ * x⁻¹)) :
    ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (parrottFiniteImageEquiv.symm a * x * (parrottFiniteImageEquiv.symm a)⁻¹ * x⁻¹) := by
  obtain ⟨x, k, hk, hkn, hc⟩ := h
  refine ⟨parrottFiniteImageEquiv.symm x, parrottFiniteImageEquiv.symm k, ?_, ?_, ?_⟩
  · change parrottFiniteImageEquiv (parrottFiniteImageEquiv.symm k) ∈ kernel
    simpa only [MulEquiv.apply_symm_apply] using hk
  · intro he
    apply hkn
    have hh := congrArg parrottFiniteImageEquiv he
    simpa only [MulEquiv.apply_symm_apply, map_one] using hh
  · have hh := parrottFiniteImageEquiv.symm.toMonoidHom.map_isConj hc
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using hh

/-- The long-root representative has a nonidentity five-kernel commutator. -/
theorem long_five_commutator :
    ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (parrottGenerator .s1 * x * (parrottGenerator .s1)⁻¹ * x⁻¹) := by
  have h := parrott_commutator (atlas1600ParrottAssignment .s1)
    (atlas_commutator_of_inverts _ w long_inverts)
  simpa only [← parrottFiniteImageEquiv_generator, MulEquiv.symm_apply_apply] using h

/-- The literal five-complement involution itself has the required commutator. -/
theorem inverter_five_commutator :
    ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (fiveInverter * x * fiveInverter⁻¹ * x⁻¹) := by
  apply parrott_commutator (r ^ 2)
  apply atlas_commutator_of_inverts _ 1
  simpa only [one_mul, inv_one, mul_one] using inverter_inverts

/-- The short-root representative has a nonidentity five-kernel commutator. -/
theorem short_five_commutator :
    ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (parrottGenerator .s4 * x * (parrottGenerator .s4)⁻¹ * x⁻¹) :=
  commutator_conjugate s4_isConj_fiveInverter.symm inverter_five_commutator

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
