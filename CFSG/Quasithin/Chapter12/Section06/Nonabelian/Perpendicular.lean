module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
public import Theory.Representation.BinaryPermutation.EightGeometry
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# The literal point perpendicular in Section 12.6

The marked nonidentity point gives a nonzero functional under the
nondegenerate polar form of the six-dimensional permutation section.
Rank-nullity gives a five-dimensional kernel. Transport through the
original coordinates and subgroup inclusion proves its order and index,
and the point line is strictly contained in it.

These are the numerical inputs to the F.9.1 normal-core argument on the
original V₅, without replacing V or its perpendicular by a model subgroup.
Source: Aschbacher--Smith, setup and Lemma 12.6.24, printed pp.830--831.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
variable {G : Type*} [Group G] (D : Setup G)

/-- The full marked module has order 64. -/
theorem space_card : Nat.card D.V = 2 ^ 6 := by
  rw [Nat.card_congr D.coordinates.toEquiv]
  change Nat.card (natural (Fin 8)) = 2 ^ 6
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_natural]

/-- The actual perpendicular to a nonidentity point has order 32. -/
theorem perpendicular_card (hz : D.z ≠ 1) : Nat.card D.V₅ = 2 ^ 5 := by
  let f := form.polarBilin (D.coordinates D.z).toAdd
  have hn : f ≠ 0 := by
    intro he
    have hv : (D.coordinates D.z).toAdd = 0 := EightGeometry.polar_nondegenerate.1
      _ (fun w => by change f w = 0; rw [he]; rfl)
    exact hz (D.coordinates.injective (show D.coordinates D.z = D.coordinates 1 by
      rw [map_one]; exact hv))
  have hd : finrank (ZMod 2) f.ker = 5 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    rw [finrank_natural] at hh
    omega
  change Nat.card ((f.ker.toAddSubgroup.toSubgroup'.map
    D.coordinates.symm.toMonoidHom).map D.V.subtype) = _
  rw [card_map_of_injective D.V.subtype_injective,
    card_map_of_injective D.coordinates.symm.injective]
  change Nat.card f.ker = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]

/-- The index is relative to the unchanged original V. -/
theorem perpendicular_index (hz : D.z ≠ 1) : D.V₅.relIndex D.V = 2 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.V₅.subgroupOf D.V)
  have he : Nat.card (D.V₅.subgroupOf D.V) = Nat.card D.V₅ :=
    Nat.card_congr (subgroupOfEquivOfLe D.V₅_le).toEquiv
  rw [he,D.perpendicular_card hz,D.space_card] at hc
  change 2 ^ 6 = D.V₅.relIndex D.V * 2 ^ 5 at hc
  omega

/-- The point line is strictly smaller than its perpendicular. -/
theorem point_lt_perpendicular (hz : D.z ≠ 1) : D.V₁ < D.V₅ := by
  apply lt_of_le_of_ne D.V₁_le_V₅
  intro he
  have hc := congrArg (fun A : Subgroup G => Nat.card A) he
  rw [D.point_card hz,D.perpendicular_card hz] at hc
  norm_num at hc
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

public section
open Subgroup Module
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
variable {G : Type*} [Group G] (D : Setup G)
/-- Actual permutation coordinates transport the point stabilizer to the
normalizer of its literal perpendicular. -/
theorem normalizes_perpendicular (A : Subgroup G)
    (hAV : A ≤ normalizer (D.V : Set G)) (hAz : A ≤ D.Gz)
    (hact : ∀ a : A, ∃ p : Equiv.Perm (Fin 8), ∀ v : D.V,
      (D.coordinates (D.V.normalizerMonoidHom ⟨a,hAV a.property⟩ v)).toAdd =
        naturalRepresentation (Fin 8) p (D.coordinates v).toAdd) :
    A ≤ normalizer (D.V₅ : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg v hv
  let a : A := ⟨g,hg⟩
  let α := D.V.normalizerMonoidHom ⟨g,hAV hg⟩
  obtain ⟨p,hp⟩ := hact a
  have hz : α D.z = D.z := by
    apply Subtype.ext
    have he := hAz hg D.z.val (mem_zpowers D.z.val)
    change g * D.z.val * g⁻¹ = D.z.val
    rw [←he,mul_inv_cancel_right]
  have hfix : naturalRepresentation (Fin 8) p (D.coordinates D.z).toAdd =
      (D.coordinates D.z).toAdd := by
    rw [←hp D.z]
    change (D.coordinates (α D.z)).toAdd = _
    rw [hz]
  let w : D.V := ⟨v,D.V₅_le hv⟩
  have hpolar : form.polarBilin (D.coordinates D.z).toAdd
      (D.coordinates (α w)).toAdd =
      form.polarBilin (D.coordinates D.z).toAdd (D.coordinates w).toAdd := by
    calc
      _ = form.polarBilin
          (naturalRepresentation (Fin 8) p (D.coordinates D.z).toAdd)
          (naturalRepresentation (Fin 8) p (D.coordinates w).toAdd) := by
        rw [hfix,←hp w]
      _ = _ := by
        simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
          ←map_add,form_invariant]
  change (α w : G) ∈ D.V₅
  apply (D.mem_V₅_iff (α w)).mpr
  rw [hpolar]
  exact (D.mem_V₅_iff w).mp hv
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open Subgroup
variable {G : Type*} [Group G] (D : Setup G)

/-- The full point centralizer is in the literal source family. Its
nontrivial intrinsic two-core follows from the original central point. -/
theorem Gz_mem_Hz (hz : D.z ≠ 1)
    (hTz : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hout : ¬ D.Gz ≤ D.M) : D.Gz ∈ D.Hz := by
  have hTC : (D.T : Subgroup G) ≤ D.Gz :=
    hTz.trans (normalizer_le_centralizer_of_card_two D.V₁ (D.point_card hz))
  have hlocal : D.L₁ ⊔ (D.T : Subgroup G) ≤ D.Gz :=
    sup_le ((map_subtype_le _).trans inf_le_right) hTC
  let : IsElementaryAbelian 2 D.V := D.elementary
  let : IsElementaryAbelian 2 D.V₁ :=
    IsElementaryAbelian.of_le (D.V₁_le_V₅.trans D.V₅_le)
  have hcore : D.V₁ ≤ D.Gz.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.V₁)
      (le_centralizer D.V₁) (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨?_,fun x hx => hlocal (hx.elim mem_sup_left mem_sup_right)⟩,le_rfl,hout⟩
  intro he
  have hp : D.V₁ = ⊥ := bot_unique (hcore.trans he.le)
  have hc := D.point_card hz
  rw [hp] at hc
  simp at hc
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
