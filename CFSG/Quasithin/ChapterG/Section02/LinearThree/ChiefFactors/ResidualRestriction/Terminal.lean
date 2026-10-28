module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Alignment
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.GroupTheory.PCoreFrattiniTransport
/-!
# The cubic terminal quotient of the actual binary local residual

The aligned star map surjects from the literal L₁ onto the marked affine
A₄ subgroup of SL₃(2). Its kernel is a two-group because it is contained
in the original star kernel. Lifting the two-core gives an actual quotient
isomorphism, and the model quotient has order three. Consequently every
two-group section of L₁/O₂(L₁) is trivial, in particular every proposed
two-chief factor above the local core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.5(8) and the binary application 12.8.8, printed pp.335–336,851–852.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction

variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : Hypothesis D F n g h)

theorem modelProjection_kernel_twoGroup : IsPGroup 2 (modelProjection d).ker := by
  rw [modelProjection, MonoidHom.ker_comp_of_injective _ _ d.model.injective]
  have he : (starProjection D).ker =
      (pCore 2 D.LT).comap (inclusion (show D.L ≤ D.LT from le_sup_left)) := by
    ext l
    change starProjection D l = 1 ↔
      (inclusion (show D.L ≤ D.LT from le_sup_left) l) ∈ pCore 2 D.LT
    constructor
    · intro hl
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hl)
    · intro hl
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hl)
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

namespace PointAlignment
variable {d} (a : PointAlignment d)

theorem projection_kernel_twoGroup : IsPGroup 2 a.projection.ker := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a.basis⁻¹).injective]
  exact modelProjection_kernel_twoGroup d
end PointAlignment

namespace Binary
open Matrix.PSL3Two.MarkedAutomorphisms
variable {d : Hypothesis D (ZMod 2) 1 g h} (a : PointAlignment d)

/-- The raw aligned star map on the literal embedded residual. -/
def rawProjection : D.L₁ →* SL(3, ZMod 2) :=
  a.projection.comp (inclusion (show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left))

theorem rawProjection_range : (rawProjection a).range = pointA := by
  rw [rawProjection, MonoidHom.range_comp, inclusion_range, a.residual_image]
  exact point_residual

/-- A surjection onto the actual affine A₄ matrix subgroup. -/
def localProjection : D.L₁ →* pointA :=
  (rawProjection a).codRestrict pointA (fun x => rawProjection_range a ▸
    (show rawProjection a x ∈ (rawProjection a).range from ⟨x, rfl⟩))

theorem localProjection_surjective : Function.Surjective (localProjection a) := by
  intro y
  have hy : (y : SL(3, ZMod 2)) ∈ (rawProjection a).range :=
    (rawProjection_range a).symm ▸ y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem localProjection_kernel_twoGroup : IsPGroup 2 (localProjection a).ker := by
  rw [localProjection, MonoidHom.ker_codRestrict, rawProjection, ← MonoidHom.comap_ker]
  exact a.projection_kernel_twoGroup.comap_of_injective _ (inclusion_injective _)

/-- The local two-core is the full preimage of the marked translation core. -/
theorem local_core_preimage :
    (pCore 2 pointA).comap (localProjection a) = pCore 2 D.L₁ :=
  (localProjection a).comap_pCore_of_ker_isPGroup
    (localProjection_surjective a) (localProjection_kernel_twoGroup a)

/-- The actual local quotient, not a group family label. -/
noncomputable def coreQuotientEquiv :
    (D.L₁ ⧸ pCore 2 D.L₁) ≃* (pointA ⧸ pCore 2 pointA) :=
  (localProjection a).pCoreQuotientEquiv
    (localProjection_surjective a) (localProjection_kernel_twoGroup a)

include a in
theorem coreQuotient_card : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 := by
  rw [Nat.card_congr (coreQuotientEquiv a).toEquiv]
  exact card_point_core_quotient

include a in
/-- Every two-group section of the terminal quotient is trivial. Hence it
has no two-chief factor, without invoking a chief-series convention. -/
theorem terminal_two_section_trivial
    (A B : Subgroup (D.L₁ ⧸ pCore 2 D.L₁)) [(A.subgroupOf B).Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) := by
  have h3 : IsPGroup 3 (D.L₁ ⧸ pCore 2 D.L₁) :=
    IsPGroup.of_card (n := 1) (by simpa using coreQuotient_card a)
  have hq3 : IsPGroup 3 (B ⧸ A.subgroupOf B) :=
    (h3.to_subgroup B).of_surjective _ (QuotientGroup.mk'_surjective _)
  apply subsingleton_of_forall_eq 1
  intro x
  obtain ⟨i, hi⟩ := hp.exists_orderOf_dvd_pow x
  obtain ⟨j, hj⟩ := hq3.exists_orderOf_dvd_pow x
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow i j) hi hj

end Binary

/-- The terminal quotient is cubic on the literal binary source data. -/
theorem binary_coreQuotient_card (d : Hypothesis D (ZMod 2) 1 g h) :
    Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 := by
  obtain ⟨a⟩ := exists_pointAlignment d
  exact Binary.coreQuotient_card a

/-- No nontrivial two-chief interval occurs above the binary local two-core. -/
theorem binary_terminal_two_section_trivial (d : Hypothesis D (ZMod 2) 1 g h)
    (A B : Subgroup (D.L₁ ⧸ pCore 2 D.L₁)) [(A.subgroupOf B).Normal]
    (hp : IsPGroup 2 (B ⧸ A.subgroupOf B)) :
    Subsingleton (B ⧸ A.subgroupOf B) := by
  obtain ⟨a⟩ := exists_pointAlignment d
  exact Binary.terminal_two_section_trivial a A B hp
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
