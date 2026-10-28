module
public import Theory.SpecificGroups.SL3.PerfectCentralCover

/-!
# The full two-core of a perfect special-linear extension

For a perfect group H with H/O₂(H) marked as SL₃(F), quotienting by
[O₂(H),H] gives a perfect central cover of that same full SL₃. Its kernel
is precisely the image of O₂(H), a central two-group. Outside field sizes
two and four, the ordinary scalar-cover theorem bounds the cover's order
by that of SL₃, so the kernel vanishes and [O₂(H),H]=O₂(H).

The quotient and marking are literal. No abelianity of O₂(H) or action
on a selected module is assumed. The nonbinary MS application identifies
its original commutator core with the intrinsic two-core, while retaining
the exceptional field-four kernel as a separate obligation.
Source: Aschbacher--Smith I.1.3, printed p.407, and C.1.34, pp.136--137.
The scalar-cover input is the proved Steinberg presentation in
Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SL3.PerfectCore
variable {H F : Type*} [Group H] [Finite H] [Group.IsPerfect H]
  [Field F] [Finite F]
local notation "D" => (⁅pCore 2 H, (⊤ : Subgroup H)⁆ : Subgroup H)

/-- The intrinsic core-commutator quotient covers the full marked SL₃. -/
def cover (e : (H ⧸ pCore 2 H) ≃* SL(3,F)) :
    PerfectCentralCovering.Cover (H ⧸ D) SL(3,F) where
  toMonoidHom := QuotientGroup.lift D (e.toMonoidHom.comp (QuotientGroup.mk' _)) (by
    intro x hx
    change e (QuotientGroup.mk' (pCore 2 H) x) = 1
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff x).mpr (commutator_le_left _ _ hx))
  surjective := QuotientGroup.lift_surjective_of_surjective _ _
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) _
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective D x
    have hxN : x ∈ pCore 2 H := by
      change e (QuotientGroup.mk' (pCore 2 H) x) = 1 at hx
      exact (QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp hx)
    have hc : (pCore 2 H).map (QuotientGroup.mk' D) ≤ center (H ⧸ D) := by
      apply commutator_top_right_eq_bot_iff_le_center.mp
      rw [← map_top_of_surjective (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D),
        ← map_commutator, QuotientGroup.map_mk'_self]
    exact hc (mem_map_of_mem _ hxN)

omit [Finite H] [Finite F] in
@[simp] theorem cover_apply (e : (H ⧸ pCore 2 H) ≃* SL(3,F)) (x : H) :
    (cover e).toMonoidHom (QuotientGroup.mk' D x) = e (QuotientGroup.mk' _ x) := by
  unfold cover
  rfl

omit [Finite H] [Finite F] in
/-- The covering kernel is the image of the original two-core. -/
theorem cover_kernel (e : (H ⧸ pCore 2 H) ≃* SL(3,F)) :
    (cover e).toMonoidHom.ker = (pCore 2 H).map (QuotientGroup.mk' D) := by
  ext x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective D x
  constructor
  · intro hx
    have he : e (QuotientGroup.mk' (pCore 2 H) x) = 1 := by
      simpa only [MonoidHom.mem_ker,cover_apply] using hx
    exact mem_map_of_mem _ ((QuotientGroup.eq_one_iff x).mp (e.map_eq_one_iff.mp he))
  · rintro ⟨y,hy,he⟩
    rw [←he]
    change (cover e).toMonoidHom (QuotientGroup.mk' D y) = 1
    rw [cover_apply]
    exact e.map_eq_one_iff.mpr ((QuotientGroup.eq_one_iff y).mpr hy)

omit [Finite H] [Finite F] in
/-- The remaining central covering kernel is a two-group at every field size. -/
theorem cover_kernel_isPGroup (e : (H ⧸ pCore 2 H) ≃* SL(3,F)) :
    IsPGroup 2 (cover e).toMonoidHom.ker := by
  rw [cover_kernel]
  exact pCore_isPGroup.map _

omit [Finite H] [Finite F] in
/-- The common cover is faithful exactly when the intrinsic commutator is
already the whole two-core. -/
theorem cover_injective_iff (e : (H ⧸ pCore 2 H) ≃* SL(3,F)) :
    Function.Injective (cover e).toMonoidHom ↔ D = pCore 2 H := by
  rw [←MonoidHom.ker_eq_bot_iff,cover_kernel,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  exact ⟨fun he => le_antisymm (commutator_le_left _ _) he,fun he => he.ge⟩

/-- Outside the two exceptional field sizes the whole two-core is generated
by commutators with the perfect group. -/
theorem commutator_eq_core (e : (H ⧸ pCore 2 H) ≃* SL(3,F))
    (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4) : D = pCore 2 H := by
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let c := cover e
  obtain ⟨f,hf,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift h2 h4
    c.quotientCenterEquiv
  have hi := (c.surjective.bijective_of_nat_card_le (Nat.card_le_card_of_surjective f hf)).1
  apply le_antisymm (commutator_le_left _ _)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change e (QuotientGroup.mk' (pCore 2 H) x) = c.toMonoidHom 1
  rw [map_one]
  exact e.map_eq_one_iff.mpr ((QuotientGroup.eq_one_iff x).mpr hx)

end Matrix.SL3.PerfectCore
