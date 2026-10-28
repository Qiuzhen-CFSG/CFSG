module

public import Theory.SpecificGroups.Monster.Construction.CInvariance

/-!
# The source local groups inside the fixed Griess automorphism group

The proved gamma and beta invariance give an injective map from the actual
spin–Leech tensor image into the parameter-free `GriessGroup`. Multiplication
preservation follows from the nondegenerate-form duality of Section 28.
Composing the existing local quotient and extraspecial embeddings preserves
the exact kernel `K` on `N₁` and gives the literal source quotient embeddings.

The image of `z₁` is a nonidentity involution with signs `(-,+,+)` on the
three original summands. Its fixed space and the containment of the local
subgroup in its centralizer are proved in this carrier. The reverse centralizer
containment and the full `N/K` action remain separate source obligations.

Source: Aschbacher, *Sporadic Groups*, Lemmas 27.5–27.9 and 28.12–28.13,
printed pp. 147–154; the centralizer consumer is in Section 31.
-/

@[expose] public section
noncomputable section

namespace Sporadic.Monster.Construction
open LocalC TrialitySpin CInvariance

/-- The faithful orthogonal local representation, bundled as linear equivalences. -/
def cLinearAction : C →* (GriessSpace ≃ₗ[ℝ] GriessSpace) where
  toFun g :=
    { toLinearMap := cRepresentation g
      invFun := cRepresentation g⁻¹
      left_inv v := by
        change (cRepresentation g⁻¹ * cRepresentation g) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv v := by
        change (cRepresentation g * cRepresentation g⁻¹) v = v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact map_one cRepresentation
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    exact map_mul cRepresentation g h

@[simp] theorem cLinearAction_apply (g : C) (v : GriessSpace) :
    cLinearAction g v = cRepresentation g v := rfl

/-- Section 28.13 puts the actual local group inside the fixed Griess group. -/
def cToGriess : C →* GriessGroup where
  toFun g := ⟨cLinearAction g,
    ⟨cRepresentation_form g, cRepresentation_beta g⟩⟩
  map_one' := Subtype.ext (map_one cLinearAction)
  map_mul' g h := Subtype.ext (map_mul cLinearAction g h)

@[simp] theorem cToGriess_apply (g : C) (v : GriessSpace) :
    (cToGriess g).val v = cRepresentation g v := rfl

theorem cToGriess_faithful : Function.Injective cToGriess := by
  intro g h he
  apply cRepresentation_faithful
  exact congrArg (fun f : GriessGroup => f.val.toLinearMap) he

/-- Multiplication preservation follows from the proved two-form invariance. -/
theorem cToGriess_product (g : C) (x y : GriessSpace) :
    griessProduct ((cToGriess g).val x) ((cToGriess g).val y) =
      (cToGriess g).val (griessProduct x y) :=
  ((mem_griessFormStabilizer_iff_product _).mp (cToGriess g).prop).2 x y

/-- The concrete subgroup denoted `C` inside the Griess automorphism group. -/
def localSubgroup : Subgroup GriessGroup := cToGriess.range

/-- The local subgroup retains its original tensor-image carrier. -/
def cEquivLocalSubgroup : C ≃* localSubgroup :=
  MonoidHom.ofInjective cToGriess_faithful

/-- The original `N₁` action in the Griess group, prior to quotienting. -/
def n1ToGriess : N1 →* GriessGroup := cToGriess.comp n1ToC

@[simp] theorem n1ToGriess_apply (g : N1) (v : GriessSpace) :
    (n1ToGriess g).val v = cRepresentation (n1ToC g) v := rfl

/-- Its exact kernel is the given four-group, relative to `N₁`. -/
theorem n1ToGriess_kernel : n1ToGriess.ker = K.subgroupOf N1 := by
  rw [← n1ToC_kernel]
  ext g
  change cToGriess (n1ToC g) = 1 ↔ n1ToC g = 1
  rw [← map_one cToGriess, cToGriess_faithful.eq_iff]

/-- The literal source quotient embeds without an additional kernel premise. -/
def n1QuotientToGriess : N1Quotient →* GriessGroup := cToGriess.comp n1QuotientToC

theorem n1QuotientToGriess_faithful : Function.Injective n1QuotientToGriess :=
  cToGriess_faithful.comp n1QuotientToC_faithful

@[simp] theorem n1QuotientToGriess_mk (g : N1) :
    n1QuotientToGriess (QuotientGroup.mk' (K.subgroupOf N1) g) = n1ToGriess g := rfl

/-- The actual extraspecial subgroup of `N/K`, embedded through the local action. -/
def q1ToGriess : Q1Image →* GriessGroup := cToGriess.comp q1ToC

theorem q1ToGriess_faithful : Function.Injective q1ToGriess :=
  cToGriess_faithful.comp q1ToC_faithful

theorem q1ToGriess_image (q : Q1) :
    q1ToGriess (q1ImageMap q) = n1ToGriess (SpinAction.q1Inclusion q) :=
  congrArg cToGriess (q1ToC_image q)

/-- The short action uses literal conjugation in the constructed Griess group. -/
theorem q1ToGriess_conjugation (g : C) (q : Q1Image) :
    q1ToGriess (cConjugation g q) = cToGriess g * q1ToGriess q * (cToGriess g)⁻¹ := by
  change cToGriess (q1ToC (cConjugation g q)) = _
  rw [q1ToC_conjugation, map_mul, map_mul, map_inv]
  rfl

end Sporadic.Monster.Construction

namespace Sporadic.Monster
open Construction Construction.LocalC Construction.TrialitySpin

/-- The concrete involution of the Griess group used in the centralizer theorem. -/
def griessZ : GriessGroup := cToGriess z1C

/-- Its actual action has signs `(-,+,+)` on `B₋ ⊥ Bᵣ ⊥ Bₛ`. -/
theorem griessZ_apply (v : GriessSpace) : griessZ.val v = (-v.1, v.2.1, v.2.2) :=
  cRepresentation_z1C v

theorem griessZ_square : griessZ ^ 2 = 1 := by
  rw [griessZ, ← map_pow, z1C_square, map_one]

theorem griessZ_ne_one : griessZ ≠ 1 := by
  intro h
  apply z1C_ne_one
  apply cToGriess_faithful
  exact h.trans (map_one cToGriess).symm

theorem griessZ_fixed_iff (v : GriessSpace) : griessZ.val v = v ↔ v.1 = 0 :=
  cRepresentation_z1C_fixed_iff v

/-- The embedded extraspecial center is precisely the distinguished involution. -/
theorem q1ToGriess_center : q1ToGriess q1ImageCenterGenerator = griessZ :=
  congrArg cToGriess q1ToC_center

theorem griessZ_commutes_local (g : C) : griessZ * cToGriess g = cToGriess g * griessZ := by
  change cToGriess z1C * cToGriess g = cToGriess g * cToGriess z1C
  rw [← map_mul, ← map_mul, z1C_central]

/-- The easy centralizer containment, now in the fixed automorphism group.
The reverse containment is the separate Section 31 centralizer theorem. -/
theorem localSubgroup_le_centralizer_griessZ :
    localSubgroup ≤ Subgroup.centralizer ({griessZ} : Set GriessGroup) := by
  rintro g ⟨c, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain rfl := Set.mem_singleton_iff.mp hz
  exact griessZ_commutes_local c

end Sporadic.Monster
