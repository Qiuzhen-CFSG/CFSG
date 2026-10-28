module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.FaithfulAction
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.GroupTheory.Amalgam.RankTwo
public import Theory.GroupAction.ExtendingSubgroupAutomorphisms

/-!
# The finite marked amalgam for the binary automorphism theorem

The two parabolics of the actual derived group have order 96 and intersect
in the Sylow two-subgroup of order 32. Their inclusion amalgam retains both
commuting squares. Restriction to these generating parabolics is faithful,
and the full Borel of order 64 embeds into the automorphisms of this amalgam.

Every automorphism of the derived group can be composed with one inner
automorphism to preserve the Sylow subgroup. The intrinsic root-normalizer
calculation then makes it preserve both parabolics with their original
labels. Consequently an upper bound of 64 for the finite amalgam's actual
automorphisms will suffice for the global automorphism identification.
This module constructs the local objects and actions; it does not assert
that remaining upper bound.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, Definition F.4.3,
printed p.274, and the invariant-parabolic argument of 2.3.9(7), printed
p.526. Root coordinates and restricted parabolics come from the licensed
ATLAS port and its checked extensions, cited in the imports.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.LieParabolicSetup Theory.GroupTheory
open scoped Pointwise
namespace Atlas.G2.LieAutomorphismExtensions

/-- The restricted parabolic normalizing the highest-root subgroup. -/
abbrev BinaryLeft := binaryMarkedParabolic 0
/-- The restricted parabolic normalizing the two-long-root subgroup. -/
abbrev BinaryRight := binaryMarkedParabolic 1

/-- The whole intersection of the two restricted parabolics. -/
def binaryOverlap : Subgroup BinaryDerived := BinaryLeft ⊓ BinaryRight

/-- The actual inclusion amalgam of the binary derived parabolics. -/
def binaryAmalgam : RankTwoAmalgam BinaryLeft binaryOverlap BinaryRight :=
  .ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Compatible automorphisms of all three groups of the inclusion amalgam. -/
abbrev BinaryAmalgamAut := RankTwoAmalgam.Iso binaryAmalgam binaryAmalgam

theorem binaryAmalgamAut_ext (a b : BinaryAmalgamAut)
    (hL : a.left = b.left) (hM : a.middle = b.middle) (hR : a.right = b.right) : a = b := by
  rcases a with ⟨⟨aL, aM, aR⟩, haL, haR⟩
  rcases b with ⟨⟨bL, bM, bR⟩, hbL, hbR⟩
  cases hL
  cases hM
  cases hR
  rfl

instance : Finite BinaryAmalgamAut := by
  let : Finite (MulAut BinaryLeft) := Finite.of_injective
    (fun a : MulAut BinaryLeft => (a : BinaryLeft → BinaryLeft)) DFunLike.coe_injective
  let : Finite (MulAut binaryOverlap) := Finite.of_injective
    (fun a : MulAut binaryOverlap => (a : binaryOverlap → binaryOverlap)) DFunLike.coe_injective
  let : Finite (MulAut BinaryRight) := Finite.of_injective
    (fun a : MulAut BinaryRight => (a : BinaryRight → BinaryRight)) DFunLike.coe_injective
  exact Finite.of_injective (fun a : BinaryAmalgamAut => (a.left, a.middle, a.right))
    (fun a b h => binaryAmalgamAut_ext a b (congrArg Prod.fst h)
      (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h))

theorem binaryMarkedParabolic_sup : BinaryLeft ⊔ BinaryRight = ⊤ := by
  apply Subgroup.map_injective BinaryDerived.subtype_injective
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  change (parabolic₁.subgroupOf BinaryDerived).map BinaryDerived.subtype ⊔
    (parabolic₂.subgroupOf BinaryDerived).map BinaryDerived.subtype = BinaryDerived
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
  exact DerivedParabolicGeneration.binary_restricted_pair_generate

/-- The two restricted parabolics determine any automorphism of the derived group. -/
theorem binaryAut_ext (a b : MulAut BinaryDerived)
    (hL : ∀ x : BinaryLeft, a x.val = b x.val)
    (hR : ∀ x : BinaryRight, a x.val = b x.val) : a = b := by
  have h : BinaryLeft ⊔ BinaryRight ≤ a.toMonoidHom.eqLocus b.toMonoidHom :=
    sup_le (fun x hx => hL ⟨x,hx⟩) (fun x hx => hR ⟨x,hx⟩)
  rw [binaryMarkedParabolic_sup] at h
  exact MulEquiv.ext (fun x => h (Subgroup.mem_top x))

abbrev BinaryPairStabilizer := Subgroup.automorphismPairStabilizer BinaryLeft BinaryRight

def binaryAmalgamRestriction (a : BinaryPairStabilizer) : BinaryAmalgamAut where
  left := (a.val.subgroupMap BinaryLeft).trans (MulEquiv.subgroupCongr a.property.1)
  right := (a.val.subgroupMap BinaryRight).trans (MulEquiv.subgroupCongr a.property.2)
  middle := (a.val.subgroupMap binaryOverlap).trans (MulEquiv.subgroupCongr (by
    change (BinaryLeft ⊓ BinaryRight).map a.val.toMonoidHom = BinaryLeft ⊓ BinaryRight
    rw [Subgroup.map_inf _ _ _ a.val.injective]
    exact congrArg₂ (· ⊓ ·) a.property.1 a.property.2))
  left_commutes _ := rfl
  right_commutes _ := rfl

theorem binaryAmalgamRestriction_injective : Function.Injective binaryAmalgamRestriction := by
  intro a b h
  apply Subtype.ext
  apply binaryAut_ext
  · intro x
    exact congrArg (fun e : BinaryAmalgamAut => (e.left x).val) h
  · intro x
    exact congrArg (fun e : BinaryAmalgamAut => (e.right x).val) h

def binaryBorelPairAction (b : borel (K := ZMod 2)) : BinaryPairStabilizer :=
  ⟨binaryConjugation b.val, binaryConjugation_borel_fixes b 0,
    binaryConjugation_borel_fixes b 1⟩

/-- The full Borel acts on the literal marked amalgam by conjugation. -/
def binaryBorelAmalgamAction (b : borel (K := ZMod 2)) : BinaryAmalgamAut :=
  binaryAmalgamRestriction (binaryBorelPairAction b)

theorem binaryOverlap_eq : binaryOverlap = unipotent.subgroupOf BinaryDerived := by
  change (parabolic₁ ⊓ parabolic₂).subgroupOf BinaryDerived = _
  rw [binary_overlap, borel_binary]

theorem card_binaryBorel : Nat.card (borel (K := ZMod 2)) = 64 := by
  rw [borel_binary]
  exact BinaryParabolicPair.card_unipotent_binary

theorem card_binaryLeft : Nat.card BinaryLeft = 96 := by
  change Nat.card (parabolic₁.subgroupOf BinaryDerived) = _
  rw [parabolic₁_binary]
  exact BinaryParabolicPair.card_derivedFirst

theorem card_binaryRight : Nat.card BinaryRight = 96 :=
  BinaryParabolicPair.card_derivedSecond

theorem card_binaryOverlap : Nat.card binaryOverlap = 32 := by
  rw [binaryOverlap_eq, ← BinaryParabolicPair.derivedSylow_eq]
  exact BinaryParabolicPair.card_derivedSylow

@[simp] theorem binaryBorelAmalgamAction_left_apply
    (b : borel (K := ZMod 2)) (x : BinaryLeft) :
    ((binaryBorelAmalgamAction b).left x).val.val = b.val * x.val.val * b.val⁻¹ := rfl

@[simp] theorem binaryBorelAmalgamAction_middle_apply
    (b : borel (K := ZMod 2)) (x : binaryOverlap) :
    ((binaryBorelAmalgamAction b).middle x).val.val = b.val * x.val.val * b.val⁻¹ := rfl

@[simp] theorem binaryBorelAmalgamAction_right_apply
    (b : borel (K := ZMod 2)) (x : BinaryRight) :
    ((binaryBorelAmalgamAction b).right x).val.val = b.val * x.val.val * b.val⁻¹ := rfl

/-- The order-64 full Borel acts faithfully on the derived amalgam. -/
theorem binaryBorelAmalgamAction_injective : Function.Injective binaryBorelAmalgamAction := by
  intro b c h
  apply Subtype.ext
  apply binaryConjugation_injective
  exact congrArg Subtype.val (binaryAmalgamRestriction_injective h)

/-- One inner correction preserves both marked parabolics of the actual derived group. -/
theorem binaryAut_normalize_marked_pair (a : MulAut BinaryDerived) :
    ∃ h : BinaryDerived, ∀ i : Fin 2,
      (binaryMarkedParabolic i).map (MulAut.conj h * a).toMonoidHom =
        binaryMarkedParabolic i := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq BinaryDerived
    (a • BinaryParabolicPair.derivedSylow) BinaryParabolicPair.derivedSylow
  have hs : (unipotent.subgroupOf BinaryDerived).map
      (MulAut.conj h * a).toMonoidHom = unipotent.subgroupOf BinaryDerived := by
    have hh' := congrArg (fun S : Sylow 2 BinaryDerived => (S : Subgroup BinaryDerived)) hh
    change ((BinaryParabolicPair.derivedSylow : Subgroup BinaryDerived).map
      a.toMonoidHom).map (MulAut.conj h).toMonoidHom = _ at hh'
    rw [Subgroup.map_map, BinaryParabolicPair.derivedSylow_eq] at hh'
    exact hh'
  obtain ⟨h₁, h₂⟩ := SylowParabolicInvariance.restricted_parabolics_invariant _ hs
  refine ⟨h, fun i => ?_⟩
  fin_cases i
  · exact h₁
  · exact h₂

end Atlas.G2.LieAutomorphismExtensions
