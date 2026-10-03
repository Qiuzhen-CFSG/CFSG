module
public import Theory.GroupTheory.Signalizer.Subgroup

/-!
# Restricting a signalizer family to an invariant subgroup

An odd solvable signalizer family restricts to any invariant subgroup H by
intersecting its values with H. The family on H uses the literal restriction
of the supplied ambient action. Its constructor has a private body; public
equations identify its values and the ambient image of its generated subgroup.

For U≤H, being a signalizer subgroup of the restricted family is equivalent
to being an ambient signalizer subgroup of the original family. The proof
uses the canonical isomorphism U.subgroupOf H≃U for order and solvability,
and transports invariance and fixed-point bounds element by element. A native
subgroup version transfers along the inclusion H→G.

The generated subgroup maps to the supremum of the actual intersections of
the values with H. This image lies in the original generated subgroup, so
completeness restricts by downward closure. No elementary, rank, finiteness,
or completeness hypothesis enters the family construction or the subgroup
correspondence. No equality with the intersection of the original generated
subgroup and H is asserted without an additional generation argument.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, §11.1, printed
p.305, `refs/latex/kurzweil.tex`. These transfers provide the subgroup interface
for later local-completeness arguments.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

private theorem solvable_subgroupOf (U H : Subgroup G) [Group.IsSolvable U] :
    Group.IsSolvable (U.subgroupOf H) := by
  apply Group.isSolvable_of_isSolvable_injective (f := H.subtype.subgroupComap U)
  intro x y h
  have hval : x.val.val = y.val.val := congrArg (fun z : U => (z : G)) h
  exact Subtype.ext (Subtype.ext hval)

public def restrict (θ : TwoSignalizerFamily A G) (H : Subgroup G)
    [IsInvariant A G H] : TwoSignalizerFamily A H where
  subgroup a := (θ.subgroup a).subgroupOf H
  odd a := (θ.odd a).of_dvd_nat (Subgroup.card_comap_dvd_of_injective
    (θ.subgroup a) H.subtype H.subtype_injective)
  solvable a := by
    let _ := θ.solvable a
    exact solvable_subgroupOf (θ.subgroup a) H
  invariant a := by
    let _ := θ.invariant a
    exact isInvariant_subgroupOf (θ.subgroup a) H
  le_fixed a := by
    intro x hx b
    exact Subtype.ext (θ.le_fixed a hx b)
  balance a b := by
    intro x hx
    exact θ.balance a b ⟨hx.1, fun c => congrArg Subtype.val (hx.2 c)⟩

@[simp] public theorem restrict_subgroup (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] (a : {a : A // a ≠ 1}) :
    (θ.restrict H).subgroup a = (θ.subgroup a).subgroupOf H := by rfl

public theorem restrict_subgroup_map (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] (a : {a : A // a ≠ 1}) :
    ((θ.restrict H).subgroup a).map H.subtype = θ.subgroup a ⊓ H := by
  rw [restrict_subgroup, Subgroup.subgroupOf_map_subtype]

public theorem restrict_closure_map (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] :
    (θ.restrict H).closure.map H.subtype = ⨆ a, θ.subgroup a ⊓ H := by
  simp only [closure, Subgroup.map_iSup, restrict_subgroup_map]

public theorem restrict_closure_map_le (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] :
    (θ.restrict H).closure.map H.subtype ≤ θ.closure ⊓ H := by
  rw [restrict_closure_map]
  exact iSup_le fun a => inf_le_inf (θ.le_closure a) le_rfl

public theorem isSignalizerSubgroup_subgroupOf_iff (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] (U : Subgroup G) (hUH : U ≤ H) :
    (θ.restrict H).IsSignalizerSubgroup (U.subgroupOf H) ↔ θ.IsSignalizerSubgroup U := by
  let e := Subgroup.subgroupOfEquivOfLe hUH
  have hcard : Nat.card (U.subgroupOf H) = Nat.card U := Nat.card_congr e.toEquiv
  constructor
  · intro hU
    let _ := hU.2.1
    have hInv : IsInvariant A G U := by
      let _ := hU.2.2.1
      have h := isInvariant_map_subtype (A := A) H (U.subgroupOf H)
      rwa [Subgroup.map_subgroupOf_eq_of_le hUH] at h
    refine ⟨hcard ▸ hU.1, Group.isSolvable_of_surjective (f := e.toMonoidHom)
      e.surjective, hInv, ?_⟩
    intro a x hx
    have hnative := hU.2.2.2 a
      (show (⟨x, hUH hx.1⟩ : H) ∈ U.subgroupOf H ⊓
        FixedPoints.subgroup (Subgroup.zpowers a.val) H from
        ⟨hx.1, fun b => Subtype.ext (hx.2 b)⟩)
    rw [restrict_subgroup] at hnative
    exact hnative
  · intro hU
    let _ := hU.2.1
    let _ := hU.2.2.1
    refine ⟨hcard.symm ▸ hU.1, solvable_subgroupOf U H,
      isInvariant_subgroupOf U H, ?_⟩
    intro a x hx
    rw [restrict_subgroup]
    exact hU.2.2.2 a ⟨hx.1, fun b => congrArg Subtype.val (hx.2 b)⟩

public theorem isSignalizerSubgroup_map_subtype_iff (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] (U : Subgroup H) :
    θ.IsSignalizerSubgroup (U.map H.subtype) ↔ (θ.restrict H).IsSignalizerSubgroup U := by
  have hsub : (U.map H.subtype).subgroupOf H = U := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← θ.isSignalizerSubgroup_subgroupOf_iff H (U.map H.subtype)
    (Subgroup.map_subtype_le U), hsub]

public theorem isComplete_restrict_iff (θ : TwoSignalizerFamily A G)
    (H : Subgroup G) [IsInvariant A G H] :
    (θ.restrict H).IsComplete ↔
      θ.IsSignalizerSubgroup ((θ.restrict H).closure.map H.subtype) := by
  exact (θ.isSignalizerSubgroup_map_subtype_iff H (θ.restrict H).closure).symm

public theorem IsComplete.restrict {θ : TwoSignalizerFamily A G} (hθ : θ.IsComplete)
    (H : Subgroup G) [IsInvariant A G H] : (θ.restrict H).IsComplete := by
  apply (θ.isComplete_restrict_iff H).mpr
  let _ := (θ.restrict H).closure_invariant
  exact hθ.mono ((θ.restrict_closure_map_le H).trans inf_le_left)
    (isInvariant_map_subtype H (θ.restrict H).closure)

end Theory.GroupTheory.TwoSignalizerFamily
