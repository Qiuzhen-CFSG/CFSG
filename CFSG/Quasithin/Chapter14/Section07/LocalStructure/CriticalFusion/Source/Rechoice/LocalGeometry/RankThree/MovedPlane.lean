module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers

/-!
# The moved-plane normalization in 14.7.70

This file isolates the two normalization steps in the rank-three paragraph.
The first is the literal earlier-65 fixed-space calculation: `R₁` fixes the
original point and normalizes the selected opposite point, hence it normalizes
`E = V₁ Zα`.  The second is the marked-cover calculation.  Its source output
is that an element of `H` preserving the selected rank-two displacement plane
centralizes its involution image.  The existing natural quotient then puts it
in the actual Sylow `T` through `Data.plane_centralizer_le`.

For a moved `E`, `Elementary.lean` identifies the moved span with the literal
`Fcomm`.  The restricted pairing producer supplies the full action of the six
literal transvections on that span.  We retain that action as an output
contract, together with its cubic in the `z`-centralizer, and prove the source
contradiction from the actual relative normalizer bound.  The cubic is an
element of the action group; no lift of order three in `G` is assumed.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, proof of
14.7.70, printed pp.1073–1074 (PDF pp.1090–1091), especially the paragraph
beginning “As R₁* centralizes Ũ₀Ṽ”.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree

open Subgroup Representation Chapter12.Section08

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace MovedPlane

variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The two literal inputs from the earlier-65 fixed-space action.  The first
clause is the action on the original point; the second is the selected-point
normalization from the same source calculation. -/
structure Earlier65 (c : CriticalPath (L := L) F) : Prop where
  fixed_point : F.Ri L 1 ≤ centralizer (F.Vi 1 : Set G)
  normalizes_opposite : F.Ri L 1 ≤ normalizer (c.Zα : Set G)

include d c
omit [Finite G] [AddCommGroup W] [Module (ZMod 2) W] d in
theorem r₁_normalizes_E (h65 : Earlier65 c) :
    F.Ri L 1 ≤ normalizer (E c : Set G) := by
  exact (le_inf (h65.fixed_point.trans (Subgroup.centralizer_le_normalizer _))
      h65.normalizes_opposite).trans
    (Subgroup.normalizer_inf_normalizer_le_normalizer_sup (F.Vi 1) c.Zα)

/-- The marked-cover calculation needed for the relative normalizer.  The
statement is deliberately phrased on the actual `H` and actual commutator;
it does not assume the desired normalizer inclusion.  In the source proof the
field is discharged by preservation of the three marked displacement planes
`(t²y,ty,0)`, followed by the original `qH` map. -/
structure MarkedPlaneControl (h : Preliminary d c) : Prop where
  separation : d.ModuleSeparation
  preserve_selected_plane : ∀ x : F.H,
    (x : G) ∈ normalizer (Fcomm c : Set G) →
      (x : G) ∈ centralizer (F.Vi 2 : Set G)

include d c
theorem marked_normalizer_le_T (h : Preliminary d c)
    (control : MarkedPlaneControl d c h) :
    F.H ⊓ normalizer (Fcomm c : Set G) ≤ (T : Subgroup G) := by
  intro x hx
  let xH : F.H := ⟨x, hx.1⟩
  exact d.plane_centralizer_le control.separation (control.preserve_selected_plane xH hx.2)

omit [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W] d c in
theorem no_cubic_of_two_group {A B : Type*} [Group A] [Group B] [Finite A]
    (hA : IsPGroup 2 A) (ρ : A →* B)
    (hcubic : ∃ a : A, orderOf (ρ a) = 3) : False := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := hcubic
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) a
  have hd : 3 ∣ 2 ^ k := by
    have hdiv := orderOf_map_dvd ρ a
    rw [ha, hk] at hdiv
    exact hdiv
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hd
  norm_num at h32

/-- The output contract of the restricted pairing calculation on a moved
plane.  `axes` records the two literal axis realizations from `CoreAxes`; the
`full` field is the result of transporting the reciprocal axis by `t` and
checking the six elementary transvections on the literal `Fcomm`. -/
structure ThreeAxisAction (h : Preliminary d c) (t : G) where
  axes : CoreAxes c
  carrier : Subgroup G
  action : carrier →* MulAut (Fcomm c)
  carrier_normalizes : carrier ≤ normalizer (Fcomm c : Set G)
  centralizer_to_H : ∀ a : carrier,
    (a : G) ∈ centralizer ({d.z} : Set G) → (a : G) ∈ F.H
  full : Function.Surjective action
  cubic : ∃ a : carrier,
    orderOf (action a) = 3 ∧ (a : G) ∈ centralizer ({d.z} : Set G)

include d c
theorem moved_plane_contradiction (h : Preliminary d c)
    (control : MarkedPlaneControl d c h) (t : G)
    (ht : t ∈ (T : Subgroup G)) (hm : t ∉ normalizer (E c : Set G))
    (action : ThreeAxisAction d c h t) : False := by
  have hmoved : movedSpan c t = Fcomm c := h.moved_span_eq_commutator t ht hm
  let C : Subgroup action.carrier :=
    (centralizer ({d.z} : Set G)).comap action.carrier.subtype
  have hCT : IsPGroup 2 C := by
    let f : C →* T :=
      { toFun := fun x =>
          ⟨(x : G), marked_normalizer_le_T d c h control
            ⟨action.centralizer_to_H x x.property,
              action.carrier_normalizes x.1.property⟩⟩
        map_one' := by rfl
        map_mul' := by intro x y; rfl }
    apply T.isPGroup'.of_injective f
    intro x y hxy
    have hG : (x : G) = (y : G) := congrArg (fun q : T => (q : G)) hxy
    exact Subtype.ext (Subtype.ext hG)
  obtain ⟨a, ha, hza⟩ := action.cubic
  let aC : C := ⟨a, hza⟩
  apply no_cubic_of_two_group hCT (action.action.comp C.subtype)
  refine ⟨aC, ?_⟩
  exact ha

include d c
theorem T_normalizes_E (h : Preliminary d c)
    (control : MarkedPlaneControl d c h)
    (full_three_axis : ∀ (t : G), t ∈ (T : Subgroup G) →
      t ∉ normalizer (E c : Set G) → ThreeAxisAction d c h t) :
    (T : Subgroup G) ≤ normalizer (E c : Set G) := by
  intro t ht
  by_contra hm
  exact moved_plane_contradiction d c h control t ht hm (full_three_axis t ht hm)

end MovedPlane

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
