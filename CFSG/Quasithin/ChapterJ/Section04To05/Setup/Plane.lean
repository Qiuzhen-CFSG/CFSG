module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure
public import Theory.GroupTheory.PGroup.NormalFour

/-!
# The original Sylow-invariant plane for the Ru subgroup construction

The source natural eight-group is normal in the original Sylow two-group.
A normal four-group inside it supplies V₂. A nontrivial normal subgroup of
a two-group meets its center; since that center has order two, the plane
contains the original Z(T). All subgroups and the ambient Sylow are retained.
This gives the actual flag needed to define the second parabolic in J.4.

Source: Aschbacher–Smith,opening notation of J.4,printed p.440.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G]

/-- A four-group in the original natural module, invariant under the chosen Sylow. -/
structure Plane (d : LocalSetup G) where
  group : Subgroup G
  le_seed : group ≤ d.V
  card : Nat.card group = 4
  normalized : (d.T : Subgroup G) ≤ normalizer (group : Set G)
  point_le : d.toTypeRuSetup.Z ≤ group

/-- Construct the source plane from Ru1/Ru2 and the compatible Sylow choice. -/
theorem exists_plane (d : LocalSetup G) : Nonempty (Plane d) := by
  have hVT : d.V ≤ (d.T : Subgroup G) := d.ru1.V_le_S.trans d.S_le_T
  let N := d.V.subgroupOf (d.T : Subgroup G)
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (d.T_le_L.trans d.ru1.natural.normalized)
  have hsquare := d.ru1.natural.square_eq_one_of_trivial_kernel rfl
  let : IsElementaryAbelian 2 d.V := {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hsquare z)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.subgroupOf hVT
  have hNcard : Nat.card N = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv).trans d.ru1.card_V
  obtain ⟨A,hAN,hANseed,hAe,hAcard⟩ :=
    d.T.isPGroup'.exists_normal_four_of_normal_elementary N (by rw [hNcard]; decide)
  let : A.Normal := hAN
  let : Fact (IsPGroup 2 d.T) := ⟨d.T.isPGroup'⟩
  have hAn : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAcard]; decide)
  obtain ⟨Z,hZn,hZA,hZcard,hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) A hAn
  have hcenter : Nat.card (center d.T) = 2 := by
    have hh := d.card_Z
    change Nat.card ((center d.T).map (d.T : Subgroup G).subtype) = 2 at hh
    rwa [Subgroup.card_subtype] at hh
  have hZeq : Z = center d.T := eq_of_le_of_card_ge hZcenter (by rw [hcenter,hZcard])
  let V₂ := A.map (d.T : Subgroup G).subtype
  refine ⟨{
    group := V₂
    le_seed := ?_
    card := ?_
    normalized := ?_
    point_le := ?_ }⟩
  · rintro v ⟨a,ha,rfl⟩
    exact hANseed ha
  · exact (Subgroup.card_subtype (d.T : Subgroup G) A).trans hAcard
  · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le A)).mp
      (show (V₂.subgroupOf (d.T : Subgroup G)).Normal from by
        change (A.map (d.T : Subgroup G).subtype).comap (d.T : Subgroup G).subtype |>.Normal
        rw [comap_map_eq_self_of_injective (d.T : Subgroup G).subtype_injective]
        infer_instance)
  · change (center d.T).map (d.T : Subgroup G).subtype ≤ V₂
    rw [← hZeq]
    exact map_mono hZA

/-- A group satisfying the original Ru hypotheses has the source J.4 flag. -/
theorem source_plane (h : IsTypeRu G) :
    ∃ d : LocalSetup G, Nonempty (Plane d) := by
  obtain ⟨d⟩ := h.nonempty_localSetup
  exact ⟨d,exists_plane d⟩

/-- The actual second parabolic, before taking its two-residual. -/
def Plane.parabolic {d : LocalSetup G} (p : Plane d) : Subgroup G :=
  d.L ⊓ normalizer (p.group : Set G)

/-- Membership in the original intersection defining the second parabolic. -/
theorem Plane.mem_parabolic {d : LocalSetup G} (p : Plane d) (x : G) :
    x ∈ p.parabolic ↔ x ∈ d.L ∧ x ∈ normalizer (p.group : Set G) := Iff.rfl

/-- The original Sylow lies in the second parabolic. -/
theorem Plane.sylow_le_parabolic {d : LocalSetup G} (p : Plane d) :
    (d.T : Subgroup G) ≤ p.parabolic := le_inf d.T_le_L p.normalized

end CFSG.Quasithin.ChapterJ.RuSubgroup
