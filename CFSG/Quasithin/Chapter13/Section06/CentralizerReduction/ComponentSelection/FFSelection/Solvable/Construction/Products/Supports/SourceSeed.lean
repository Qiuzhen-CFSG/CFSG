module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports.FixedKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Normality
public import Theory.GroupTheory.Commutator.SylowFixedSeed

/-!
# The Sylow-central source seed removes the singleton fixed kernel

The native product records alone allow central shears. In the actual
13.6.13 setup, z is fixed by T_v and generates U_v under G_v. A normal
star subgroup and its two-residual therefore move exactly the same
subgroup of U_v: the Sylow supplement fixes the seed, and normality
propagates this through its conjugate span. The already proved residual
planes consequently give order four for each selected whole S₃ factor.

All subgroups and maps below are the original star action. No fixed-kernel
disjointness, moved-space order, or product decomposition is assumed.
Source: Aschbacher--Smith, combined manuscript, 13.6.13, printed p.929,
with the Sylow-central marking preceding 13.6.9 on p.928.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

/-- On the actual seed span, every normal star actor has the same moved
subgroup as its embedded two-residual. -/
theorem movedSubgroup_eq_residual_of_sylow_seed
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    (H : Subgroup (Gstar z v)) [H.Normal] :
    movedSubgroup z v H = movedSubgroup z v ((pResidual 2 H).map H.subtype) := by
  let R := (pResidual 2 H).map H.subtype
  let A := H.comap (starMk z v)
  let B := R.comap (starMk z v)
  have hAB : A ≤ B ⊔ (S : Subgroup (Gv v)) := by
    obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal A
    have he := congrArg (fun Q : Subgroup A => Q.map A.subtype)
      (pResidual_sup_sylow_eq_top P)
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
      hP, subgroupOf_map_subtype] at he
    rw [← he]
    apply sup_le (le_sup_of_le_left ?_) (inf_le_left.trans le_sup_right)
    apply map_le_iff_le_comap.mp
    rw [map_embedded_pResidual]
    have ha : A.map (starMk z v) = H :=
      map_comap_eq_self_of_surjective (starMk_surjective z v) H
    rw [ha]
  have hsup : starPreimage z v H ≤ starPreimage z v R ⊔ Tv T v := by
    have hm := map_mono (f := (Gv v).subtype) hAB
    rw [Subgroup.map_sup, hS] at hm
    exact hm
  have hZfix : zpowers z ≤ centralizer (Tv T v : Set G) := by
    apply zpowers_le.mpr
    apply mem_centralizer_iff.mpr
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hfix ht)
  exact commutator_conjugateSpan_eq_of_fixed_supplement
    (zpowers z) (Gv v) (starPreimage z v H) (starPreimage z v R) (Tv T v)
    (zpowers_le.mpr hz) (starPreimage_le_Gv z v R) inf_le_right
    (starPreimage_normalized z v H) (starPreimage_normalized z v R)
    (map_mono (comap_mono (map_subtype_le _))) hsup hZfix

/-- The first selected native S₃ factor moves a plane on the original U_v.
Its ambient normality and the Sylow-fixed seed discharge the former support
premise, including for an exceptional complementary factor. -/
theorem minimalSolvable_twoFactor_first_moved_card
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      (pResidual 2 c.first).map c.first.subtype) :
    Nat.card (movedSubgroup z v
      (c.first.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) = 4 := by
  let I := FFFactors.offenderActor (starRepresentation z v)
  let H := c.first.map I.subtype
  let : H.Normal := minimalSolvable_twoFactor_first_normal L T z v hz S hS hfix hX c e hF
  rw [movedSubgroup_eq_residual_of_sylow_seed T z v hz S hS hfix H,
    ← map_embedded_pResidual]
  exact twoFactor_residual_moved_card z v c c.first (Or.inl rfl) e

/-- The second selected factor satisfies the same conclusion, without a
condition on its complementary source factor. -/
theorem minimalSolvable_twoFactor_second_moved_card
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      (pResidual 2 c.second).map c.second.subtype) :
    Nat.card (movedSubgroup z v
      (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) = 4 := by
  let I := FFFactors.offenderActor (starRepresentation z v)
  let H := c.second.map I.subtype
  let : H.Normal := minimalSolvable_twoFactor_second_normal L T z v hz S hS hfix hX c e hF
  rw [movedSubgroup_eq_residual_of_sylow_seed T z v hz S hS hfix H,
    ← map_embedded_pResidual]
  exact twoFactor_residual_moved_card z v c c.second (Or.inr rfl) e

/-- The original hyperplane branch also moves exactly its cubic plane. -/
theorem minimalSolvable_hyperplane_moved_card
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v))) :
    Nat.card (movedSubgroup z v
      (c.second.map (FFFactors.offenderActor (starRepresentation z v)).subtype)) = 4 := by
  obtain ⟨⟨e⟩, hF⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  let I := FFFactors.offenderActor (starRepresentation z v)
  let H := c.second.map I.subtype
  let : H.Normal := minimalSolvable_hyperplane_second_normal L T z v hz S hS hfix hX c e hF
  rw [movedSubgroup_eq_residual_of_sylow_seed T z v hz S hS hfix H,
    ← map_embedded_pResidual]
  exact hyperplane_residual_moved_card z v c e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
