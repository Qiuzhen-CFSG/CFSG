module
public import CFSG.Quasithin.Chapter12.Section08.Actions
public import CFSG.Quasithin.Chapter12.Section08.Preliminary

/-!
# Comparing the literal tilded and central quotients

The image of U in G₁/V₁ is canonically U/V₁. Since V₁ lies in Z(U),
the map to U/Z(U) factors through that image. The resulting surjection
is equivariant for the actual H-conjugation actions.

Source: Aschbacher–Smith, Lemma 12.8.8(2), printed pp.851–852. This is
only the comparison of carriers and actions; the commutator forms are
separate constructions.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable [IsMulCommutative V]

instance point_normal_U (F : InvariantFlag T V n) :
    ((F.Vi 1).subgroupOf F.U).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))).mpr F.U_le_H

theorem tildeMap_U_ker (F : InvariantFlag T V n) :
    (F.tildeMap F.U F.U_le_H).ker = (F.Vi 1).subgroupOf F.U := by
  ext a
  rw [MonoidHom.mem_ker]
  change F.tildeMap F.U F.U_le_H a = 1 ↔ _
  rw [Subtype.ext_iff]
  change F.tildeProjection ⟨a, F.U_le_H a.property⟩ = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

/-- The image in G₁/V₁ is the literal quotient of U by V₁. -/
noncomputable def utildeEquiv (F : InvariantFlag T V n) :
    F.U ⧸ (F.Vi 1).subgroupOf F.U ≃* F.tilde F.U :=
  (QuotientGroup.quotientMulEquivOfEq F.tildeMap_U_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (F.tildeMap F.U F.U_le_H)
      (F.tildeMap_surjective F.U F.U_le_H))

@[simp] theorem utildeEquiv_apply_mk (F : InvariantFlag T V n) (a : F.U) :
    F.utildeEquiv (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) a) =
      F.tildeMap F.U F.U_le_H a := by
  rfl

theorem point_subgroupOf_U_le_center (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    (F.Vi 1).subgroupOf F.U ≤ center F.U := by
  intro a ha
  obtain ⟨b, hb, he⟩ := F.point_le_ZU hn ha
  have he' : b = a := Subtype.ext he
  exact he' ▸ hb

/-- The canonical surjection from Ũ to Û. -/
noncomputable def tildeToUhat (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    F.tilde F.U →* F.Uhat :=
  (QuotientGroup.lift ((F.Vi 1).subgroupOf F.U)
    (QuotientGroup.mk' (center F.U)) (by
      rw [QuotientGroup.ker_mk']
      exact F.point_subgroupOf_U_le_center hn)).comp F.utildeEquiv.symm.toMonoidHom

@[simp] theorem tildeToUhat_apply_map (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (a : F.U) :
    F.tildeToUhat hn (F.tildeMap F.U F.U_le_H a) =
      QuotientGroup.mk' (center F.U) a := by
  rw [← F.utildeEquiv_apply_mk a]
  change (QuotientGroup.lift ((F.Vi 1).subgroupOf F.U) (QuotientGroup.mk' (center F.U))
    (by rw [QuotientGroup.ker_mk']; exact F.point_subgroupOf_U_le_center hn))
    (F.utildeEquiv.symm (F.utildeEquiv (QuotientGroup.mk' _ a))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem tildeToUhat_surjective (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    Function.Surjective (F.tildeToUhat hn) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) q
  exact ⟨F.tildeMap F.U F.U_le_H a, F.tildeToUhat_apply_map hn a⟩

/-- The projection retains the literal H-actions on both quotient carriers. -/
theorem tildeToUhat_equivariant (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (h : F.H) (a : F.tilde F.U) :
    F.tildeToUhat hn (F.localTildeAction F.H le_rfl h a) =
      F.uhatAction h (F.tildeToUhat hn a) := by
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H a
  rw [tildeToUhat_apply_map, uhatAction_apply_mk]
  have hnorm : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have he := F.tildeAction_apply_map F.H F.U le_rfl F.U_le_H hnorm h u
  exact (congrArg (F.tildeToUhat hn) he).trans
    (F.tildeToUhat_apply_map hn (F.uAction h u))

omit [IsMulCommutative V] in
/-- Membership in a tilded subgroup containing the point lifts exactly. -/
theorem mem_tilde_iff_of_point_le (F : InvariantFlag T V n)
    (A : Subgroup G) (hpoint : F.Vi 1 ≤ A) (a : F.H) :
    F.tildeProjection a ∈ F.tilde A ↔ (a : G) ∈ A := by
  change a ∈ ((A.subgroupOf F.H).map F.tildeProjection).comap F.tildeProjection ↔ _
  rw [comap_map_eq]
  have hker : F.tildeProjection.ker ≤ A.subgroupOf F.H := by
    intro b hb
    have hm : b ∈ (F.Vi 1).subgroupOf F.H := (QuotientGroup.eq_one_iff b).mp hb
    exact hpoint hm
  rw [sup_eq_left.mpr hker]
  rfl

/-- The denominator of Ũ → Û is precisely the image of Z(U). -/
theorem tildeToUhat_ker (F : InvariantFlag T V n) (hn : 1 ≤ n) :
    (F.tildeToUhat hn).ker = (F.tilde F.ZU).subgroupOf (F.tilde F.U) := by
  ext a
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H a
  rw [MonoidHom.mem_ker, tildeToUhat_apply_map]
  have hu : (QuotientGroup.mk' (center F.U)) u = 1 ↔ u ∈ center F.U :=
    QuotientGroup.eq_one_iff u
  rw [hu]
  change u ∈ center F.U ↔ F.tildeProjection ⟨u, F.U_le_H u.property⟩ ∈ F.tilde F.ZU
  rw [F.mem_tilde_iff_of_point_le F.ZU (F.point_le_ZU hn)]
  constructor
  · intro hu
    exact mem_map.mpr ⟨u, hu, rfl⟩
  · rintro ⟨v, hv, he⟩
    have he' : v = u := Subtype.ext he
    exact he' ▸ hv

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
