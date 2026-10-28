module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness

/-!
# The terminal action obstruction in the graph-field cover case

The normalizer, its embedded two-residual Y, and N_T(E)Y below are the
actual subgroups in source 16.4.9(2). A quaternion quotient Q/E inside an
actual GL₂(3) quotient forces Q to be relatively normal. But a normal
subgroup fixing z fixes its whole orbit, contradicting Q's transvection
r ↦ rz when that orbit contains r.

The transitivity and GL₂(3) quotient are explicit inputs to these terminal
lemmas. Their construction remains part of the cover argument; the model
contracts alone do not supply them. In particular no involution-swapping
conjugator is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1191.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G]

/-- The simultaneous normalizer N_G(E) ∩ N_G(C_T(E)). -/
def coverNormalizer (T : Sylow 2 G) (r z : G) : Subgroup G :=
  normalizer (fourGroup r z : Set G) ⊓
    normalizer ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G) : Set G)

/-- The embedded two-residual of the simultaneous normalizer. -/
def coverY (T : Sylow 2 G) (r z : G) : Subgroup G :=
  (pResidual 2 (coverNormalizer T r z)).map (coverNormalizer T r z).subtype

/-- The actual product N_T(E)Y, expressed as a generated subgroup. -/
def coverOvergroup (T : Sylow 2 G) (r z : G) : Subgroup G :=
  ((T : Subgroup G) ⊓ normalizer (fourGroup r z : Set G)) ⊔ coverY T r z

theorem coverY_le_normalizer (T : Sylow 2 G) (r z : G) :
    coverY T r z ≤ normalizer (fourGroup r z : Set G) :=
  (map_subtype_le _).trans inf_le_left

theorem coverOvergroup_le_normalizer (T : Sylow 2 G) (r z : G) :
    coverOvergroup T r z ≤ normalizer (fourGroup r z : Set G) :=
  sup_le inf_le_right (coverY_le_normalizer T r z)

instance normal_fourGroup_in_coverOvergroup (T : Sylow 2 G) (r z : G) :
    ((fourGroup r z).subgroupOf (coverOvergroup T r z)).Normal :=
  normal_subgroupOf_of_le_normalizer (coverOvergroup_le_normalizer T r z)

/-- Transitivity of the actual embedded Y on E minus its identity. -/
def CoverTransitive (T : Sylow 2 G) (r z : G) : Prop :=
  ∀ u ∈ fourGroup r z, u ≠ 1 → ∀ v ∈ fourGroup r z, v ≠ 1 →
    ∃ y ∈ coverY T r z, MulAut.conj y u = v

/-- The exact matrix quotient required in the second action alternative. -/
def CoverGeneralLinear (T : Sylow 2 G) (r z : G) : Prop :=
  Nonempty (((coverOvergroup T r z) ⧸
    (fourGroup r z).subgroupOf (coverOvergroup T r z)) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem cover_not_normal {L : Subgroup G} {r z : G}
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hz : z ≠ 1) {M : Subgroup G} (hQM : d.Q ≤ M)
    (hmoves : ∃ y ∈ M, MulAut.conj y z = r) : ¬ (d.Q.subgroupOf M).Normal := by
  intro hn
  have hMN : M ≤ normalizer (d.Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQM).mp hn
  obtain ⟨y, hy, hyr⟩ := hmoves
  obtain ⟨t, ht, htr⟩ := c.transvection
  have hk : y⁻¹ * t * y ∈ d.Q := by
    have hny : y⁻¹ ∈ normalizer (d.Q : Set G) :=
      (normalizer (d.Q : Set G)).inv_mem (hMN hy)
    simpa only [inv_inv] using (mem_normalizer_iff.mp hny t).mp ht
  have hfix : MulAut.conj (y⁻¹ * t * y) z = z := by
    have hh := mem_centralizer_singleton_iff.mp (c.fixes_z hk)
    change (y⁻¹ * t * y) * z * (y⁻¹ * t * y)⁻¹ = z
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  have hfixr : MulAut.conj t r = r := by
    rw [← hyr]
    have hh := congrArg (MulAut.conj y) hfix
    change y * ((y⁻¹ * t * y) * z * (y⁻¹ * t * y)⁻¹) * y⁻¹ = y * z * y⁻¹ at hh
    change t * (y * z * y⁻¹) * t⁻¹ = y * z * y⁻¹
    convert hh using 1; group
  apply hz
  have he : r * z = r * 1 := by simpa only [mul_one] using htr.symm.trans hfixr
  exact mul_left_cancel he

variable [Finite G]

theorem cover_not_normal_of_transitive {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hQ : d.Q ≤ coverOvergroup T r z) (htrans : CoverTransitive T r z) :
    ¬ (d.Q.subgroupOf (coverOvergroup T r z)).Normal := by
  have hz : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hr : r ≠ 1 := by intro he; simp [he] at hr2
  apply cover_not_normal d c hz hQ
  obtain ⟨y, hy, he⟩ := htrans z (mem_sup_right (mem_zpowers z)) hz
    r (mem_sup_left (mem_zpowers r)) hr
  exact ⟨y, mem_sup_right hy, he⟩


omit [Finite G] in
theorem cover_normal_of_generalLinear {T : Sylow 2 G} {r z : G} {L : Subgroup G}
    (d : NormalizerData L r z) (hQ : d.Q ≤ coverOvergroup T r z)
    (hGL : CoverGeneralLinear T r z) :
    (d.Q.subgroupOf (coverOvergroup T r z)).Normal := by
  let M := coverOvergroup T r z
  let E := fourGroup r z
  let A := d.Q.subgroupOf M
  let F := E.subgroupOf M
  let _ : (E.subgroupOf d.Q).Normal :=
    normal_subgroupOf_of_le_normalizer d.normalizes_four
  let b : A ≃* d.Q := subgroupOfEquivOfLe hQ
  have hb : (F.subgroupOf A).map b.toMonoidHom = E.subgroupOf d.Q := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      change (x : G) ∈ E
      have hyE : ((y : A) : G) ∈ E := hy
      have heval := congrArg (fun q : d.Q => (q : G)) he
      exact heval ▸ hyE
    · intro hx
      refine ⟨b.symm x, ?_, b.apply_symm_apply x⟩
      exact hx
  let a := QuotientGroup.congr (F.subgroupOf A) (E.subgroupOf d.Q) b hb
  obtain ⟨eQ⟩ := d.quaternion
  obtain ⟨eM⟩ := hGL
  exact Matrix.GeneralLinearGroup.normal_of_three_quotient F A
    (fun _ hx => d.four_le hx) eM ⟨a.trans eQ⟩

theorem cover_no_generalLinear {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hr2 : orderOf r = 2)
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hQ : d.Q ≤ coverOvergroup T r z) (htrans : CoverTransitive T r z) :
    ¬ CoverGeneralLinear T r z := by
  intro hGL
  exact cover_not_normal_of_transitive h hr2 d c hQ htrans
    (cover_normal_of_generalLinear d hQ hGL)

end CFSG.Quasithin.Chapter16.Intersections.GraphField
