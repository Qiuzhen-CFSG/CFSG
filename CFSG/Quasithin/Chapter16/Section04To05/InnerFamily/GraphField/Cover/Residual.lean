module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Frattini
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The residual intersection in the cover normalizer

`coverComponentIntersection` is the actual intersection of all conjugates of
L under the normalizer of E. Its embedded two-residual is characteristic in
that intersection, and the conjugation calculation makes it normal relative
to N_G(E). Transitivity and the single compatible mark place the intersection in
C_L(r). Once normalization of Lᵣ is proved, residual monotonicity and
two-perfectness prove the equality with the embedded residual. The
normalization premise remains a separate obligation of the cover argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1191.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G]

def coverComponentIntersection (L : Subgroup G) (r z : G) : Subgroup G :=
  ⨅ y : normalizer (fourGroup r z : Set G), L.conjBy (y : G)

theorem coverComponentIntersection_le (L : Subgroup G) (r z : G) :
    coverComponentIntersection L r z ≤ L := by
  change (⨅ y : normalizer (fourGroup r z : Set G), L.conjBy (y : G)) ≤ L
  have h := iInf_le (fun y : normalizer (fourGroup r z : Set G) => L.conjBy (y : G)) 1
  simpa only [OneMemClass.coe_one, conjBy_one] using h

theorem normalizer_le_coverComponentIntersection_normalizer (L : Subgroup G) (r z : G) :
    normalizer (fourGroup r z : Set G) ≤
      normalizer (coverComponentIntersection L r z : Set G) := by
  intro y hy
  apply mem_normalizer_iff_map_conj_eq.mpr
  let N := normalizer (fourGroup r z : Set G)
  have map_conj (a b : G) :
      (L.conjBy a).map (MulAut.conj b).toMonoidHom = L.conjBy (b * a) := by
    change (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom = _
    rw [map_map]
    congr 1
    ext x
    simp [MulAut.mul_def]
  change (⨅ x : N, L.conjBy (x : G)).map (MulAut.conj y).toMonoidHom =
    ⨅ x : N, L.conjBy (x : G)
  rw [Subgroup.map_iInf (MulAut.conj y).toMonoidHom (MulAut.conj y).injective]
  apply le_antisymm
  · apply le_iInf
    intro x
    let xy : N := ⟨y⁻¹ * (x : G), N.mul_mem (N.inv_mem hy) x.property⟩
    have hle := iInf_le (fun a : N =>
      (L.conjBy (a : G)).map (MulAut.conj y).toMonoidHom) xy
    rw [map_conj] at hle
    simpa [xy, mul_assoc] using hle
  · apply le_iInf
    intro x
    let xy : N := ⟨y * (x : G), N.mul_mem hy x.property⟩
    have hle := iInf_le (fun a : N => L.conjBy (a : G)) xy
    rw [map_conj]
    simpa [xy, mul_assoc] using hle

theorem residual_normal_of_coverComponentIntersection
    {z r : G} {L : Subgroup G} (heq : residual L r = (pResidual 2 (coverComponentIntersection L r z)).map
      (coverComponentIntersection L r z).subtype) :
    ((residual L r).subgroupOf (normalizer (fourGroup r z : Set G))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [heq]
  exact (normalizer_le_coverComponentIntersection_normalizer L r z).trans
    (normalizer_le_normalizer_characteristic_image _ _)



variable [Finite G] {T : Sylow 2 G} {z r g : G} {L R : Subgroup G}

/-- Any element taking z to r transports L to the already chosen L′.
Only the single mark from Geometry is used. -/
theorem component_conjugate_eq_of_same_mark
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hg : MulAut.conj g z = r) {y : G} (hy : MulAut.conj y z = r) :
    L.conjBy y = L.conjBy g := by
  have hfix : MulAut.conj (y * g⁻¹) r = r := by
    rw [← hg]
    have he : MulAut.conj (y * g⁻¹) (MulAut.conj g z) = MulAut.conj y z := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [he, hy, hg]
  have hc : y * g⁻¹ ∈ centralizer ({r} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    change (y * g⁻¹) * r * (y * g⁻¹)⁻¹ = r at hfix
    exact (mul_inv_eq_iff_eq_mul).mp hfix
  have hn := actor_centralizer_le_conjugate_normalizer h hr hr2 hc
  have he := mem_normalizer_iff_map_conj_eq.mp hn
  change (L.conjBy g).conjBy (y * g⁻¹) = L.conjBy g at he
  simpa only [conjBy_conjBy, inv_mul_cancel_right] using he

/-- Transitivity identifies a member of the normalizer orbit with L′,
so the whole intersection lies in the actual C_L(r). -/
theorem coverComponentIntersection_le_fixed
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hg : MulAut.conj g z = r) (htrans : CoverTransitive T r z) :
    coverComponentIntersection L r z ≤ L ⊓ centralizer ({r} : Set G) := by
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hr1 : r ≠ 1 := by intro he; simp [he] at hr2
  obtain ⟨y, hy, he⟩ := htrans z (mem_sup_right (mem_zpowers z)) hz1
    r (mem_sup_left (mem_zpowers r)) hr1
  have hLy := component_conjugate_eq_of_same_mark h hr hr2 hg he
  have hWJ : coverComponentIntersection L r z ≤ L.conjBy g := by
    rw [← hLy]
    exact iInf_le (fun y : normalizer (fourGroup r z : Set G) => L.conjBy (y : G))
      ⟨y, coverY_le_normalizer T r z hy⟩
  have hrJ : r ∈ centralizer (L.conjBy g : Set G) := by
    have he : (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) :=
      map_centralizer_equiv _ (MulAut.conj g)
    exact he ▸ (h.sylow.le hr).1
  exact le_inf (coverComponentIntersection_le L r z) (hWJ.trans (by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hrJ l hl)))

omit [Finite G] in
/-- A normalized residual lies in every conjugate in the actual intersection. -/
theorem residual_le_coverComponentIntersection
    (hn : normalizer (fourGroup r z : Set G) ≤ normalizer (residual L r : Set G)) :
    residual L r ≤ coverComponentIntersection L r z := by
  apply le_iInf
  intro y
  have he : (residual L r).conjBy (y : G) = residual L r :=
    mem_normalizer_iff_map_conj_eq.mp (hn y.property)
  rw [← he]
  exact map_mono ((residual_le_centralizer L r).trans inf_le_left)

/-- Given normalization, the equality is a residual sandwich, not an input
identifying an abstract residual with an embedded subgroup. -/
theorem residual_eq_coverComponentIntersection_of_normalizes
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hg : MulAut.conj g z = r) (htrans : CoverTransitive T r z)
    (hn : normalizer (fourGroup r z : Set G) ≤ normalizer (residual L r : Set G)) :
    residual L r = (pResidual 2 (coverComponentIntersection L r z)).map
      (coverComponentIntersection L r z).subtype := by
  let W := coverComponentIntersection L r z
  have hDW : residual L r ≤ W := residual_le_coverComponentIntersection hn
  have hp : IsPPerfect 2 (residual L r) :=
    isPPerfect_embedded_pResidual 2 (L ⊓ centralizer ({r} : Set G))
  have hpW : IsPPerfect 2 ((residual L r).subgroupOf W) :=
    hp.of_surjective (subgroupOfEquivOfLe hDW).symm.toMonoidHom
      (subgroupOfEquivOfLe hDW).symm.surjective
  apply le_antisymm
  · have hh := map_mono (f := W.subtype)
      (le_pResidual_of_isPPerfect ((residual L r).subgroupOf W) hpW)
    rwa [map_subgroupOf_eq_of_le hDW] at hh
  · exact embedded_pResidual_mono 2 (coverComponentIntersection_le_fixed h hr hr2 hg htrans)

end CFSG.Quasithin.Chapter16.Intersections.GraphField
