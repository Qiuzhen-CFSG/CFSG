module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Geometry
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The central-factor transvection in Lemma 16.4.6

The strict normalizer condition in the two-group T_C⟨r⟩ supplies an
actual conjugator of ⟨r,z⟩ outside that four-group. Removing its r-factor
places it in T_C. The centralizer identity forces its action r ↦ rz;
it fixes z and v and normalizes T_E and Ω₁(T_E). The marked-eight
obstruction then gives T_C = ⟨z⟩.

Source: Aschbacher–Smith, Lemma 16.4.6, printed pp.1185–1186.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
open Subgroup
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem mem_two {a x : G} (ha : orderOf a = 2) :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, hn'⟩
    interval_cases n <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

private theorem join_cases {A : Subgroup G} {a x : G}
    (hn : a ∈ normalizer (A : Set G)) (ha : orderOf a = 2)
    (hx : x ∈ A ⊔ zpowers a) : x ∈ A ∨ ∃ b ∈ A, x = b * a := by
  have hx' : x ∈ (A : Set G) * (zpowers a : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A (zpowers a) (zpowers_le.mpr hn)]
    exact hx
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  rcases (mem_two ha).mp hc with rfl | rfl
  · exact Or.inl (by simpa using hb)
  · exact Or.inr ⟨b, hb, rfl⟩

namespace Configuration
variable {T : Sylow 2 G} {L R : Subgroup G} {g r z v u s t : G}
variable (h : Configuration T L R g r z v u s t)
include h

theorem r_mem_sylow : r ∈ T := (omegaOneAmbient_le _ h.eight.r_mem).1

theorem v_mem_inner : v ∈ innerSylow T L := by
  refine ⟨(omegaOneAmbient_le _ h.eight.v_mem).1, ?_⟩
  have hh : v ∈ omegaOneAmbient (pairCentralizer T r z) ⊓ L := by
    rw [h.inner_intersection]
    exact mem_zpowers v
  exact hh.2

theorem u_mem_sylow : u ∈ T := (omegaOneAmbient_le _ h.eight.u_mem).1

theorem z_mem_central : z ∈ centralizingSylow T L := by
  refine ⟨h.source.mem_sylow, ?_⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mp (h.source.component.1 hx)

theorem sylow_normalizes_inner :
    (T : Subgroup G) ≤ normalizer (innerSylow T L : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer h.source.sylow_normalizes).trans
    inf_normalizer_le_normalizer_inf

theorem sylow_normalizes_central :
    (T : Subgroup G) ≤ normalizer (centralizingSylow T L : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    (h.source.sylow_normalizes.trans (normalizer_le_normalizer_centralizer L))).trans
    inf_normalizer_le_normalizer_inf

theorem sylow_fixes_z {a : G} (ha : a ∈ T) : MulAut.conj a z = z := by
  have hc := mem_centralizer_singleton_iff.mp (h.source.sylow_centralizes ha)
  change a * z * a⁻¹ = z
  rw [hc, mul_inv_cancel_right]

theorem central_fixes_v {a : G} (ha : a ∈ centralizingSylow T L) :
    MulAut.conj a v = v := by
  change a * v * a⁻¹ = v
  rw [← ha.2 v h.v_mem_inner.2, mul_inv_cancel_right]

private theorem r_ne_z : r ≠ z := by
  intro he
  have hh : r * v = r := by
    rw [← h.eight.t_r, he, h.eight.t_z]
  have hv1 : v = 1 := mul_left_cancel (hh.trans (mul_one r).symm)
  simpa [hv1] using h.eight.v_order

private theorem r_not_mem_central : r ∉ centralizingSylow T L := by
  intro hr
  have hh : MulAut.conj t r = r := by
    change t * r * t⁻¹ = r
    rw [hr.2 t h.t_inner.2, mul_inv_cancel_right]
  rw [h.eight.t_r] at hh
  have hv1 : v = 1 := mul_left_cancel (hh.trans (mul_one r).symm)
  simpa [hv1] using h.eight.v_order

private theorem pair_mem_cases {x : G} (hx : x ∈ zpowers r ⊔ zpowers z) :
    x = 1 ∨ x = z ∨ x = r ∨ x = r * z := by
  have hn : z ∈ normalizer (zpowers r : Set G) := by
    apply centralizer_le_normalizer
    have hc : zpowers r ≤ centralizer ({z} : Set G) :=
      zpowers_le.mpr (h.source.sylow_centralizes h.r_mem_sylow)
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hc ha)
  rcases join_cases hn h.eight.z_order hx with hh | ⟨a, ha, rfl⟩
  · rcases (mem_two h.eight.r_order).mp hh with rfl | rfl <;> simp
  · rcases (mem_two h.eight.r_order).mp ha with rfl | rfl <;> simp

/-- Strict growth of the local central factor constructs the extra transvection,
including normalization of the actual centralizer and its first omega. -/
theorem exists_extra_transvection (hlt : zpowers z < centralizingSylow T L) :
    ∃ a ∈ centralizingSylow T L,
      a ∈ normalizer (pairCentralizer T r z : Set G) ∧
      a ∈ normalizer (omegaOneAmbient (pairCentralizer T r z) : Set G) ∧
      MulAut.conj a r = r * z ∧ MulAut.conj a z = z ∧ MulAut.conj a v = v := by
  let C := centralizingSylow T L
  let E := zpowers r ⊔ zpowers z
  let Q := C ⊔ zpowers r
  have hEQ : E ≤ Q := sup_le le_sup_right
    ((zpowers_le.mpr h.z_mem_central).trans le_sup_left)
  have hQT : Q ≤ (T : Subgroup G) := sup_le inf_le_left (zpowers_le.mpr h.r_mem_sylow)
  have hCE : ¬ C ≤ E := by
    intro hh
    apply not_le_of_gt hlt
    intro x hx
    rcases h.pair_mem_cases (hh hx) with he | he | he | he
    · exact he ▸ (zpowers z).one_mem
    · exact he ▸ mem_zpowers z
    · exact False.elim (h.r_not_mem_central (he ▸ hx))
    · have hrC := C.mul_mem hx (C.inv_mem h.z_mem_central)
      rw [he, mul_inv_cancel_right] at hrC
      exact False.elim (h.r_not_mem_central hrC)
  have hproper : E.subgroupOf Q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hQE := subgroupOf_eq_top.mp he
    exact hCE (le_sup_left.trans hQE)
  let : Group.IsNilpotent Q := (T.isPGroup'.to_le hQT).isNilpotent
  obtain ⟨b, hb, hbE⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (E.subgroupOf Q) hproper)
  have hbN : (b : G) ∈ normalizer (E : Set G) := by
    rw [← subgroupOf_normalizer_eq hEQ] at hb
    exact hb
  have hrN : r ∈ normalizer (E : Set G) := E.le_normalizer (mem_sup_left (mem_zpowers r))
  have ha : ∃ a ∈ C, a ∈ normalizer (E : Set G) ∧ a ∉ E := by
    rcases join_cases (h.sylow_normalizes_central h.r_mem_sylow)
        h.eight.r_order b.property with hc | ⟨c, hc, he⟩
    · exact ⟨b, hc, hbN, hbE⟩
    · refine ⟨c, hc, ?_, ?_⟩
      · have hh := (normalizer (E : Set G)).mul_mem hbN
          ((normalizer (E : Set G)).inv_mem hrN)
        rwa [he, mul_inv_cancel_right] at hh
      · intro hcE
        apply hbE
        change (b : G) ∈ E
        rw [he]
        exact E.mul_mem hcE (mem_sup_left (mem_zpowers r))
  obtain ⟨a, haC, haE, haout⟩ := ha
  have haz := h.sylow_fixes_z haC.1
  have har : MulAut.conj a r = r * z := by
    have hmem : MulAut.conj a r ∈ E :=
      (mem_normalizer_iff.mp haE r).mp (mem_sup_left (mem_zpowers r))
    rcases h.pair_mem_cases hmem with he | he | he | he
    · have hr1 := (MulAut.conj a).injective (he.trans (map_one _).symm)
      simpa [hr1] using h.eight.r_order
    · exact False.elim (h.r_ne_z ((MulAut.conj a).injective (he.trans haz.symm)))
    · have hcentral : a ∈ C ⊓ involutionCentralizer r := by
        refine ⟨haC, mem_centralizer_singleton_iff.mpr ?_⟩
        change a * r * a⁻¹ = r at he
        exact mul_inv_eq_iff_eq_mul.mp he
      rw [h.centralizer_in_central_factor] at hcentral
      exact False.elim (haout (mem_sup_right hcentral))
    · exact he
  have haTE : a ∈ normalizer (pairCentralizer T r z : Set G) :=
    inf_normalizer_le_normalizer_inf
      ⟨(T : Subgroup G).le_normalizer haC.1,
        normalizer_le_normalizer_centralizer E haE⟩
  let : (omega₁ (pairCentralizer T r z) (p := 2)).Characteristic :=
    omega₁_characteristic _
  exact ⟨a, haC, haTE,
    normalizer_le_normalizer_characteristic_image _ _ haTE,
    har, haz, h.central_fixes_v haC⟩

/-- The marked geometry rules out strict growth of the central factor. -/
theorem central_eq_zpowers : centralizingSylow T L = zpowers z := by
  apply le_antisymm _ (zpowers_le.mpr h.z_mem_central)
  by_contra hle
  have hlt := lt_of_le_not_ge (zpowers_le.mpr h.z_mem_central) hle
  obtain ⟨a, _, _, _, har, haz, hav⟩ := h.exists_extra_transvection hlt
  exact h.eight.no_extra_transvection a har haz hav

end Configuration
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
