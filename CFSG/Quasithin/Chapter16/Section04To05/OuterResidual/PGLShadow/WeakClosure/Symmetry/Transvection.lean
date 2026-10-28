module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Configuration

/-!
# The marked reflection and its exact transvection data

If an element fixes A pointwise and sends an involution w to wc, with
nonidentity c in A and central in A⟨w⟩, its fixed subgroup on A⟨w⟩ is
exactly A and its commutator subgroup is exactly ⟨c⟩. The proof decomposes
elements into A and its w-coset, then controls commutators of every power
of the actor. The actor itself need not have order two.

Apply this to the actual reflection supplied by `CentralizerGeometry` to
construct t with both fixed generators, its exact axis, and its commutator
center. The same calculation will apply to the opposite reflection.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1185. All conjugations are left conjugations.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
variable {G : Type*} [Group G]

private theorem conjugation_fixed_iff (a x : G) :
    MulAut.conj a x = x ↔ x ∈ involutionCentralizer a := by
  change a * x * a⁻¹ = x ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  rw [involutionCentralizer, mem_centralizer_singleton_iff]
  exact eq_comm

private theorem commutator_cyclic_le {V C : Subgroup G} {t : G}
    (ht : t ∈ normalizer (C : Set G))
    (hgen : ∀ x ∈ V, ⁅t, x⁆ ∈ C) : ⁅zpowers t, V⁆ ≤ C := by
  apply commutator_le.mpr
  intro a ha x hx
  rw [zpowers_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
      have : a = t := Set.mem_singleton_iff.mp ha
      subst a
      exact hgen x hx
  | one => simp
  | mul a b ha hb iha ihb =>
      rw [commutatorElement_mul_left_eq_conj_mul]
      apply C.mul_mem _ iha
      exact (mem_normalizer_iff.mp
        ((show closure ({t} : Set G) ≤ normalizer (C : Set G) from
          by rw [← zpowers_eq_closure]; exact zpowers_le.mpr ht) ha) _).mp ihb
  | inv a ha iha =>
      rw [commutatorElement_inv_left]
      have hna : a⁻¹ ∈ normalizer (C : Set G) :=
        (normalizer (C : Set G)).inv_mem
          ((show closure ({t} : Set G) ≤ normalizer (C : Set G) from
            by rw [← zpowers_eq_closure]; exact zpowers_le.mpr ht) ha)
      have hc : ⁅x, a⁆ ∈ C := by rw [← commutatorElement_inv]; exact C.inv_mem iha
      simpa only [inv_inv] using (mem_normalizer_iff.mp hna _).mp hc

/-- A reflection moving one involution by a central nonidentity displacement
has exactly the fixed axis and commutator line specified by those generators. -/
theorem marked_reflection_axis_center {A : Subgroup G} {w c t : G}
    (hw : orderOf w = 2) (hc : c ≠ 1) (hcA : c ∈ A)
    (hwA : w ∈ centralizer (A : Set G))
    (hAc : A ≤ centralizer (zpowers c : Set G))
    (hfixed : A ≤ involutionCentralizer t)
    (hmove : MulAut.conj t w = w * c) :
    (A ⊔ zpowers w) ⊓ involutionCentralizer t = A ∧
      ⁅A ⊔ zpowers w, zpowers t⁆ = zpowers c := by
  have hfix (x : G) (hx : x ∈ A) : MulAut.conj t x = x :=
    (conjugation_fixed_iff t x).mpr (hfixed hx)
  have hwc : w * c = c * w := (mem_centralizer_iff.mp hwA c hcA).symm
  have htw : ⁅t, w⁆ = c := by
    change (MulAut.conj t w) * w⁻¹ = c
    rw [hmove, hwc, mul_inv_cancel_right]
  have htC : t ∈ centralizer (zpowers c : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (hfixed hcA)).symm)
  have hwC : w ∈ centralizer (zpowers c : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hwc
  have hVC : A ⊔ zpowers w ≤ centralizer (zpowers c : Set G) :=
    sup_le hAc (zpowers_le.mpr hwC)
  have hnormal : zpowers w ≤ normalizer (A : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hwA)
  have decompose (x : G) (hx : x ∈ A ⊔ zpowers w) :
      ∃ a ∈ A, x = a ∨ x = a * w := by
    have hprod : x ∈ (A : Set G) * (zpowers w : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A (zpowers w) hnormal]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod
    classical
    change b ∈ zpowers w at hb
    rw [(orderOf_pos_iff.mp (by omega : 0 < orderOf w)).mem_zpowers_iff_mem_range_orderOf,
      hw] at hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    have hn' : n = 0 ∨ n = 1 := by have := Finset.mem_range.mp hn; omega
    rcases hn' with rfl | rfl
    · exact ⟨a, ha, Or.inl (by simp)⟩
    · exact ⟨a, ha, Or.inr (by simp)⟩
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, he | he⟩ := decompose x hx.1
      · exact he ▸ ha
      · have hxe : MulAut.conj t x = x := (conjugation_fixed_iff t x).mpr hx.2
        rw [he, map_mul, hfix a ha, hmove] at hxe
        have hce : c = 1 := by
          apply mul_left_cancel (a := a * w)
          simpa only [mul_assoc, mul_one] using hxe
        exact (hc hce).elim
    · exact le_inf le_sup_left hfixed
  · apply le_antisymm
    · rw [commutator_comm]
      apply commutator_cyclic_le (Subgroup.centralizer_le_normalizer _ htC)
      intro x hx
      obtain ⟨a, ha, rfl | rfl⟩ := decompose x hx
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mem_centralizer_singleton_iff.mp (hfixed ha)).symm]
        exact (zpowers c).one_mem
      · rw [commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_mul_comm.mpr
            (mem_centralizer_singleton_iff.mp (hfixed ha)).symm, one_mul, htw]
        exact (mem_normalizer_iff.mp
          ((hVC.trans (Subgroup.centralizer_le_normalizer _)) (mem_sup_left ha)) c).mp (mem_zpowers c)
    · apply zpowers_le.mpr
      rw [← htw, commutator_comm]
      exact commutator_mem_commutator (mem_zpowers t) (mem_sup_right (mem_zpowers w))
variable [Finite G] {T : Sylow 2 G} {z g r v : G} {L R : Subgroup G}

/-- The original reflection has the complete marked transvection equations. -/
theorem CentralizerGeometry.exists_marked_transvection
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hc : CentralizerGeometry T z L r v) :
    ∃ t ∈ componentSylow T L ⊓
        normalizer (commonCentralizer (T : Subgroup G) z r : Set G),
      MulAut.conj t r = r * v ∧ MulAut.conj t z = z ∧ MulAut.conj t v = v ∧
      markedEight z r v ⊓ involutionCentralizer t = zpowers z ⊔ zpowers v ∧
      ⁅markedEight z r v, zpowers t⁆ = zpowers v := by
  obtain ⟨t, ht, htr⟩ := hc.reflection
  have htT : t ∈ (T : Subgroup G) := ht.1.1
  have hzA : z ∈ embeddedCenter (T : Subgroup G) := by
    rw [hc.center_eq]
    exact mem_sup_left (mem_zpowers z)
  have hvA : v ∈ embeddedCenter (T : Subgroup G) := by
    rw [hc.center_eq]
    exact mem_sup_right (mem_zpowers v)
  have hfix : embeddedCenter (T : Subgroup G) ≤ involutionCentralizer t := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hx.2 t htT).symm)
  have hV : markedEight z r v = embeddedCenter (T : Subgroup G) ⊔ zpowers r := by
    rw [hc.center_eq, markedEight, sup_comm (zpowers z) (zpowers v)]
  have hrv : r ∈ centralizer (embeddedCenter (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (show embeddedCenter (T : Subgroup G) ≤
      centralizer (T : Set G) from inf_le_right) (h.le_sylow hr)
  have hAc : embeddedCenter (T : Subgroup G) ≤ centralizer (zpowers v : Set G) :=
    inf_le_right.trans (centralizer_le (fun _ hx => (zpowers_le.mpr hvA.1) hx))
  have hvne : v ≠ 1 := by intro he; simpa [he] using hc.v_order
  obtain ⟨haxis, hcenter⟩ := marked_reflection_axis_center hr2 hvne hvA hrv hAc hfix htr
  refine ⟨t, ht, htr, (conjugation_fixed_iff t z).mpr (hfix hzA),
    (conjugation_fixed_iff t v).mpr (hfix hvA), ?_, ?_⟩
  · rw [← hV] at haxis
    exact haxis.trans hc.center_eq
  · simpa only [← hV] using hcenter

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
