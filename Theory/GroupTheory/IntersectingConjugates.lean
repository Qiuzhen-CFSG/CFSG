module

public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Intersecting conjugates and abelian point spans

If the normalizer of V is transitive on its nonidentity elements, the span
of the C_G(z)-conjugates of V is abelian exactly when intersecting conjugates
of V commute. One direction moves an intersection element to z and uses the
centralizer transporter. In the other direction every generating conjugate
contains z; normality extends its centralization of V to the entire span.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.6(2)–(3), printed pp.850–851. The Chapter 12 consumer retains
the actual right-conjugation convention and the marked point subgroup.
-/

namespace Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A nontrivial intersection can be moved to the distinguished point. -/
public theorem commutator_conjugate_eq_bot_of_abelian_point_span (V : Subgroup G) {z : G} (hzV : z ∈ V) (hz : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ n ∈ normalizer (V : Set G),
      (MulAut.conj n) z = x)
    [IsMulCommutative (conjugateSpanBy V (centralizer ({z} : Set G)))]
    (g : G) (hg : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  have ha := a.property
  have hane' : (a : G) ≠ 1 := fun he => hane (Subtype.ext he)
  obtain ⟨n, hn, hnz⟩ := htrans a ha.1 hane'
  have hz' : z ∈ V.map (MulAut.conj (n⁻¹ * g)).toMonoidHom := by
    obtain ⟨b, hb, hba⟩ := ha.2
    refine ⟨b, hb, ?_⟩
    apply (MulAut.conj n).injective
    simpa [MulAut.conj_apply, mul_assoc] using hba.trans hnz.symm
  let : IsMulCommutative (centralizerConjugateClosure V z) := by
    rw [centralizerConjugateClosure_eq_conjugateSpanBy]
    infer_instance
  have hcomm := commutator_eq_bot_of_abelian_centralizerConjugateClosure V hz htrans
    (g := 1) (by simpa using hzV) hz'
  have hc : V ≤ centralizer (V.map (MulAut.conj (n⁻¹ * g)).toMonoidHom : Set G) := by
    have h1 : V.map (MulAut.conj (1 : G)).toMonoidHom = V := by
      ext x
      simp [Subgroup.mem_map]
    rw [h1] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have hx' : (MulAut.conj n⁻¹) x ∈ V :=
    (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hn) x).mp hx
  have hy' : (MulAut.conj n⁻¹) y ∈ V.map (MulAut.conj (n⁻¹ * g)).toMonoidHom := by
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨b, hb, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  apply (MulAut.conj n⁻¹).injective
  simpa only [map_mul] using mem_centralizer_iff.mp (hc hx') _ hy'

/-- Pairwise commutation of intersecting conjugates makes the point span abelian. -/
public theorem point_span_abelian_of_intersecting_conjugates_commute (V : Subgroup G) {z : G} (hzV : z ∈ V) (hz : z ≠ 1)
    (hcomm : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    IsMulCommutative (conjugateSpanBy V (centralizer ({z} : Set G))) := by
  let H := centralizer ({z} : Set G)
  let U := conjugateSpanBy V H
  have hc : U ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨h, hh, v, hv, rfl⟩
    have hzconj : (MulAut.conj h) z = z := by
      have hh' := mem_centralizer_singleton_iff.mp hh
      simp [MulAut.conj_apply, hh', mul_assoc]
    have hne : V ⊓ V.map (MulAut.conj h).toMonoidHom ≠ ⊥ := by
      intro he
      have hzmem : z ∈ V ⊓ V.map (MulAut.conj h).toMonoidHom :=
        ⟨hzV, z, hzV, hzconj⟩
      exact hz (show z ∈ (⊥ : Subgroup G) from he ▸ hzmem)
    exact (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (hcomm h hne)))
      (mem_map_of_mem _ hv)
  apply le_centralizer_iff_isMulCommutative.mp
  exact le_centralizer_conjugateSpanBy_of_normalizes U V H
    (le_normalizer_conjugateSpanBy V H) hc

/-- The point-span criterion, with normalizer transitivity as its only fusion input. -/
public theorem point_span_abelian_iff_intersecting_conjugates_commute
    (V : Subgroup G) {z : G} (hzV : z ∈ V) (hz : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ n ∈ normalizer (V : Set G),
      (MulAut.conj n) z = x) :
    IsMulCommutative (conjugateSpanBy V (centralizer ({z} : Set G))) ↔
      ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  constructor
  · intro hc
    let := hc
    exact commutator_conjugate_eq_bot_of_abelian_point_span V hzV hz htrans
  · exact point_span_abelian_of_intersecting_conjugates_commute V hzV hz

end Subgroup
