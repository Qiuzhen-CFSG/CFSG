module

public import CFSG.Quasithin.ChapterF.Section09.TrackBounds
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Endpoints

/-!
# Original F.9 critical endpoints in the ambient group

The F.7 seed and neighbor-join module are identified with V and V_H after
mapping out of the actual generated subgroup. Normalized critical endpoints
supply the two edge placements, mutual normalization and noncentral action
on U_gamma/V_1^g. Reversal transports every H-invariant label simultaneously.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.10, F.9.13(2–5), F.9.17, printed pp.321–324.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base)
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
open Section07 Section07.CriticalPairs
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

omit h [Finite G] in
/-- Conjugating inside G₀ and then including it in G is literal ambient conjugation. -/
theorem conjugate_map_ambient (A : Subgroup (G₀ (D := D))) (g : G₀ (D := D)) :
    (A.map (MulAut.conj g).toMonoidHom).map (D.LT ⊔ D.H).subtype =
      (A.map (D.LT ⊔ D.H).subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1

omit h [Finite G] in
private theorem conjugate_inverse (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, MonoidHom.id_apply]
    group
  rw [he, map_id]

/-- The second F.7 module is exactly the large F.9 span, not U_H. -/
theorem f7Large_map :
    (vertexModule (family (D := D)) h.f7Setup.seed
      (base (family (D := D)) true)).map (D.LT ⊔ D.H).subtype = D.VH := by
  rw [second_base_module_eq_conjugate_join _ _ h.f7Setup.seed_normalized,
    ← conjugateSpanBy_eq_iSup_conj, map_conjugateSpanBy, h.f7Seed_map]
  change conjugateSpanBy D.V
    ((D.H.subgroupOf (D.LT ⊔ D.H)).map (D.LT ⊔ D.H).subtype) = _
  rw [map_subgroupOf_eq_of_le le_sup_right]
  rfl

abbrev CriticalEndpoint := NormalizedEndpoint h.f7Setup h.f7V_ne_bot

namespace CriticalEndpoint
variable {h} (i : h.CriticalEndpoint)

abbrev representative : G := ((i : G₀ (D := D)) : G)
abbrev conjugate (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj i.representative).toMonoidHom

include i

/-- The module at the opposite endpoint is the actual conjugate V_H^g. -/
theorem large_map :
    (vertexModule (family (D := D)) h.f7Setup.seed i.vertex).map
      (D.LT ⊔ D.H).subtype = i.conjugate D.VH := by
  rw [NormalizedEndpoint.vertex, vertexModule_translate _ _ h.f7Setup.seed_normalized,
    conjugate_map_ambient, h.f7Large_map]

/-- The endpoint stabilizer is the same literal conjugate of H. -/
theorem stabilizer_map :
    (stabilizer (family (D := D)) i.vertex).map (D.LT ⊔ D.H).subtype =
      i.conjugate D.H := by
  rw [NormalizedEndpoint.vertex, stabilizer_translate,
    show stabilizer (family (D := D)) (base (family (D := D)) true) =
      family (D := D) true from stabilizer_base _ true,
    conjugate_map_ambient]
  change ((D.H.subgroupOf (D.LT ⊔ D.H)).map (D.LT ⊔ D.H).subtype).map _ = _
  rw [map_subgroupOf_eq_of_le le_sup_right]

/-- F.9.13(2), retaining the actual edge in the generated subgroup. -/
theorem edge_core (hb : 3 ≤ h.b) :
    ∃ w : CosetGeometry.RankTwo.Vertex (family (D := D)),
      w.type = false ∧ (graph (family (D := D))).Adj (base (family (D := D)) true) w ∧
      i.conjugate D.VH ≤
        (((stabilizer (family (D := D)) (base (family (D := D)) true)) ⊓
          stabilizer (family (D := D)) w).map (D.LT ⊔ D.H).subtype).pCoreIn 2 := by
  obtain ⟨w, hwt, hw, hc⟩ := i.exists_base_edge hb
  refine ⟨w, hwt, hw, ?_⟩
  have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hc
  rw [i.large_map, ← AmalgamLocalCores.pCoreIn_map_of_injective
    2 _ (D.LT ⊔ D.H).subtype_injective] at hm
  exact hm

theorem large_le (hb : 3 ≤ h.b) : i.conjugate D.VH ≤ D.H := by
  have hm := map_mono (f := (D.LT ⊔ D.H).subtype) (i.endpoint_module_le hb)
  rw [i.large_map] at hm
  exact hm.trans_eq (map_subgroupOf_eq_of_le le_sup_right)

theorem reverse_le (hb : 3 ≤ h.b) : D.VH ≤ i.conjugate D.H := by
  have hm := map_mono (f := (D.LT ⊔ D.H).subtype) (i.reverse_module_le hb)
  rw [h.f7Large_map, i.stabilizer_map] at hm
  exact hm

theorem commutator (hb : 3 ≤ h.b) :
    ⁅D.VH, i.conjugate D.VH⁆ ≤ D.VH ⊓ i.conjugate D.VH := by
  have hm := map_mono (f := (D.LT ⊔ D.H).subtype) (i.commutator_le hb)
  rw [map_commutator, map_inf _ _ _ (D.LT ⊔ D.H).subtype_injective,
    h.f7Large_map, i.large_map] at hm
  exact hm

/-- Criticality detects the genuine centralizer quotient from F.9.2(3). -/
theorem noncentral : ¬ ⁅i.conjugate D.UH, D.V⁆ ≤ i.conjugate D.V₁ := by
  intro hc
  have hV : D.V ≤ i.conjugate D.H := by
    have hm := map_mono (f := (D.LT ⊔ D.H).subtype) i.seed_le_stabilizer
    rwa [h.f7Seed_map, i.stabilizer_map] at hm
  have hpreV : D.V.map (MulAut.conj i.representative⁻¹).toMonoidHom ≤ D.H := by
    have hm := map_mono (f := (MulAut.conj i.representative⁻¹).toMonoidHom) hV
    simpa only [conjugate, conjugate_inverse] using hm
  have hpreC : ⁅D.UH, D.V.map (MulAut.conj i.representative⁻¹).toMonoidHom⁆ ≤ D.V₁ := by
    have hm := map_mono (f := (MulAut.conj i.representative⁻¹).toMonoidHom) hc
    simpa only [map_commutator, conjugate, conjugate_inverse] using hm
  have hpre : D.V.map (MulAut.conj i.representative⁻¹).toMonoidHom ≤ h.kernel D.UH := by
    intro v hv
    exact (h.mem_kernel_iff h.UH_le_H).mpr
      ⟨hpreV hv, fun u hu => hpreC (commutator_mem_commutator hu hv)⟩
  rw [h.kernel_UH_eq_QH] at hpre
  have hcore : D.V ≤ i.conjugate D.QH := by
    have hm := map_mono (f := (MulAut.conj i.representative).toMonoidHom) hpre
    have hi := conjugate_inverse D.V i.representative⁻¹
    rw [inv_inv] at hi
    rwa [hi] at hm
  have hcore' : h.f7Setup.seed ≤ (stabilizer (family (D := D)) i.vertex).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (f := (D.LT ⊔ D.H).subtype) (D.LT ⊔ D.H).subtype_injective).mp
    rw [h.f7Seed_map, ← AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (D.LT ⊔ D.H).subtype_injective, i.stabilizer_map]
    rw [AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (MulAut.conj i.representative).injective]
    exact hcore
  apply i.property.2.2
  apply hcore'.trans
  have hb := Completion.base_core_le_kernel (family (D := D)) h.f7Setup true
  have hm := map_mono (f := (MulAut.conj (i : G₀ (D := D))).toMonoidHom) hb
  rw [← ballKernel_translate,
    ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj (i : G₀ (D := D))).injective,
    ← stabilizer_base (family (D := D)) true, ← stabilizer_translate] at hm
  exact hm

/-- F.9.17 uses one conjugator on every H-invariant label. The small-star
nontriviality premise is exactly U_gamma not contained in O₂(H). -/
theorem reverse_labels (hb : 3 ≤ h.b) (hn : ¬ i.conjugate D.UH ≤ D.QH) :
    ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
      D.H ≤ normalizer (A : Set G) → (i.conjugate A).map
        (MulAut.conj j.representative).toMonoidHom = A := by
  have hsmall : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hn' : ¬ vertexModule (family (D := D)) h.f7Setup.seed i.vertex ≤
      (family (D := D) true).pCoreIn 2 := by
    intro hc
    apply hn
    have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hc
    rw [i.large_map, ← AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (D.LT ⊔ D.H).subtype_injective,
      show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
        map_subgroupOf_eq_of_le le_sup_right] at hm
    exact (map_mono hsmall).trans hm
  obtain ⟨j, hj⟩ := i.reversal (i.moving_of_not_le_core hb _ le_rfl hn')
  refine ⟨j, fun A hA => ?_⟩
  have hprod : representative (h := h) j * i.representative ∈ D.H := hj
  rw [conjugate, map_map]
  have he : (MulAut.conj (representative (h := h) j)).toMonoidHom.comp
      (MulAut.conj i.representative).toMonoidHom =
        (MulAut.conj (representative (h := h) j * i.representative)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [he]
  exact mem_normalizer_iff_map_conj_eq.mp (hA hprod)

end CriticalEndpoint

/-- Original F.9.10 supplies a nonempty finite family to the Chapter 15 consumer. -/
theorem criticalEndpoint_nonempty (hcore : D.V ≤ D.QH)
    (hc : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : Nonempty h.CriticalEndpoint :=
  NormalizedEndpoint.nonempty (h.b_bounds_of_intersecting_conjugates_commute hcore hc).2

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
