module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Preliminary
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound

/-!
# The literal elementary-eight intersection and its two cores

For s = g*z*g⁻¹ in Q, restrict inverse conjugation and the centralizer
quotient map to C_Q(s). Its kernel embeds as precisely Q ∩ Qᵍ. The domain
has order at least sixteen and its image has order dividing both 32 and
6, hence at most two. Together with the elementary rank bound this gives
order eight without changing the conjugator. Such an elementary eight
contains the extraspecial center, is normal in each core, and centralizes
only itself inside Q. We also record the exact transport under H-conjugacy.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemmas 2.4–2.5, p.34. Normality in H and the ambient centralizer
require the subsequent local action argument and are not assumed here.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
/-- The conjugate core lies in the centralizer of the same left-conjugated involution. -/
public theorem conjugate_core_le_centralizer (g : G) :
    (coreInG z).map (MulAut.conj g).toMonoidHom ≤ Centralizer (g * z * g⁻¹) := by
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hc := mem_centralizer_singleton_iff.mp (coreInG_le z hx)
  change (MulAut.conj g) x * (MulAut.conj g) z =
    (MulAut.conj g) z * (MulAut.conj g) x
  simpa only [map_mul] using congrArg (MulAut.conj g) hc

/-- The exact order assertion of source 2.4 for the given literal intersection. -/
public theorem coreIntersection_card (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    Nat.card (coreIntersection z g) = 8 := by
  let Q := coreInG z
  let s : Q := ⟨g * z * g⁻¹, hgQ⟩
  let D : Subgroup Q := centralizer ({s} : Set Q)
  let inc : D →* G := Q.subtype.comp D.subtype
  let : IsExtraspecial 2 Q := h.coreInG_extraspecial
  have hlarge : 16 ≤ Nat.card D :=
    IsExtraspecial.centralizer_card_ge_sixteen_of_card_thirty_two h.coreInG_card s
  have hinj : Function.Injective inc := Q.subtype_injective.comp D.subtype_injective
  let back : D →* G := (MulAut.conj g).symm.toMonoidHom.comp inc
  have hback (x : D) : back x ∈ Centralizer z := by
    apply mem_centralizer_singleton_iff.mpr
    have hc := congrArg Q.subtype (mem_centralizer_singleton_iff.mp x.property)
    change inc x * (g * z * g⁻¹) = (g * z * g⁻¹) * inc x at hc
    have he := congrArg (fun a : G => g⁻¹ * a * g) hc
    simpa only [back, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_symm_apply, mul_assoc, inv_mul_cancel, mul_inv_cancel,
      inv_mul_cancel_left, one_mul, mul_one] using he
  let toH : D →* Centralizer z := back.codRestrict (Centralizer z) hback
  let f : D →* (Centralizer z ⧸ Core z) := (QuotientGroup.mk' (Core z)).comp toH
  have hker (x : D) : x ∈ f.ker ↔ inc x ∈ Q.map (MulAut.conj g).toMonoidHom := by
    change toH x ∈ (QuotientGroup.mk' (Core z)).ker ↔ _
    rw [QuotientGroup.ker_mk', ← coreInG_subgroupOf z, mem_map_equiv]
    rfl
  have hmap : f.ker.map inc = coreIntersection z g := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.val.property, (hker x).mp hx⟩
    · intro x hx
      have hc : (⟨x, hx.1⟩ : Q) ∈ D := by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact mem_centralizer_singleton_iff.mp (conjugate_core_le_centralizer g hx.2)
      let xD : D := ⟨⟨x, hx.1⟩, hc⟩
      exact ⟨xD, (hker xD).mpr hx.2, rfl⟩
  have hkerCard : Nat.card f.ker = Nat.card (coreIntersection z g) := by
    rw [← hmap, card_map_of_injective hinj]
  have hr6 : Nat.card f.range ∣ 6 := h.quotient_card ▸ f.range.card_subgroup_dvd_card
  have hr32 : Nat.card f.range ∣ 32 :=
    (card_range_dvd f).trans (h.coreInG_card ▸ D.card_subgroup_dvd_card)
  have hr2 : Nat.card f.range ∣ 2 := Nat.dvd_gcd hr6 hr32
  have hrle : Nat.card f.range ≤ 2 := Nat.le_of_dvd (by decide) hr2
  have hc := f.ker.card_mul_index
  rw [index_ker, hkerCard] at hc
  have hu := coreIntersection_card_le_eight h g hg
  nlinarith [Nat.mul_le_mul_left (Nat.card (coreIntersection z g)) hrle]

private theorem eight_normalizes_and_contains_center
    (E Q : Subgroup G) [IsExtraspecial 2 Q] [IsElementaryAbelian 2 E]
    (hQ : Nat.card Q = 32) (hE : Nat.card E = 8) (hEQ : E ≤ Q) :
    Q ≤ normalizer (E : Set G) ∧ (center Q).map Q.subtype ≤ E := by
  let : IsElementaryAbelian 2 (E.subgroupOf Q) := IsElementaryAbelian.subgroupOf hEQ
  have hc : Nat.card (E.subgroupOf Q) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans hE
  obtain ⟨hn, hz⟩ :=
    IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two hQ
      (E.subgroupOf Q) hc
  refine ⟨(normal_subgroupOf_iff_le_normalizer hEQ).mp hn, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact hz hq

/-- The first core normalizes its elementary intersection with the second core. -/
public theorem core_normalizes_intersection (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    coreInG z ≤ normalizer (coreIntersection z g : Set G) := by
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  let : IsElementaryAbelian 2 (coreIntersection z g) := coreIntersection_elementary h g hg
  exact (eight_normalizes_and_contains_center (coreIntersection z g) (coreInG z)
    h.coreInG_card (coreIntersection_card h g hgQ hg) (coreIntersection_le z g)).1

/-- Reciprocity: the original involution belongs to the conjugate core as well. -/
public theorem involution_mem_coreIntersection (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    z ∈ coreIntersection z g := by
  let : IsExtraspecial 2 (coreInG z) := h.coreInG_extraspecial
  let : IsElementaryAbelian 2 (coreIntersection z g) := coreIntersection_elementary h g hg
  have hz := (eight_normalizes_and_contains_center (coreIntersection z g) (coreInG z)
    h.coreInG_card (coreIntersection_card h g hgQ hg) (coreIntersection_le z g)).2
  rw [h.coreInG_center_image] at hz
  exact hz (mem_zpowers z)

/-- The second core also normalizes the literal intersection. -/
public theorem conjugate_core_normalizes_intersection (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    (coreInG z).map (MulAut.conj g).toMonoidHom ≤
      normalizer (coreIntersection z g : Set G) := by
  let Qg := (coreInG z).map (MulAut.conj g).toMonoidHom
  let : IsExtraspecial 2 Qg :=
    IsExtraspecial.of_mulEquiv ((MulAut.conj g).subgroupMap (coreInG z)) h.coreInG_extraspecial
  let : IsElementaryAbelian 2 (coreIntersection z g) := coreIntersection_elementary h g hg
  have hc : Nat.card Qg = 32 := by
    rw [card_map_of_injective (MulAut.conj g).injective, h.coreInG_card]
  exact (eight_normalizes_and_contains_center (coreIntersection z g) Qg hc
    (coreIntersection_card h g hgQ hg) inf_le_right).1

/-- The intersection is self-centralizing inside the original extraspecial core. -/
public theorem core_centralizer_intersection (h : Hypotheses z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    coreInG z ⊓ centralizer (coreIntersection z g : Set G) = coreIntersection z g := by
  let Q := coreInG z
  let E := coreIntersection z g
  let F := E.subgroupOf Q
  have hEQ : E ≤ Q := coreIntersection_le z g
  let : IsExtraspecial 2 Q := h.coreInG_extraspecial
  let : IsElementaryAbelian 2 E := coreIntersection_elementary h g hg
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hEQ
  have hF : Nat.card F = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans
      (coreIntersection_card h g hgQ hg)
  have hz : center Q ≤ F :=
    (IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two
      h.coreInG_card F hF).2
  have hc : centralizer (F : Set Q) = F :=
    extraspecial_two_centralizer_eq_of_card_sq F hz (by rw [hF, h.coreInG_card]; decide)
  apply le_antisymm
  · rintro x ⟨hxQ, hxC⟩
    have hxF : (⟨x, hxQ⟩ : Q) ∈ centralizer (F : Set Q) := by
      intro y hy
      exact Subtype.ext (hxC y hy)
    rw [hc] at hxF
    exact hxF
  · exact le_inf hEQ E.le_centralizer


omit [Finite G] in
private theorem conjugation_comp (a g : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (a * g)).toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- Arranging the source witness by an element of H conjugates the literal intersection. -/
public theorem coreIntersection_map_conj (h : Hypotheses z) {a : G}
    (ha : a ∈ Centralizer z) (g : G) :
    (coreIntersection z g).map (MulAut.conj a).toMonoidHom =
      coreIntersection z (a * g) := by
  have hn : a ∈ normalizer (coreInG z : Set G) := h.normalizer_core.symm ▸ ha
  have he : (coreInG z).map (MulAut.conj a).toMonoidHom = coreInG z :=
    mem_normalizer_iff_map_conj_eq.mp hn
  unfold coreIntersection
  rw [map_inf _ _ _ (MulAut.conj a).injective, map_map,
    he, conjugation_comp]

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
