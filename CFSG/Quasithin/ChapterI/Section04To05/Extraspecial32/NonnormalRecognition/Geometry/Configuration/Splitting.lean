module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Splitting.Involution
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Splitting.Sylow
public import Theory.GroupTheory.Gaschutz

/-!
# Splitting the normalizer at either endpoint

The actual intersection normalizer supplies an outside involution of H.
Nonnormality forces it to interchange the quaternion factors. The invariant
four-group construction then supplies a complement to the literal E in an
actual Sylow two-subgroup of N_G(E). Gaschütz's theorem lifts this to a
complement to E in N_G(E), since E is elementary abelian and normal in its
own normalizer. No fusion-saturation assumption, ambient recognition, or
D-system is used.

This is the local splitting argument of source Lemma 2.8 applied to the
normalizers of the two actual intersections in Lemma 3.1.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), Lemmas 2.8 and 3.1, printed pp.36–37.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z g : G}

/-- The source hypotheses split the elementary intersection in an actual
Sylow two-subgroup of its normalizer, with no saturation assumption. -/
public theorem intersection_sylow_complement (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z) (d : IntersectionData z g) :
    ∃ S : Sylow 2 (normalizer (coreIntersection z g : Set G)),
      ∃ K : Subgroup S,
        IsComplement' (((coreIntersection z g).subgroupOf
          (normalizer (coreIntersection z g : Set G))).subgroupOf S) K := by
  obtain ⟨a, haH, ha, hout⟩ := exists_outside_involution h d
  obtain ⟨q⟩ := h.quaternionCentralProduct
  let aH : Centralizer z := ⟨a, haH⟩
  have hs := factor_swap_of_outside_involution h hn q aH (Subtype.ext ha)
    (fun haQ => hout (mem_map_of_mem (Centralizer z).subtype haQ))
  let e : Core z ≃* coreInG z :=
    (Core z).equivMapOfInjective (Centralizer z).subtype (Centralizer z).subtype_injective
  let qG : QuaternionCentralProductData (coreInG z) := {
    left := q.left.map e.toMonoidHom
    right := q.right.map e.toMonoidHom
    left_model := ⟨(e.subgroupMap q.left).symm.trans q.left_model.some⟩
    right_model := ⟨(e.subgroupMap q.right).symm.trans q.right_model.some⟩
    intersection_card := by
      rw [← map_inf _ _ _ e.injective, card_map_of_injective e.injective]
      exact q.intersection_card
    commute := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      change e b * e c = e c * e b
      simpa only [← map_mul] using congrArg e (q.commute b hb c hc)
    span := by
      rw [← Subgroup.map_sup, q.span, map_top_of_surjective _ e.surjective] }
  apply intersection_sylow_complement_of_swap h d qG a haH ha hout
  change ((q.left.map e.toMonoidHom).map (coreInG z).subtype).map
    (MulAut.conj a).toMonoidHom = (q.right.map e.toMonoidHom).map (coreInG z).subtype
  have hh := congrArg (fun R : Subgroup (Core z) =>
    R.map ((Centralizer z).subtype.comp (Core z).subtype)) hs
  simp only [map_map] at hh ⊢
  exact hh

/-- The nonnormal quaternion hypotheses split the literal intersection in its
whole normalizer. This applies at either endpoint without ambient saturation. -/
public theorem intersection_normalizer_complement (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z) (d : IntersectionData z g) :
    ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K := by
  let E := coreIntersection z g
  let V := E.subgroupOf (normalizer (E : Set G))
  let : IsElementaryAbelian 2 E := d.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf E.le_normalizer
  obtain ⟨S, hS⟩ := intersection_sylow_complement h hn d
  exact (V.exists_complement_iff_sylow (IsElementaryAbelian.isPGroup 2 V) S).mpr hS

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
