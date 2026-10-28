module
public import ABG.ChapterII.Section1.WreathedFrameTransport
public import ABG.ChapterII.Section1.WreathedRepresentativeFusion

/-!
# Fusion controlled by an arbitrary wreathed frame

Let `U` and `V` be the ambient subgroups of a wreathed fusion frame for a
specified Sylow two-subgroup `S` of a finite group. A reflexive transitive
relation on `S` containing conjugacy inside `S` is preserved by every
ambient conjugacy if normalizer steps at `U` and `V` preserve it. This is
the representative-independent control reduction in the opening proof of
ABG Chapter II Section 1 Proposition 2, article p.12, in
`refs/latex/alperin-brauer-gorenstein-pages/page-013.tex`.

Choose a presentation of `S` and compare its canonical subgroups with the
frame. The bases agree, and the two quaternion central products are conjugate
by an element of `S`. The inverse conjugator transfers the hypothesis at the
frame's `V` to the canonical `V`; transitivity absorbs the endpoint Sylow
conjugacies. Apply the canonical representative fusion relation theorem.
The supplied representatives need no extremality or tame-intersection
hypotheses, and the relation needs no symmetry assumption.
-/

namespace ABG

/-- The two normalizers of a wreathed frame control relations under ambient element fusion. -/
public theorem wreathed_representative_fusion_relation
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G) (hframe : WreathedFusionFrame S n U V)
    (R : S → S → Prop) (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hconj : ∀ {x y : S}, IsConj x y → R x y)
    (hU : ∀ g : G, g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x y : S, (x : G) ∈ U → g⁻¹ * (x : G) * g = (y : G) → R x y)
    (hV : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) →
      ∀ x y : S, (x : G) ∈ V → g⁻¹ * (x : G) * g = (y : G) → R x y)
    {x y : S} (hxy : IsConj (x : G) (y : G)) : R x y := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hframe.1
  obtain ⟨hbase, s, hs⟩ := hframe.presentation_representatives P
  apply Wreathed.representative_fusion_relation S P R hrefl htrans hconj ?_ ?_ hxy
  · simpa only [← hbase] using hU
  · have hinv : V.map (MulAut.conj ((s⁻¹ : S) : G)).toMonoidHom =
        P.V.map (S : Subgroup G).subtype := by
      rw [← hs, Subgroup.map_map]
      have he : (MulAut.conj ((s⁻¹ : S) : G)).toMonoidHom.comp
          (MulAut.conj (s : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [he, Subgroup.map_id]
    exact Subgroup.normalizer_fusion_relation_of_conjugate (S : Subgroup G)
      (P.V.map (S : Subgroup G).subtype) V R htrans hconj s⁻¹ hinv hV

end ABG
