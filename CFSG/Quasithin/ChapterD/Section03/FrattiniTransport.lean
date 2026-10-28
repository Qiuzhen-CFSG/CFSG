module
public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.Frattini.OmegaProducts

/-!
# Transport of the literal Frattini conjugation action

A group isomorphism sends a subgroup's Frattini subgroup onto that of its
image. The induced quotient isomorphism intertwines the original normalizer
conjugations, so invariant subgroups and Frattini irreducibility transport.

This connects the actual action image to the centralizer quotient used in
Aschbacher--Smith 15.1.2, printed p.1086, extraspecial case.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterD.Section03
variable {G H : Type*} [Group G] [Group H]

private theorem frattiniAction_mk' (T X : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G)) (t : T) (x : X) :
    frattiniAction T X hTX t (QuotientGroup.mk' (frattini X) x) =
      QuotientGroup.mk' (frattini X)
        (X.normalizerMonoidHom ⟨t, hTX t.property⟩ x) := by
  change quotientAut (frattini X) (X.normalizerMonoidHom (inclusion hTX t))
    (QuotientGroup.mk' (frattini X) x) = _
  rw [quotientAut_apply_mk]
  rfl

private theorem frattiniIrreducible_transfer
    (T X : Subgroup G) (S Y : Subgroup H)
    (hTX : T ≤ normalizer (X : Set G)) (hSY : S ≤ normalizer (Y : Set H))
    (e : Y ≃* X) (a : S →* T) (ha : Function.Surjective a)
    (he : ∀ s : S, ∀ y : Y,
      e (Y.normalizerMonoidHom ⟨s, hSY s.property⟩ y) =
      X.normalizerMonoidHom ⟨a s, hTX (a s).property⟩ (e y))
    (hI : FrattiniIrreducible T X hTX) : FrattiniIrreducible S Y hSY := by
  let q := QuotientGroup.congr (frattini Y) (frattini X) e (frattini_map_equiv e)
  have hq (s : S) (v : Y ⧸ frattini Y) :
      q (frattiniAction S Y hSY s v) =
        frattiniAction T X hTX (a s) (q v) := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini Y) v
    rw [frattiniAction_mk']
    change QuotientGroup.mk' (frattini X)
      (e (Y.normalizerMonoidHom ⟨s, hSY s.property⟩ y)) =
      frattiniAction T X hTX (a s) (QuotientGroup.mk' (frattini X) (e y))
    rw [frattiniAction_mk', he]
  intro A hA
  have hi : ∀ t : T, ∀ v ∈ A.map q.toMonoidHom,
      frattiniAction T X hTX t v ∈ A.map q.toMonoidHom := by
    intro t v hv
    obtain ⟨s, rfl⟩ := ha t
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨frattiniAction S Y hSY s y, hA s y hy, hq s y⟩
  rcases hI (A.map q.toMonoidHom) hi with hb | ht
  · left
    apply map_injective (f := q.toMonoidHom) q.injective
    simpa only [Subgroup.map_bot] using hb
  · right
    apply map_injective (f := q.toMonoidHom) q.injective
    rw [map_top_of_surjective q.toMonoidHom q.surjective]
    exact ht

/-- Ambient isomorphisms preserve irreducibility of the original Frattini action. -/
theorem FrattiniIrreducible.map_equiv {T X : Subgroup G}
    {hTX : T ≤ normalizer (X : Set G)} (hI : FrattiniIrreducible T X hTX)
    (e : G ≃* H)
    (hbar : T.map e.toMonoidHom ≤ normalizer (X.map e.toMonoidHom : Set H)) :
    FrattiniIrreducible (T.map e.toMonoidHom) (X.map e.toMonoidHom) hbar := by
  apply frattiniIrreducible_transfer T X _ _ hTX hbar
    (e.subgroupMap X).symm (e.subgroupMap T).symm.toMonoidHom
    (e.subgroupMap T).symm.surjective ?_ hI
  intro t x
  apply Subtype.ext
  change e.symm ((t : H) * (x : H) * (t : H)⁻¹) =
    e.symm t * e.symm x * (e.symm t)⁻¹
  simp only [map_mul, map_inv]
end CFSG.Quasithin.ChapterD.Section03
