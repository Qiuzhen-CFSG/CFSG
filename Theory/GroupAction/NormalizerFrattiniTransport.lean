module

public import Theory.GroupAction.NormalizerFrattini

/-!
# Transporting an irreducible normalizer action through an embedding

A homomorphism injective on P identifies the two Frattini quotients. An
irreducible action of any subgroup normalizing P therefore makes the full
normalizer of its image irreducible. The equivalence is induced by the
original homomorphism, so it also applies to an odd subgroup modulo O₂.

Source: the quotient step in Aschbacher--Smith 13.1.11, printed p.872.
-/

public noncomputable section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem frattini_map_mulEquiv (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    exact ⟨e.symm b, frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb, e.apply_symm_apply b⟩

/-- The actual map on a subgroup induces this equivalence of Frattini quotients. -/
@[expose] def mapFrattiniEquiv (f : G →* H) (P : Subgroup G)
    (hi : Function.Injective (f.subgroupMap P)) :
    (P ⧸ frattini P) ≃* (P.map f ⧸ frattini (P.map f)) :=
  let e := MulEquiv.ofBijective (f.subgroupMap P) ⟨hi, f.subgroupMap_surjective P⟩
  QuotientGroup.congr _ _ e (frattini_map_mulEquiv e)

theorem mapFrattiniEquiv_apply_mk (f : G →* H) (P : Subgroup G)
    (hi : Function.Injective (f.subgroupMap P)) (a : P) :
    mapFrattiniEquiv f P hi (QuotientGroup.mk' (frattini P) a) =
      QuotientGroup.mk' (frattini (P.map f)) (f.subgroupMap P a) := rfl

private def mapNormalizerHom (f : G →* H) (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) : S →* normalizer (P.map f : Set H) :=
  (f.comp S.subtype).codRestrict _ (fun s => P.le_normalizer_map f (mem_map_of_mem f (hn s.property)))

private theorem mapFrattiniEquiv_equivariant (f : G →* H) (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G))
    (hi : Function.Injective (f.subgroupMap P)) (s : S) (a : P ⧸ frattini P) :
    mapFrattiniEquiv f P hi (frattiniConjugationHom S P hn s a) =
      frattiniConjugationHom (normalizer (P.map f : Set H)) (P.map f) le_rfl
        (mapNormalizerHom f P S hn s) (mapFrattiniEquiv f P hi a) := by
  induction a using QuotientGroup.induction_on with | H a =>
    change mapFrattiniEquiv f P hi
      (frattiniConjugationHom S P hn s (QuotientGroup.mk' _ a)) =
        frattiniConjugationHom (normalizer (P.map f : Set H)) (P.map f) le_rfl
          (mapNormalizerHom f P S hn s)
            (mapFrattiniEquiv f P hi (QuotientGroup.mk' _ a))
    simp only [frattiniConjugationHom, MonoidHom.comp_apply, quotientAut_apply_mk,
      mapFrattiniEquiv_apply_mk]
    apply congrArg (QuotientGroup.mk' _)
    apply Subtype.ext
    change f ((s : G) * (a : G) * (s : G)⁻¹) = f s * f a * (f s)⁻¹
    simp only [map_mul, map_inv]

/-- An irreducible subgroup of the normalizer remains irreducible after any
homomorphism which embeds P; the target actor is the full actual normalizer. -/
theorem normalizerFrattiniIrreducible_map (f : G →* H) (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G))
    (hi : Function.Injective (f.subgroupMap P))
    (hirr : ∀ A : Subgroup (P ⧸ frattini P),
      (∀ s : S, ∀ a ∈ A, frattiniConjugationHom S P hn s a ∈ A) →
        A = ⊥ ∨ A = ⊤) : IsNormalizerFrattiniIrreducible (P.map f) := by
  intro A hA
  let e := mapFrattiniEquiv f P hi
  have hinv : ∀ s : S, ∀ a ∈ A.comap e.toMonoidHom,
      frattiniConjugationHom S P hn s a ∈ A.comap e.toMonoidHom := by
    intro s a ha
    change e (frattiniConjugationHom S P hn s a) ∈ A
    rw [mapFrattiniEquiv_equivariant]
    exact hA _ _ ha
  rcases hirr (A.comap e.toMonoidHom) hinv with hb | ht
  · left
    have hm := congrArg (Subgroup.map e.toMonoidHom) hb
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      Subgroup.map_bot] using hm
  · right
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm

end Subgroup
