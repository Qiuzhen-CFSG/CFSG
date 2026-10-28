module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.Amalgam

/-!
# Equivalence on the setwise-edge stabilizer

An equivalence of graph uniqueness systems extends the given pointwise-edge
isomorphism to the setwise-edge stabilizer, compatibly with the local group.
This supplies the third isomorphism of the rank-three amalgam.

Choose the local edge reversal `t` in the equivalence identity. Every element
of the edge stabilizer lies in exactly one of the cosets `B` and `B * t`, where
`B` fixes both endpoints. The normal-form map sends `b * t` to the product of
the given images of `b` and `t`. Conjugation compatibility handles products
crossing the cosets, while agreement on `B ∩ H` supplies the square relation.
In particular, the reversal need not be an involution. Injectivity follows
from injectivity on `B` and the target reversal exchanging the endpoints;
surjectivity follows from the target's same two-coset decomposition.

Source: Aschbacher, *Sporadic Groups* (1994), printed p. 201, Lemma 37.6.
-/

public section

namespace Theory.GroupTheory.GraphUniquenessSystem

/-- The two normal forms define a homomorphism once conjugation and the
square of the nontrivial coset representative are respected. -/
private theorem twoCosetHom {K L : Type*} [Group K] [Group L]
    (B : Subgroup K) (t : K) (u : L) (φ : B →* L)
    (ht : t ∉ B) (htt : t * t ∈ B)
    (hc : ∀ b : B, t * b * t⁻¹ ∈ B)
    (hsq : φ ⟨t * t, htt⟩ = u * u)
    (hconj : ∀ b : B, φ ⟨t * b * t⁻¹, hc b⟩ = u * φ b * u⁻¹)
    (hcases : ∀ g : K, g ∈ B ∨ g * t⁻¹ ∈ B) :
    ∃ f : K →* L, (∀ b : B, f b = φ b) ∧ f t = u := by
  classical
  let f : K → L := fun g => if hg : g ∈ B then φ ⟨g, hg⟩
    else φ ⟨g * t⁻¹, (hcases g).resolve_left hg⟩ * u
  have fb (b : B) : f b = φ b := by simp [f, b.property]
  have fbt (b : B) : f ((b : K) * t) = φ b * u := by
    have hn : (b : K) * t ∉ B := fun h => ht ((B.mul_mem_cancel_left b.property).mp h)
    simp [f, hn]
  have cases' (g : K) : ∃ b : B, g = b ∨ g = (b : K) * t := by
    rcases hcases g with h | h
    · exact ⟨⟨g, h⟩, Or.inl rfl⟩
    · exact ⟨⟨g * t⁻¹, h⟩, Or.inr (by simp)⟩
  have fm (g h : K) : f (g * h) = f g * f h := by
    obtain ⟨b, rfl | rfl⟩ := cases' g <;>
      obtain ⟨c, rfl | rfl⟩ := cases' h
    · exact (fb (b * c)).trans (by rw [map_mul, fb, fb])
    · rw [← mul_assoc]
      change f (((b * c : B) : K) * t) = _
      rw [fbt, fb, fbt, map_mul, mul_assoc]
    · have he : (b : K) * t * c = ((b * ⟨t * c * t⁻¹, hc c⟩ : B) : K) * t := by
        simp [mul_assoc]
      rw [he, fbt, map_mul, hconj, fbt, fb]
      simp [mul_assoc]
    · have he : (b : K) * t * ((c : K) * t) =
          ((b * ⟨t * c * t⁻¹, hc c⟩ * ⟨t * t, htt⟩ : B) : K) := by
        simp [mul_assoc]
      rw [he, fb, map_mul, map_mul, hconj, hsq, fbt, fbt]
      simp [mul_assoc]
  refine ⟨MonoidHom.mk' f fm, fb, ?_⟩
  simpa using fbt 1

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

private theorem edgeHom_of_isEquivalence (hs : s.IsEquivalence) :
    ∃ f : U.edgeSetGroup →* U'.edgeSetGroup,
      (∀ b : U.edgeGroup,
        (f ⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : G') = (s.edgeIso b : G')) ∧
      (∀ (h : U.H) (he : (h : G) ∈ U.edgeSetGroup),
        (f ⟨h, he⟩ : G') = (s.localIso h : G')) := by
  obtain ⟨t, htx, hty, hconj⟩ := hs
  let B := U.edgeGroup.subgroupOf U.edgeSetGroup
  let t₀ : U.edgeSetGroup := ⟨t, Or.inr ⟨htx, hty⟩⟩
  let t₁ : U'.edgeSetGroup := ⟨s.localIso t, (s.local_edge t).mp t₀.property⟩
  let φ : B →* U'.edgeSetGroup :=
    { toFun := fun b => ⟨s.edgeIso ⟨b, b.property⟩,
        U'.edgeGroup_le_edgeSetGroup (s.edgeIso ⟨b, b.property⟩).property⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun b : U'.edgeGroup => (b : G')) s.edgeIso.map_one
      map_mul' := by
        intro b c
        apply Subtype.ext
        exact congrArg (fun b : U'.edgeGroup => (b : G'))
          (s.edgeIso.map_mul ⟨b, b.property⟩ ⟨c, c.property⟩) }
  have ht : t₀ ∉ B := fun h => U.adjacent.ne (h.1.symm.trans htx)
  have htt : t₀ * t₀ ∈ B := by
    exact ⟨by change ((t : G) * t) • U.x = U.x; rw [mul_smul, htx, hty],
      by change ((t : G) * t) • U.y = U.y; rw [mul_smul, hty, htx]⟩
  have hc (b : B) : t₀ * b * t₀⁻¹ ∈ B := U.conj_mem_edgeGroup htx hty b.property
  have hsq : φ ⟨t₀ * t₀, htt⟩ = t₁ * t₁ := by
    apply Subtype.ext
    change (s.edgeIso ⟨(t : G) * t, htt⟩ : G') = _
    rw [s.edgeIso_agree _ (U.H.mul_mem t.property t.property)]
    exact congrArg (fun h : U'.H => (h : G')) (s.localIso.map_mul t t)
  have hconj' (b : B) : φ ⟨t₀ * b * t₀⁻¹, hc b⟩ = t₁ * φ b * t₁⁻¹ := by
    apply Subtype.ext
    exact hconj ⟨b, b.property⟩
  obtain ⟨f, fb, ft⟩ := twoCosetHom B t₀ t₁ φ ht htt hc hsq hconj'
    (fun g => U.edgeSetGroup_cases t htx hty g.property)
  have fe (b : U.edgeGroup) :
      (f ⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : G') = (s.edgeIso b : G') :=
    congrArg (fun g : U'.edgeSetGroup => (g : G'))
      (fb ⟨⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩, b.property⟩)
  refine ⟨f, fe, ?_⟩
  intro h he
  rcases U.edgeSetGroup_cases t htx hty he with hb | hb
  · exact (fe ⟨h, hb⟩).trans (s.edgeIso_agree _ h.property)
  · let b : U.edgeGroup := ⟨(h : G) * (t : G)⁻¹, hb⟩
    have hbH : (b : G) ∈ U.H := U.H.mul_mem h.property (U.H.inv_mem t.property)
    have heq : (⟨h, he⟩ : U.edgeSetGroup) =
        (⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : U.edgeSetGroup) * t₀ := by
      apply Subtype.ext
      simp [b, t₀]
    rw [heq, map_mul, Subgroup.coe_mul, fe, ft, s.edgeIso_agree b hbH]
    change (s.localIso (h * t⁻¹) : G') * (s.localIso t : G') = _
    simp

private theorem edgeHom_bijective (f : U.edgeSetGroup →* U'.edgeSetGroup)
    (fe : ∀ b : U.edgeGroup,
      (f ⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : G') = (s.edgeIso b : G'))
    (fh : ∀ (h : U.H) (he : (h : G) ∈ U.edgeSetGroup),
      (f ⟨h, he⟩ : G') = (s.localIso h : G')) : Function.Bijective f := by
  obtain ⟨t, htx, hty⟩ := U.exists_swap
  obtain ⟨htx', hty'⟩ := s.map_swap t htx hty
  let t₀ : U.edgeSetGroup := ⟨t, Or.inr ⟨htx, hty⟩⟩
  constructor
  · apply (injective_iff_map_eq_one f).mpr
    intro a ha
    rcases U.edgeSetGroup_cases t htx hty a.property with hb | hb
    · have hi : s.edgeIso ⟨a, hb⟩ = 1 := by
        apply Subtype.ext
        exact (fe ⟨a, hb⟩).symm.trans (congrArg (fun g : U'.edgeSetGroup => (g : G')) ha)
      have hi' : (⟨a, hb⟩ : U.edgeGroup) = 1 :=
        s.edgeIso.injective (hi.trans s.edgeIso.map_one.symm)
      exact Subtype.ext (congrArg (fun b : U.edgeGroup => (b : G)) hi')
    · let b : U.edgeGroup := ⟨(a : G) * (t : G)⁻¹, hb⟩
      have heq : a = (⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : U.edgeSetGroup) * t₀ := by
        apply Subtype.ext
        simp [b, t₀]
      have hi : (f a : G') • U'.x = U'.y := by
        rw [heq, map_mul, Subgroup.coe_mul, fe, fh t t₀.property, mul_smul, htx']
        exact (s.edgeIso b).property.2
      rw [ha, Subgroup.coe_one, one_smul] at hi
      exact False.elim (U'.adjacent.ne hi)
  · intro g
    rcases U'.edgeSetGroup_cases (s.localIso t) htx' hty' g.property with hb | hb
    · let b := s.edgeIso.symm ⟨g, hb⟩
      refine ⟨⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩, ?_⟩
      apply Subtype.ext
      exact (fe b).trans (congrArg (fun b : U'.edgeGroup => (b : G'))
        (s.edgeIso.apply_symm_apply ⟨g, hb⟩))
    · let b := s.edgeIso.symm ⟨(g : G') * (s.localIso t : G')⁻¹, hb⟩
      refine ⟨(⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : U.edgeSetGroup) * t₀, ?_⟩
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, fe, fh t t₀.property]
      change (s.edgeIso (s.edgeIso.symm _) : G') * (s.localIso t : G') = _
      simp

/-- Aschbacher 37.6: an equivalence extends to an isomorphism of the
setwise-edge groups, agreeing with both given local isomorphisms. -/
theorem nonempty_amalgamEquiv_of_isEquivalence (hs : s.IsEquivalence) :
    Nonempty s.AmalgamEquiv := by
  obtain ⟨f, fe, fh⟩ := s.edgeHom_of_isEquivalence hs
  exact ⟨{ edgeSetIso := MulEquiv.ofBijective f (s.edgeHom_bijective f fe fh)
           onEdge := fe
           onLocal := fh }⟩

end Similarity
end Theory.GroupTheory.GraphUniquenessSystem
