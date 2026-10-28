module

public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Frattini
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Normalizer actions on Frattini quotients

Conjugation by the actual normalizer induces an action on P/Φ(P). If that
action is irreducible, the image of an invariant subgroup is either trivial
or surjective. Frattini nongeneration turns the latter case into equality.
The ambient version retains the image of Φ(P) under P's subtype inclusion.

This is the invariant-kernel step used in Aschbacher–Smith, *The
Classification of Quasithin Groups*, A.1.32, printed pp.28–29.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Conjugation by a normalizing subgroup on the actual Frattini quotient. -/
@[expose] public def frattiniConjugationHom (S R : Subgroup G) (hn : S ≤ normalizer (R : Set G)) :
    S →* MulAut (R ⧸ frattini R) :=
  let _ := conjMulDistribMulActionOfLeNormalizer S R hn
  (quotientAut (frattini R)).comp (MulDistribMulAction.toMulAut S R)

/-- The full normalizer has no proper nontrivial invariant subgroup on P/Φ(P). -/
@[expose] public def IsNormalizerFrattiniIrreducible (P : Subgroup G) : Prop :=
  ∀ A : Subgroup (P ⧸ frattini P),
    (∀ s : normalizer (P : Set G), ∀ a ∈ A,
      frattiniConjugationHom (normalizer (P : Set G)) P le_rfl s a ∈ A) → A = ⊥ ∨ A = ⊤

/-- An invariant subgroup is contained in the Frattini subgroup or is the whole group. -/
public theorem IsNormalizerFrattiniIrreducible.invariant_le_frattini_or_eq [Finite G] {P : Subgroup G}
    (hirr : IsNormalizerFrattiniIrreducible P) (D : Subgroup P)
    (hD : ∀ s : normalizer (P : Set G), ∀ d ∈ D,
      (⟨(s : G) * (d : G) * (s : G)⁻¹,
        (mem_normalizer_iff.mp s.property (d : G)).mp d.property⟩ : P) ∈ D) :
    D ≤ frattini P ∨ D = ⊤ := by
  let q := QuotientGroup.mk' (frattini P)
  have hinv : ∀ s : normalizer (P : Set G), ∀ a ∈ D.map q,
      frattiniConjugationHom (normalizer (P : Set G)) P le_rfl s a ∈ D.map q := by
    rintro s a ⟨d, hd, rfl⟩
    refine ⟨_, hD s d hd, ?_⟩
    let _ := conjMulDistribMulActionOfLeNormalizer (normalizer (P : Set G)) P le_rfl
    exact (quotientAut_apply_mk (frattini P)
      (MulDistribMulAction.toMulAut (normalizer (P : Set G)) P s) d).symm
  rcases hirr (D.map q) hinv with hb | ht
  · left
    simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp hb
  · right
    apply frattini_nongenerating
    have hh := congrArg (Subgroup.comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh

/-- The ambient placement of a normal subgroup of an irreducible Frattini actor. -/
public theorem IsNormalizerFrattiniIrreducible.normal_le_frattini_or_eq [Finite G] {P R : Subgroup G} [R.Normal]
    (hirr : IsNormalizerFrattiniIrreducible P) (hRP : R ≤ P) :
    R ≤ (frattini P).map P.subtype ∨ R = P := by
  have h := hirr.invariant_le_frattini_or_eq (R.subgroupOf P) (by
    intro s d hd
    exact (inferInstance : R.Normal).conj_mem d hd s)
  rcases h with h | h
  · left
    rw [← map_subgroupOf_eq_of_le hRP]
    exact map_mono h
  · right
    have hm := congrArg (Subgroup.map P.subtype) h
    simpa only [map_subgroupOf_eq_of_le hRP, ← MonoidHom.range_eq_map, range_subtype] using hm

end Subgroup
