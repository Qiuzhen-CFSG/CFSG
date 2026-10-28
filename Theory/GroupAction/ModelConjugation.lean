module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugation in a specified group model, with its kernel retained

If T normalizes K and K is identified with a model D by an actual
multiplicative equivalence, transport the conjugation action to Aut(D).
Its kernel, embedded in the ambient group, is exactly T ∩ C_G(K).
An embedded subgroup of D contained in T induces its literal inner image.
Only relative normalization is required; K need not be normal in G.

These elementary transport identities are used when lifting the model
torus calculations in Aschbacher–Smith 13.8.20, printed p.954.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupAction.ModelConjugation
variable {G D : Type*} [Group G] [Group D]

/-- The actual conjugation action transported along the specified model isomorphism. -/
def action (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G))
    (e : K ≃* D) : T →* MulAut D :=
  (MulAut.congr e).toMonoidHom.comp (K.normalizerMonoidHom.comp (inclusion hTK))

/-- The kernel inside T is its centralizer of K. -/
theorem action_ker (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G))
    (e : K ≃* D) : (action T K hTK e).ker = (centralizer (K : Set G)).subgroupOf T := by
  ext t
  change (MulAut.congr e) (K.normalizerMonoidHom (inclusion hTK t)) = 1 ↔
    (t : G) ∈ centralizer (K : Set G)
  rw [← (MulAut.congr e).map_one, (MulAut.congr e).injective.eq_iff]
  change inclusion hTK t ∈ K.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- Embed the kernel back in the original ambient group. -/
theorem action_ker_map (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G))
    (e : K ≃* D) : (action T K hTK e).ker.map T.subtype =
      T ⊓ centralizer (K : Set G) := by
  rw [action_ker, subgroupOf_map_subtype, inf_comm]

/-- Elements of K induce the corresponding inner automorphisms of D. -/
theorem action_conj (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G))
    (e : K ≃* D) (x : K) (hx : (x : G) ∈ T) :
    action T K hTK e ⟨x,hx⟩ = MulAut.conj (e x) := by
  apply MulEquiv.ext
  intro d
  change e (x * e.symm d * x⁻¹) = e x * d * (e x)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

/-- An embedded subgroup contained in T has exactly its inner conjugation image. -/
theorem inner_image (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G))
    (e : K ≃* D) (U : Subgroup D)
    (hUT : U.map (K.subtype.comp e.symm.toMonoidHom) ≤ T) :
    ((U.map (K.subtype.comp e.symm.toMonoidHom)).subgroupOf T).map (action T K hTK e) =
      U.map MulAut.conj := by
  ext α
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨u,hu,htu⟩ := ht
    have hx : (e.symm u : G) ∈ T := hUT ⟨u,hu,rfl⟩
    have ht' : t = ⟨e.symm u,hx⟩ := Subtype.ext htu.symm
    refine ⟨u,hu,?_⟩
    rw [ht', action_conj, e.apply_symm_apply]
  · rintro ⟨u,hu,rfl⟩
    have hx : (e.symm u : G) ∈ T := hUT ⟨u,hu,rfl⟩
    refine ⟨⟨e.symm u,hx⟩, ⟨u,hu,rfl⟩, ?_⟩
    rw [action_conj, e.apply_symm_apply]

end Theory.GroupAction.ModelConjugation
