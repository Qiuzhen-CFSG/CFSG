module
public import Theory.GroupAction.NormalizerFrattiniRestriction

/-!
# Frattini irreducibility from an invariant subgroup interval

An actor normalizing a subgroup acts irreducibly on its Frattini quotient
when the interval from the embedded Frattini subgroup to the subgroup has
no proper actor-invariant member. Restriction to any containing group
retains the literal subgroup inclusion and Frattini quotient.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A chief Frattini interval gives irreducibility under the full relative
normalizer, with the subgroup and its quotient map unchanged. -/
theorem normalizerFrattiniIrreducible_subgroupOf_of_interval
    (P H : Subgroup G) (hPH : P ≤ H) (hn : H ≤ normalizer (P : Set G))
    (hmin : ∀ N : Subgroup G, (frattini P).map P.subtype ≤ N → N ≤ P →
      H ≤ normalizer (N : Set G) → N = (frattini P).map P.subtype ∨ N = P) :
    IsNormalizerFrattiniIrreducible (P.subgroupOf H) := by
  apply normalizerFrattiniIrreducible_subgroupOf P H H hPH le_rfl hn
  intro A hA
  let q := QuotientGroup.mk' (frattini P)
  let N := (A.comap q).map P.subtype
  have hNP : N ≤ P := map_subtype_le _
  have hPhi : (frattini P).map P.subtype ≤ N := by
    apply map_mono
    intro x hx
    change q x ∈ A
    have he : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]
    exact A.one_mem
  have hconj (s : H) (x : G) (hx : x ∈ N) : (s : G) * x * (s : G)⁻¹ ∈ N := by
    obtain ⟨p,hp,rfl⟩ := hx
    let y : P := ⟨(s : G) * (p : G) * (s : G)⁻¹,
      (mem_normalizer_iff.mp (hn s.property) p).mp p.property⟩
    refine ⟨y,?_,rfl⟩
    change q y ∈ A
    let _ := conjMulDistribMulActionOfLeNormalizer H P hn
    have hi := hA s (q p) hp
    change frattiniConjugationHom H P hn s (QuotientGroup.mk' _ p) ∈ A at hi
    simp only [frattiniConjugationHom,MonoidHom.comp_apply,quotientAut_apply_mk] at hi
    convert hi using 1
    congr 1

  have hHN : H ≤ normalizer (N : Set G) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · exact hconj ⟨s,hs⟩ x
    · intro hx
      simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using
        hconj (⟨s,hs⟩ : H)⁻¹ (s*x*s⁻¹) hx
  have hcomap : N.comap P.subtype = A.comap q :=
    comap_map_eq_self_of_injective P.subtype_injective _
  have hmap : (A.comap q).map q = A :=
    map_comap_eq_self_of_surjective (f := q) (QuotientGroup.mk'_surjective _) A
  rcases hmin N hPhi hNP hHN with hz | ht
  · left
    have he : A.comap q = frattini P := by
      rw [←hcomap,hz,comap_map_eq_self_of_injective P.subtype_injective]
    rw [←hmap,he]
    exact (map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  · right
    have he : A.comap q = ⊤ := by
      rw [←hcomap,ht]
      ext x
      simp only [mem_comap,mem_top,iff_true]
      exact x.property
    rw [←hmap,he]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective _)

end Subgroup
