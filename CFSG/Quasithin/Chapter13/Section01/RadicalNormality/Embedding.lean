module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Locating the intrinsic radical embedding in the original local component

If K is normalized by T, its quotient in KT is a two-group. Every detected
perfect C-component therefore lies in K and equals K by component uniqueness.
The proved intrinsic embedding theorem then reduces a nonnormal radical with
noncyclic T-automizer to a quasisimple linear-three quotient. Its actual Sylow
plane embeds in that quotient, giving the divisibility by p².

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
the nonnormal-embedding step in Lemma 13.1.4, p.867, using Theorem 1.3.4.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.XiEmbedding
namespace CFSG.Quasithin.Chapter13.Section01.RadicalNormality
variable {G : Type*} [Group G] [Finite G]

private theorem detected_eq {T K D : Subgroup G} (hK : K ∈ L G T)
    (hTK : T ≤ normalizer (K : Set G))
    (hD : D ∈ cComponentsIn (K ⊔ T)) : D = K := by
  let H := K ⊔ T
  have hKH : K ≤ H := le_sup_left
  let N := K.subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  have hgen : N ⊔ T.subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le (show T ≤ H from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 (H ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    (T.subgroupOf H) (isSylowIn_iff.mp hK.2.1).1.comap_subtype hgen
  let : Group.IsNilpotent (H ⧸ N) := hp.isNilpotent
  let : Group.IsPerfect (D.subgroupOf H) := hD.2.perfect
  have hDN : D.subgroupOf H ≤ N := le_of_isPerfect_of_solvable_quotient _ _
  have he := hD.2.eq_of_le hK.1 hDN
  have hm := congrArg (map H.subtype) he
  change (D.subgroupOf H).map H.subtype = (K.subgroupOf H).map H.subtype at hm
  rw [map_subgroupOf_eq_of_le hD.1, map_subgroupOf_eq_of_le hKH] at hm
  exact hm


/-- The actual local join has only the linear-three alternative when p > 3
and the T-automizer is noncyclic. The quotient and its Sylow-plane embedding
are those of the original K, not an independently selected model. -/
theorem normal_or_linear_three {p : ℕ} {T K X P : Subgroup G}
    (hK : K ∈ L G T) (hTK : T ≤ normalizer (K : Set G))
    (hXK : X ≤ K) (h : LocalInput p T X P (K ⊔ T))
    (hH : IsSQTK KnownSimple.IsKnownSimple (K ⊔ T : Subgroup G))
    (hp3 : 3 < p) (hcyc : ¬ IsCyclic (automizer T P)) :
    (X.subgroupOf K).Normal ∨
      IsQuasisimple (XiQuotient K) ∧ LinearThreeModel p (XiQuotient K) ∧
      p ^ 2 ∣ Nat.card (XiQuotient K) := by
  rcases h.adequate_knownSimple hH hK.2.1 with hn | ⟨D, hD, hq, _, ha⟩
  · exact Or.inl (normal_subgroupOf_of_le_normalizer
      (le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
        (hXK.trans le_sup_left)).mp hn)))
  have he := detected_eq hK hTK hD
  subst D
  rcases ha with ⟨⟨e⟩, hs | ⟨_, hl | hs | hp⟩⟩ | hp
  · exact (hs.1.1 hTK).elim
  · refine Or.inr ⟨hq, hl, ?_⟩
    have hPL : P ≤ K := ((isSylowIn_iff.mp h.sylow).2.1).trans hXK
    have hd := card_dvd_of_injective (InvariantLarge.componentMap hPL)
      (InvariantLarge.componentMap_injective (isSylowIn_iff.mp h.sylow).1 h.odd hPL)
    rw [Nat.card_congr e.toEquiv, plane_card] at hd
    exact hd
  · exact (hcyc hs.2).elim
  · have hh := hp.1
    omega
  · have hh := hp.1
    omega

end CFSG.Quasithin.Chapter13.Section01.RadicalNormality
