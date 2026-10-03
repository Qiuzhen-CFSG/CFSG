module

public import Theory.GroupTheory.ElementaryEightIndexTwoNormalizer
public import Theory.GroupTheory.ElementaryEightConjugacyFusion
public import Theory.GroupTheory.SaturatedCentralizerCard
public import Theory.GroupTheory.SaturatedCentralizerTransport

/-!
# No fusion into the core of index-two elementary-eight geometry

An outside involution with the recorded local geometry cannot fuse into the
index-two subgroup. The conjugacy-class normalizer calculation first excludes
fusion to the center of the Sylow subgroup via the elementary-eight automizer.
Every remaining fused involution has Sylow centralizer of order at most 16.
Consequently an inside centralizer of order 16 is Sylow in its ambient element
centralizer. Sylow conjugacy transports the distinguished eight into that
abelian sixteen, contradicting its self-centralizing property.

No ambient simplicity or transfer assumption is used. The transfer assembly
remains `ElementaryEightIndexTwoGeometry.false_of_no_fusion`.

Source: MacWilliams, Trans. AMS 150 (1970), assertions (xxiii)–(xxv) and
the following paragraph, printed pp.384–385,
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace ElementaryEightIndexTwoGeometry

/-- The distinguished involution does not fuse to a central Sylow element. -/
public theorem not_isConj_central
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (z : S) (hz : z ∈ center S) : ¬ IsConj (t : G) (z : G) := by
  let E := centralizer ({t} : Set S)
  let : IsElementaryAbelian 2 E := h.centralizer_elementary
  have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  intro htz
  apply S.not_isConj_of_elementary_eight_normalizer_class z t hz E rfl
    h.centralizer_card ?_ ?_ ?_ htz.symm
  · intro P hp hEP
    simpa only [h1, map_id] using h.conjugate_self_centralizer S 1 P hp
      (by simpa only [h1, map_id] using hEP)
  · intro T hET
    simpa only [h1, map_id] using (h.conjugate_local_profile S 1 T
      (by simpa only [h1, map_id] using hET)).2
  · intro P
    have hh := h.conjugate_normalizer_sylow_bound S 1
    rw [h1, map_id] at hh
    exact hh P

/-- No involution in the index-two core is conjugate to the distinguished
outside involution. This consequence needs no simplicity hypothesis. -/
public theorem no_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t) :
    ∀ u : S, u ∈ R → orderOf u = 2 → ¬ IsConj (t : G) (u : G) := by
  intro u hu huorder htu
  have hnoncentral (v : S) (htv : IsConj (t : G) (v : G)) : v ∉ center S :=
    fun hv => h.not_isConj_central S v hv htv
  obtain ⟨huElem, huCard⟩ := (h.inside_centralizers u hu huorder).resolve_left
    (hnoncentral u htu)
  let E := centralizer ({t} : Set S)
  let U := E.map (S : Subgroup G).subtype
  let A := (centralizer ({u} : Set S)).map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 E := h.centralizer_elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (centralizer ({u} : Set S)) := huElem
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hU : Nat.card U = 8 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective]
    exact h.centralizer_card
  have hA : Nat.card A = 16 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective]
    exact huCard
  have hAC : A ≤ centralizer ({(u : G)} : Set G) := by
    dsimp only [A]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hUC : U ≤ centralizer ({(t : G)} : Set G) := by
    dsimp only [U, E]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  obtain ⟨v, huv, hvmax⟩ := S.exists_conjugate_with_saturated_centralizer u
  have htv := htu.trans huv
  have hvorder : orderOf v = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp huv
    rw [← Subgroup.orderOf_coe, ← hg]
    change orderOf ((MulAut.conj g) (u : G)) = 2
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, huorder]
  have hvcard : Nat.card (centralizer ({v} : Set S)) ≤ 16 := by
    by_cases hvR : v ∈ R
    · have hh := ((h.inside_centralizers v hvR hvorder).resolve_left
        (hnoncentral v htv)).2
      omega
    · rw [h.outside_centralizers v hvR hvorder]
      omega
  let B := (centralizer ({v} : Set S)).map (S : Subgroup G).subtype
  have hBC : B ≤ centralizer ({(v : G)} : Set G) := by
    dsimp only [B]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hB : Nat.card B ≤ 16 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hvcard
  have hmax (V : Subgroup G) (hpV : IsPGroup 2 V) (hAV : A ≤ V)
      (hVC : V ≤ centralizer ({(u : G)} : Set G)) : V = A := by
    have hc := card_le_of_isConj_of_saturated_centralizer (v : G) (u : G)
      huv.symm B ((S.isPGroup'.to_subgroup _).map _) hBC hvmax V hpV hVC
    exact (eq_of_le_of_card_ge hAV (by rw [hA]; exact hc.trans hB)).symm
  obtain ⟨g, _, hg⟩ := exists_conj_into_saturated_centralizer (u : G) (t : G)
    A U (IsElementaryAbelian.isPGroup 2 A) (IsElementaryAbelian.isPGroup 2 U)
    hAC hUC hmax htu
  let F := U.map (MulAut.conj g).toMonoidHom
  have hself : A ⊓ centralizer (F : Set G) = F :=
    h.conjugate_self_centralizer S g A (IsElementaryAbelian.isPGroup 2 A) hg
  have hAF : A ≤ F := by
    rw [← hself]
    exact le_inf le_rfl (A.le_centralizer.trans (centralizer_le hg))
  have hc := card_le_of_le hAF
  have hF : Nat.card F = 8 := (card_map_of_injective (MulAut.conj g).injective).trans hU
  rw [hA, hF] at hc
  omega

end ElementaryEightIndexTwoGeometry
