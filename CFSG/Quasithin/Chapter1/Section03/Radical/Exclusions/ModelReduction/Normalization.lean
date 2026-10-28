module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Factors
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Normalization by the actual two-core of XT

In the swapped case each odd factor P ∩ K has order p. Its nontrivial
image in the simple quotient K/O₂(K) forces every element of H centralizing
P to normalize K: a moved component would commute with K and place that
image in its trivial center. Normalizers lift through the two-core quotient.

Write T = O₂(X)N_T(P). For R = O₂(XT), the factor in R ∩ N_T(P)
centralizes P by coprimality, while O₂(X) normalizes K through the component
layer. Thus R normalizes K in the swapped case as well as the invariant
case. This discharges normalization, without any pushing-up model input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.513–514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding
variable {G : Type*} [Group G] [Finite G]

private theorem center_bot {D : Type*} [Group D] [Group.IsPerfect D]
    [IsSimpleGroup D] : center D = ⊥ := by
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hz | hz
  · exact hz
  · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp hz)).elim

omit [Finite G] in
private theorem fixed_nonidentity_normalizes {K : Subgroup G}
    (hK : IsComponent G K) (hz : center K = ⊥) {x g : G}
    (hx : x ∈ K) (hne : x ≠ 1) (hg : Commute g x) : g ∈ normalizer K := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := hK.commutator_eq_bot_of_ne (hK.map_conj g) (Ne.symm he)
  have hf : MulAut.conj g x = x := by
    change g * x * g⁻¹ = x
    rw [hg.eq]
    simp
  have hxg : x ∈ K.map (MulAut.conj g).toMonoidHom :=
    hf ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  have hxc : (⟨x, hx⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hc) y.property) x hxg).symm
  have hxx : (⟨x, hx⟩ : K) = 1 := mem_bot.mp (hz ▸ hxc)
  exact hne (congrArg ((↑) : K → G) hxx)

private theorem centralizer_odd_le_normalizer {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G} (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hs : IsSimpleGroup (K ⧸ pCore 2 K))
    (hp : Odd p) (hA : IsPGroup p A) (hne : A ≠ ⊥) (hAK : A ≤ K) :
    centralizer (A : Set G) ≤ normalizer K := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let e := cComponentTwoCoreQuotientEquiv hK
  let _ := hs
  let _ := hq
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨hK.subnormal.quotient, IsQuasisimple.of_mulEquiv e⟩
  let _ : IsSimpleGroup B := e.symm.isSimpleGroup
  let _ := hB.2
  have hAB : Disjoint A (pCore 2 G) :=
    hA.disjoint_of_coprime pCore_isPGroup (Nat.coprime_two_right.mpr hp)
  let _ : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  obtain ⟨x, hx, hx1⟩ := A.exists_ne_one_of_nontrivial
  intro g hg
  rw [← normalizer_cComponent_quotient hK (pCore 2 G)]
  change q g ∈ normalizer B
  have hxq : q x ≠ 1 := by
    intro he
    have hxc : x ∈ pCore 2 G := (QuotientGroup.eq_one_iff x).mp he
    exact hx1 (hAB.le_bot ⟨hx, hxc⟩)
  exact fixed_nonidentity_normalizes hB (center_bot (D := B))
    (mem_map_of_mem q (hAK hx)) hxq
    ((show Commute g x from (mem_centralizer_iff.mp hg x hx).symm).map q)


private theorem simple_of_linear_model {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) {q : ℕ} (hm : ClassicalGroup.IsPSL Q 2 q) :
    IsSimpleGroup Q := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  let _ := hq
  let _ : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hs : IsSimpleGroup PSL(2, F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  exact e.isSimpleGroup_congr.mpr hs

/-- Every rank-one quotient in the swapped alternative is simple.
Perfectness rules out the small nonsimple projective groups. -/
theorem swappedModel_simple {Q : Type*} [Group Q] {p : ℕ}
    (hq : IsQuasisimple Q) (hm : SwappedModel p Q) : IsSimpleGroup Q := by
  rcases hm with ⟨n, _, _, hm⟩ | ⟨q, _, _, hm⟩
  · exact simple_of_linear_model hq hm
  · exact simple_of_linear_model hq hm

/-- Centralizing P fixes the selected swapped component, through its
nontrivial odd intersection and its actual simple core quotient. -/
theorem ComponentCandidate.centralizer_normalizes_of_swapped
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K)
    (hswap : SwappedFactors T P K) (hm : SwappedModel p (XiQuotient K)) :
    H₀ ⊓ centralizer (P : Set G) ≤ normalizer K := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  let A := (P ⊓ K).subgroupOf H₀
  let B := K.subgroupOf H₀
  have hAH : P ⊓ K ≤ H₀ := inf_le_right.trans h.component.1
  let e := (subgroupOfEquivOfLe h.component.1).symm
  let eqv := QuotientGroup.congr (pCore 2 K) (pCore 2 B) e (pCore_map_iso 2 e)
  let _ := h.quasisimple
  have hq : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqv
  have hs : IsSimpleGroup (B ⧸ pCore 2 B) := eqv.isSimpleGroup_congr.mp
    (swappedModel_simple h.quasisimple hm)
  have ha : A ≠ ⊥ := by
    intro ha
    have hac : Nat.card A = 1 := by rw [ha]; exact Subgroup.card_bot
    have he := Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv
    have hc := swapped_intersection_card h.alternatives.1 hswap
    have hp := h.local_input.prime.one_lt
    change Nat.card A = Nat.card (P ⊓ K : Subgroup G) at he
    omega
  have hnorm := centralizer_odd_le_normalizer h.component.2 hq hs
    h.local_input.odd (h.local_input.odd_complement.isPGroup.to_le inf_le_left).comap_subtype
    ha (comap_mono inf_le_right)
  intro g hg
  have hc : (⟨g, hg.1⟩ : H₀) ∈ centralizer (A : Set H₀) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    exact Subtype.ext ((mem_centralizer_iff.mp hg.2) a ha.1)
  have hn := B.le_normalizer_map H₀.subtype (mem_map_of_mem H₀.subtype (hnorm hc))
  simpa only [B, map_subgroupOf_eq_of_le h.component.1, Subgroup.subtype_apply] using hn

/-- The Frattini factorization of T reduces normalization by O₂(XT)
to normalization by the centralizer of P. -/
theorem ComponentCandidate.radical_normalizes_of_centralizer
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K)
    (hc : H₀ ⊓ centralizer (P : Set G) ≤ normalizer K) :
    (X ⊔ T).pCoreIn 2 ≤ normalizer K := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  let R := (X ⊔ T).pCoreIn 2
  have hRH : R ≤ H₀ := (pCoreIn_le 2 _).trans h.local_input.overgroup
  have hRT : R ≤ T := by
    obtain ⟨S, hS⟩ := h.sylow_two.restrict le_sup_right h.local_input.overgroup
    exact hS ▸ pCoreIn_le_sylow (X ⊔ T) S
  have hCR : X.pCoreIn 2 ≤ R := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le X.le_normalizer h.local_input.invariant)
  have hPR : P ≤ normalizer R :=
    (h.local_input.complement_le.trans le_sup_left).trans
      ((X ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (X ⊔ T) (pCore 2 (X ⊔ T : Subgroup G))))
  have hdis : Disjoint R P := (isPGroup_pCoreIn 2 (X ⊔ T)).disjoint_of_coprime
    h.local_input.odd_complement.isPGroup (Nat.coprime_two_left.mpr h.local_input.odd)
  have hcentral : R ⊓ normalizer P ≤ centralizer (P : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply hdis.le_bot.trans' (le_inf ?_ ?_)
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hPR)
    · exact le_normalizer_iff_commutator_le_right.mp inf_le_right
  have hfactor : (X.pCoreIn 2 : Set G) *
      ((T ⊓ normalizer P : Subgroup G) : Set G) = T := by
    have hn : T ⊓ normalizer P ≤ normalizer (X.pCoreIn 2 : Set G) :=
      inf_le_left.trans (h.local_input.invariant.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn, ← h.local_input.normalizer_factor]
  intro r hr
  have hrT : r ∈ (T : Set G) := hRT hr
  rw [← hfactor] at hrT
  obtain ⟨c, hcX, s, hs, he⟩ := hrT
  have hsR : s ∈ R := by
    have hh := R.mul_mem (R.inv_mem (hCR hcX)) hr
    rwa [← he, inv_mul_cancel_left] at hh
  rw [← he]
  exact (normalizer (K : Set G)).mul_mem
    (h.xi_normalizes (pCoreIn_le 2 X hcX))
    (hc ⟨hRH hsR, hcentral ⟨hsR, hs.2⟩⟩)

/-- The two-core R normalizes the component in both surviving alternatives. -/
theorem ComponentCandidate.radical_normalizes
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K) :
    (X ⊔ T).pCoreIn 2 ≤ normalizer K := by
  rcases h.alternatives.2 with ⟨hs, hm⟩ | ⟨ht, _⟩
  · exact h.radical_normalizes_of_centralizer (h.centralizer_normalizes_of_swapped hs hm)
  · exact h.radical_normalizes_of_invariant ht

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
