module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.Intersection
public import Theory.GroupTheory.PPerfectHom
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.CoreNormalization.Models

/-!
# The local two-core normalizes the component in 15.3.12

Let `B = Y_L = O²(Y₊ ∩ L)` and `R = O₂(Y₊S)`. If `r ∈ R` moves `L`,
1.2.1(2) makes the two component images commute modulo `O₂(I)`, and the
actual models in 1.2.1(3) make the image of `L` centerless. Conjugation by
`[b,r]` on that image agrees with conjugation by `b`. Thus the action image
of `B` is a two-group, since `[B,R]` is a two-group. Two-perfectness kills
this action, and the trivial center forces `B` into `O₂(I)`. A two-perfect
two-group is trivial, contrary to the supplied nontriviality of `Y_L`.

The final theorem retains component membership and normality inside `I`.
Its structural inputs are the literal conclusions of 1.2.1(2)–(3), with
actual quotient carriers and model isomorphisms. The rank hypotheses of
15.3.12 enter through the nontriviality input, proved in `OddRank.Intersection`;
the enclosing source owner supplies that input and the Chapter 1 facts.
No exponent hypothesis on `Y₊` is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 15.3.12(1),
printed pp.1124–1125 (PDF pp.1141–1142), using Proposition 1.2.1(2)–(3), p.504.
-/

public section

open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

/-- When the conjugate commutes with a centerless subgroup, its two-perfect
subgroup cannot have a two-group commutator with the conjugating group. -/
private theorem eq_bot_of_commuting_conjugate {G : Type*} [Group G] {L B R : Subgroup G}
    (hBL : B ≤ L) (hB : IsPPerfect 2 B)
    (hp : IsPGroup 2 (⁅B, R⁆ : Subgroup G))
    (hz : center L = ⊥) {r : G} (hr : r ∈ R)
    (hc : L.map (MulAut.conj r).toMonoidHom ≤ centralizer (L : Set G)) :
    B = ⊥ := by
  let f : B →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion (hBL.trans L.le_normalizer))
  let Q := (⁅B, R⁆ : Subgroup G).subgroupOf (normalizer (L : Set G))
  have hpQ : IsPGroup 2 Q := hp.comap_subtype
  have hf : f.range ≤ Q.map L.normalizerMonoidHom := by
    rintro _ ⟨b, rfl⟩
    have hbc : r * (b : G)⁻¹ * r⁻¹ ∈ centralizer (L : Set G) :=
      hc (mem_map.mpr ⟨(b : G)⁻¹, L.inv_mem (hBL b.property), rfl⟩)
    have hn : ⁅(b : G), r⁆ ∈ normalizer (L : Set G) := by
      change (b : G) * r * (b : G)⁻¹ * r⁻¹ ∈ _
      rw [show (b : G) * r * (b : G)⁻¹ * r⁻¹ =
        (b : G) * (r * (b : G)⁻¹ * r⁻¹) by group]
      exact (normalizer (L : Set G)).mul_mem (L.le_normalizer (hBL b.property))
        (Subgroup.centralizer_le_normalizer _ hbc)
    refine mem_map.mpr ⟨⟨⁅(b : G), r⁆, hn⟩, ?_, ?_⟩
    · exact commutator_mem_commutator b.property hr
    · ext x
      change ⁅(b : G), r⁆ * (x : G) * ⁅(b : G), r⁆⁻¹ =
        (b : G) * (x : G) * (b : G)⁻¹
      have hx := hbc (x : G) x.property
      change (x : G) * (r * (b : G)⁻¹ * r⁻¹) =
        (r * (b : G)⁻¹ * r⁻¹) * (x : G) at hx
      simp only [commutatorElement_def]
      calc
        _ = (b : G) * ((r * (b : G)⁻¹ * r⁻¹) * (x : G)) *
              (r * (b : G)⁻¹ * r⁻¹)⁻¹ * (b : G)⁻¹ := by group
        _ = _ := by rw [← hx]; group
  have hpF : IsPGroup 2 f.range := (hpQ.map _).to_le hf
  have he := hB.hom_eq_one_of_isPGroup hpF f.rangeRestrict
  apply eq_bot_iff.mpr
  intro b hb
  have hbauto : f ⟨b,hb⟩ = 1 := by
    simpa only [MonoidHom.coe_rangeRestrict, MonoidHom.one_apply, Subgroup.coe_one] using
      congrArg (fun a : f.range => (a : MulAut L)) (DFunLike.congr_fun he (⟨b,hb⟩ : B))
  have hbc : (⟨b, hBL hb⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hh := congrArg (fun a : MulAut L => (a x : G)) hbauto
    change b * (x : G) * b⁻¹ = (x : G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact show b = 1 from congrArg (fun x : L => (x : G)) (mem_bot.mp (hz ▸ hbc))

private theorem eq_bot_of_twoPerfect_twoGroup {G : Type*} [Group G] {B : Subgroup G}
    (hB : IsPPerfect 2 B) (hp : IsPGroup 2 B) : B = ⊥ := by
  have h := hB.hom_eq_one_of_isPGroup hp (MonoidHom.id B)
  apply eq_bot_iff.mpr
  intro b hb
  exact congrArg (fun x : B => (x : G)) (DFunLike.congr_fun h (⟨b,hb⟩ : B))

open CFSG.Quasithin.Chapter1.Section02

private theorem normalizes_of_quotient_centerless {G : Type*} [Group G] [Finite G]
    {L B R : Subgroup G} (hL : L.IsCComponent)
    (hBL : B ≤ L) (hB : IsPPerfect 2 B) (hBne : B ≠ ⊥)
    (hp : IsPGroup 2 (⁅B, R⁆ : Subgroup G))
    (hcomm : ∀ K : Subgroup G, K.IsCComponent → K ≠ L → ⁅L, K⁆ ≤ pCore 2 G)
    (hz : center (L.map (QuotientGroup.mk' (pCore 2 G))) = ⊥) :
    R ≤ normalizer (L : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let Lq := L.map q
  let Bq := B.map q
  let Rq := R.map q
  have hBq : IsPPerfect 2 Bq := hB.of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  have hpq : IsPGroup 2 (⁅Bq, Rq⁆ : Subgroup (G ⧸ pCore 2 G)) := by
    change IsPGroup 2 (⁅B.map q, R.map q⁆ : Subgroup _)
    rw [← map_commutator]
    exact hp.map q
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let K := L.map (MulAut.conj r).toMonoidHom
  have hc := hcomm K (hL.map_equiv (MulAut.conj r)) hne
  have hconj : K.map q = Lq.map (MulAut.conj (q r)).toMonoidHom := by
    have he : q.comp (MulAut.conj r).toMonoidHom =
        (MulAut.conj (q r)).toMonoidHom.comp q := by ext; simp [q]
    change (L.map (MulAut.conj r).toMonoidHom).map q = _
    rw [map_map, he, ← map_map]
  have hzero : ⁅Lq, Lq.map (MulAut.conj (q r)).toMonoidHom⁆ = ⊥ := by
    rw [← hconj]
    change ⁅L.map q, K.map q⁆ = ⊥
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc
  have hBzero : Bq = ⊥ := eq_bot_of_commuting_conjugate (map_mono hBL) hBq hpq hz
    (mem_map_of_mem q hr) (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm _ _).trans hzero))
  have hBcore : B ≤ pCore 2 G := by
    have hh := (Subgroup.map_eq_bot_iff B (f := q)).mp hBzero
    simpa only [q, QuotientGroup.ker_mk'] using hh
  exact hBne (eq_bot_of_twoPerfect_twoGroup hB (pCore_isPGroup.to_le hBcore))

private theorem normalizes_of_component_facts {G : Type*} [Group G] [Finite G]
    {L B R : Subgroup G} (hL : L.IsCComponent)
    (hBL : B ≤ L) (hB : IsPPerfect 2 B) (hBne : B ≠ ⊥)
    (hp : IsPGroup 2 (⁅B, R⁆ : Subgroup G))
    (hcomm : ∀ K : Subgroup G, K.IsCComponent → K ≠ L →
      ⁅L, K⁆ ≤ L.pCoreIn 2 ⊓ K.pCoreIn 2 ∧
        L.pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 G)
    (hstructure : L.Normal ∨ (normalizer (L : Set G)).index = 2 ∧
      NonnormalCComponentModel (L ⧸ pCore 2 L)) :
    R ≤ normalizer (L : Set G) := by
  rcases hstructure with hn | ⟨_, hm⟩
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · let := pCore_isNilpotent (p := 2) (G := G)
    have hLq := hL.map_quotient (pCore 2 G)
    have hm' := hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL).symm
    exact normalizes_of_quotient_centerless hL hBL hB hBne hp
      (fun K hK hne => (hcomm K hK hne).1.trans (hcomm K hK hne).2)
      (CoreNormalization.nonnormalModel_center_eq_bot
        hm' hLq.not_isSolvable)

/-- The core-normalization clause of 15.3.12(1), conditional on the earlier
component structure and nontriviality of the actual intersection residual.
The component normality and all Chapter 1 hypotheses are relative to `I`. -/
theorem localCore_le_normalizer_of_component_facts {G : Type*} [Group G] [Finite G] {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsCComponent)
    (hcomm : ∀ K : Subgroup I, K.IsCComponent → K ≠ L.subgroupOf I →
      ⁅L.subgroupOf I, K⁆ ≤ (L.subgroupOf I).pCoreIn 2 ⊓ K.pCoreIn 2 ∧
        (L.subgroupOf I).pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 I)
    (hstructure : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        NonnormalCComponentModel ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hne : intersectionResidual Y L ≠ ⊥) :
    localCore Y S ≤ normalizer (L : Set G) := by
  let B := intersectionResidual Y L
  let R := localCore Y S
  have hBI : B ≤ I := ((intersectionResidual_le Y L).trans inf_le_right).trans hLI
  have hRI : R ≤ I := ((Y ⊔ S).pCoreIn_le 2).trans hI.1.2
  have hBperfect : IsPPerfect 2 (B.subgroupOf I) :=
    (intersectionResidual_isPPerfect Y L).of_surjective
      (subgroupOfEquivOfLe hBI).symm.toMonoidHom (subgroupOfEquivOfLe hBI).symm.surjective
  have hBne : B.subgroupOf I ≠ ⊥ := by
    intro h
    apply hne
    have hh := congrArg (map I.subtype) h
    simpa only [map_subgroupOf_eq_of_le hBI, Subgroup.map_bot] using hh
  have hp : IsPGroup 2 (⁅B.subgroupOf I, R.subgroupOf I⁆ : Subgroup I) := by
    have hh : ⁅B.subgroupOf I, R.subgroupOf I⁆ ≤ R.subgroupOf I := by
      apply (map_le_map_iff_of_injective I.subtype_injective).mp
      rw [map_commutator,
        map_subgroupOf_eq_of_le hBI, map_subgroupOf_eq_of_le hRI]
      exact commutator_intersectionResidual_localCore_le Y S L
    exact (((Y ⊔ S).isPGroup_pCoreIn 2).comap_subtype).to_le hh
  have hn := normalizes_of_component_facts hL
    (comap_mono ((intersectionResidual_le Y L).trans inf_le_right))
    hBperfect hBne hp hcomm hstructure
  rw [← subgroupOf_normalizer_eq hLI] at hn
  intro r hr
  exact hn (show (⟨r, hRI hr⟩ : I) ∈ R.subgroupOf I from hr)

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
