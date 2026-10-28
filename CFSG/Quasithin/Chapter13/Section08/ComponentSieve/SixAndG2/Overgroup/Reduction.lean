module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Overgroup

/-!
# The literal containing-component reduction for 13.8.27(2)

The earlier uniform component reductions give the three actual surviving
quotients. The normal two-subgroup constructs G₁ ∈ Hz, and 1.2.4 constructs
K₁ with its relative normality and its A.3.12 embedding of the literal images
in G₁/O₂(G₁). The smaller image may still have a two-core: its quotient,
not that image itself, has the prescribed model.

Equality of those images lifts to equality of the components because the
ambient two-core lies in T ≤ H. Thus the only additional input to the final
conditional deduction is separation of the three models in the constrained
A.3.12 list. This module does not assert that separation, or exclude abstract
A₆ embeddings in A₈. The source assembly must discharge `SurvivorRigidity`.

Source: Aschbacher–Smith, 13.8.27(2), printed p.963, PDF p.980.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open AlternatingAndLinear.LinearReduction.Overgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Actual carriers in the surviving list; the G₂ carrier is its derived subgroup. -/
@[expose] def Survivor (X : Type u) [Group X] : Prop :=
  IsAlternating X 6 ∨ ClassicalGroup.IsPSL X 4 2 ∨
    Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))

theorem Survivor.of_equiv {X Y : Type u} [Group X] [Group Y]
    (h : Survivor X) (e : X ≃* Y) : Survivor Y := by
  rcases h with h | h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (Or.inl (h.of_mulEquiv e.symm))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr ⟨e.symm.trans f⟩)

/-- This is a constrained A.3.12 calculation, not an arbitrary embedding claim.
Its proof is an independent prerequisite of the final source assembly. -/
@[expose] def SurvivorRigidity : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (B C : Subgroup X), B ≤ C →
    A312Embedding B C → Survivor (B ⧸ pCore 2 B) → Survivor C → B = C

omit [Finite G] in
/-- The precise earlier uniform reductions supply the surviving list. -/
theorem surviving_quotient {L L₁ T G₁ M J C : Subgroup G}
    (facts : UniformComponentFacts L L₁ T G₁ M)
    (hJ : J ∈ Source.Hz L₁ T G₁ M) (hCJ : C ≤ J)
    (hC : (C.subgroupOf J).IsCComponent) : Survivor (C ⧸ pCore 2 C) := by
  rcases facts.componentList hJ hCJ hC with ⟨n, hn3, hn5, hn⟩ | ha6 | ha7 | hg2
  · obtain ⟨rfl, _, _⟩ := facts.binaryReduction hJ hCJ hC hn3 hn5 hn
    exact Or.inr (Or.inl hn)
  · exact Or.inl ha6
  · exact (facts.not_A7 hJ hCJ hC ha7).elim
  · exact Or.inr (Or.inr hg2)

private noncomputable def imageTwoCoreEquiv (B : Subgroup G) :
    (B ⧸ pCore 2 B) ≃*
      ((B.map (QuotientGroup.mk' (pCore 2 G))) ⧸
        pCore 2 (B.map (QuotientGroup.mk' (pCore 2 G)))) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let b := q.subgroupMap B
  have hb : Function.Surjective b := q.subgroupMap_surjective B
  have hk : IsPGroup 2 b.ker := by
    dsimp [b, q]
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  let f := (QuotientGroup.mk' (pCore 2 (B.map q))).comp b
  have hf : f.ker = pCore 2 B := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact b.comap_pCore_of_ker_isPGroup hb hk
  exact (QuotientGroup.quotientMulEquivOfEq hf.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk'_surjective _).comp hb))

/-- Quotienting the smaller literal star image removes exactly its two-core. -/
noncomputable def quotientStarQuotientEquiv {J B : Subgroup G} (hBJ : B ≤ J) :
    (B ⧸ pCore 2 B) ≃*
      (Source.starImage J B ⧸ pCore 2 (Source.starImage J B)) :=
  let e := (subgroupOfEquivOfLe hBJ).symm
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (imageTwoCoreEquiv (B.subgroupOf J))

omit [Finite G] in
/-- The source two-subgroup puts the whole normalizer in the same family Hz. -/
theorem ambient_mem_Hz {L₁ G₁ M H P : Subgroup G} {T : Sylow 2 G}
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ (T : Subgroup G))
    (hPn : G₁ ≤ normalizer (P : Set G)) :
    G₁ ∈ Source.Hz L₁ (T : Subgroup G) G₁ M := by
  apply Components.mem_Hz_of_normal_two_subgroup L₁ (T : Subgroup G) G₁ M P _
    hP hp hPbase hPn (hH.1.2.trans hH.2.1) le_rfl
  exact fun he => hH.2.2 (hH.2.1.trans he)

/-- Construct the actual A.3.12 pair with both surviving models. No containing
component, ambient normality or equality of overgroups is assumed. -/
theorem exists_surviving_overcomponent {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    {L L₁ G₁ M H K P : Subgroup G} {T : Sylow 2 G}
    (facts : UniformComponentFacts L L₁ (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ (T : Subgroup G))
    (hPn : G₁ ≤ normalizer (P : Set G))
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    ∃ K₁ : Subgroup G, K₁ ≤ G₁ ∧ (K₁.subgroupOf G₁).IsCComponent ∧ K ≤ K₁ ∧
      (K₁.subgroupOf G₁).Normal ∧
      A312Embedding (Source.starImage G₁ K) (Source.starImage G₁ K₁) ∧
      Survivor (Source.starImage G₁ K ⧸ pCore 2 (Source.starImage G₁ K)) ∧
      Survivor (Source.starImage G₁ K₁) ∧ G₁ = K₁ ⊔ (T : Subgroup G) := by
  have hG := ambient_mem_Hz hH hP hp hPbase hPn
  obtain ⟨K₁, hK₁G, hK₁, hKK₁, hn, he⟩ :=
    exists_component_overgroup earlier hH hKH hK (facts.normal hH hKH hK) hQ
  exact ⟨K₁, hK₁G, hK₁, hKK₁, hn, he,
    (surviving_quotient facts hH hKH hK).of_equiv
      (quotientStarQuotientEquiv (hKH.trans hH.2.1)),
    (surviving_quotient facts hG hK₁G hK₁).of_equiv
      (Components.componentStarEquiv G₁ K₁ hK₁G hK₁),
    facts.join_eq hG hK₁G hK₁⟩

omit [Finite G] in
/-- Equality in the actual ambient quotient lifts using the common Sylow.
Relative component minimality, rather than ambient normality, finishes. -/
theorem component_eq_of_star_eq {H J B C : Subgroup G} {T : Sylow 2 G}
    (hTH : (T : Subgroup G) ≤ H) (hHJ : H ≤ J) (hBH : B ≤ H)
    (hB : (B.subgroupOf H).IsCComponent) (hCJ : C ≤ J)
    (hC : (C.subgroupOf J).IsCComponent) (hBC : B ≤ C)
    (he : Source.starImage J B = Source.starImage J C) : B = C := by
  have hcore : pCore 2 J ≤ (T : Subgroup G).subgroupOf J := by
    have hs := pCore_isPGroup.le_sylow_of_normal (T.subtype (hTH.trans hHJ))
    simpa only [Sylow.coe_subtype] using hs
  have hCBcore : C.subgroupOf J ≤ B.subgroupOf J ⊔ pCore 2 J := by
    have hi : Source.starImage J C ≤ Source.starImage J B := he.ge
    have ht := map_le_iff_le_comap.mp hi
    simpa only [Source.starImage, comap_map_eq, QuotientGroup.ker_mk'] using ht
  have hCH : C ≤ H := by
    intro c hcC
    have hcJ : c ∈ J := hCJ hcC
    have ht := hCBcore (show (⟨c, hcJ⟩ : J) ∈ C.subgroupOf J from hcC)
    exact (sup_le (comap_mono hBH) (hcore.trans (comap_mono hTH))) ht
  have he' := hB.eq_of_le (hC.subgroupOf_of_le hCH hHJ) (comap_mono hBC)
  have hm := congrArg (Subgroup.map H.subtype) he'
  simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hCH] using hm

/-- Conditional assembly of 13.8.27(2). The constrained list calculation
`rigidity` is explicitly outstanding; it is not supplied by group orders. -/
theorem equalities_of_survivor_rigidity {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦) (rigidity : SurvivorRigidity.{u})
    {L L₁ G₁ M H K P : Subgroup G} {T : Sylow 2 G}
    (facts : UniformComponentFacts L L₁ (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ (T : Subgroup G))
    (hPn : G₁ ≤ normalizer (P : Set G))
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) := by
  obtain ⟨K₁, hK₁G, hK₁, hKK₁, hn, he, hs, hl, hjoin⟩ :=
    exists_surviving_overcomponent earlier facts hH hKH hK hP hp hPbase hPn hQ
  have hstars := rigidity (Source.Hstar G₁) _ _ (map_mono (comap_mono hKK₁)) he hs hl
  have hKK₁eq := component_eq_of_star_eq (le_sup_right.trans hH.1.2)
    hH.2.1 hKH hK hK₁G hK₁ hKK₁ hstars
  subst K₁
  exact ⟨hK₁, hn, hjoin.trans (facts.join_eq hH hKH hK).symm,
    facts.join_eq hH hKH hK⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
end
