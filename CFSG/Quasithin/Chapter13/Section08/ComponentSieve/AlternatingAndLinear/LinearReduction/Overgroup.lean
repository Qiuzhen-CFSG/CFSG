module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# The overgroup deduction in Aschbacher–Smith 13.8.25

Given the uniform preceding binary-linear reduction and the earlier source
component facts, a component K of H with K/O₂(K) ≅ L₄(2) forces H = G₁.
All component and normality assertions are relative to their stated overgroups.

First construct the genuine local-family membership inside G₁, including its
Sylow and nontrivial two-core conditions. Apply the proved lifting deduction
1.2.4 from the universal A.3.12 and A.3.8 inputs, retaining the actual embedding
in G₁/O₂(G₁). Construct K₁T ∈ Hz using the source normal two-subgroup V₁.

For this particular L₄(2) branch, orders give a shorter rigorous substitute for
case elimination in the A.3.12 embedding list. The full 13.8.21(2) list, A₇
exclusion and uniform binary reduction bound |K₁/O₂(K₁)| by 20160: the A₆
alternative has order 360, and G₂(2)′ is a subgroup of G₂(2), of order 12096.
The actual image of K in G₁/O₂(G₁) has order at least |K/O₂(K)| = 20160.
The nested images therefore coincide. Since O₂(G₁) lies in T ≤ H, this puts
K₁ inside H. Relative component minimality then gives K₁ = K. Constructing
G₁ ∈ Hz and applying 13.8.21(3) finishes H = KT = K₁T = G₁.

`UniformComponentFacts` lists only the precise earlier-source consequences
consumed here; it is not a replacement encoding of the full statements of
13.8.21–23. The parent source-theorem assembly supplies these facts, the
uniform binary reduction and the genuine local setup. This file neither
proves the earlier theorems nor assumes embedding rigidity or H = G₁.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 13.8.25, printed p.960, PDF p.977, the paragraph
beginning “Therefore we have established that n = 4”. The concrete order
formulas are imported from the attributed ATLAS port.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Overgroup
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem card_psl4_two {X : Type*} [Group X]
    (h : ClassicalGroup.IsPSL X 4 2) : Nat.card X = 20160 := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := h
  let := hF
  let := hfin
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hq] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem card_alternating_six {X : Type*} [Group X]
    (h : IsAlternating X 6) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem card_g2_derived_le {X : Type*} [Group X]
    (h : Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nat.card X ≤ 12096 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hb := (commutator (Atlas.G2.Model (ZMod 2))).card_le_card_group
  have hc : Nat.card (Atlas.G2.Model (ZMod 2)) = 12096 := by
    rw [Atlas.G2.card_Model]
    norm_num [Nat.card_eq_fintype_card]
  omega

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

private theorem quotient_card_le_starImage {J B : Subgroup G} (hBJ : B ≤ J) :
    Nat.card (B ⧸ pCore 2 B) ≤ Nat.card (Source.starImage J B) := by
  let e := (subgroupOfEquivOfLe hBJ).symm
  let e' := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (imageTwoCoreEquiv (B.subgroupOf J))
  rw [Nat.card_congr e'.toEquiv]
  exact Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (pCore 2 (Source.starImage J B))) (QuotientGroup.mk'_surjective _)

private theorem component_eq_of_card_bound {H J B C : Subgroup G} {S : Sylow 2 G}
    (hSH : (S : Subgroup G) ≤ H) (hHJ : H ≤ J) (hBH : B ≤ H)
    (hB : (B.subgroupOf H).IsCComponent) (hCJ : C ≤ J)
    (hC : (C.subgroupOf J).IsCComponent) (hBC : B ≤ C)
    (hc : Nat.card (C ⧸ pCore 2 C) ≤ Nat.card (B ⧸ pCore 2 B)) : B = C := by
  have hBJ := hBH.trans hHJ
  have hi : Source.starImage J B ≤ Source.starImage J C :=
    map_mono (comap_mono hBC)
  have he : Source.starImage J B = Source.starImage J C := by
    apply eq_of_le_of_card_ge hi
    calc
      Nat.card (Source.starImage J C) = Nat.card (C ⧸ pCore 2 C) :=
        (Nat.card_congr (Components.componentStarEquiv J C hCJ hC).toEquiv).symm
      _ ≤ Nat.card (B ⧸ pCore 2 B) := hc
      _ ≤ Nat.card (Source.starImage J B) := quotient_card_le_starImage hBJ
  have hcore : pCore 2 J ≤ (S : Subgroup G).subgroupOf J := by
    have hs := pCore_isPGroup.le_sylow_of_normal (S.subtype (hSH.trans hHJ))
    simpa only [Sylow.coe_subtype] using hs
  have hCBcore : C.subgroupOf J ≤ B.subgroupOf J ⊔ pCore 2 J := by
    have hi' : Source.starImage J C ≤ Source.starImage J B := he.ge
    have ht := map_le_iff_le_comap.mp hi'
    simpa only [Source.starImage, comap_map_eq, QuotientGroup.ker_mk'] using ht
  have hCH : C ≤ H := by
    intro c hcC
    have hcJ : c ∈ J := hCJ hcC
    have ht := hCBcore (show (⟨c, hcJ⟩ : J) ∈ C.subgroupOf J from hcC)
    have hu : B.subgroupOf J ⊔ pCore 2 J ≤ H.subgroupOf J := by
      apply sup_le (comap_mono hBH)
      exact hcore.trans (comap_mono hSH)
    exact hu ht
  have he' := hB.eq_of_le (hC.subgroupOf_of_le hCH hHJ) (comap_mono hBC)
  have hm := congrArg (Subgroup.map H.subtype) he'
  simpa only [map_subgroupOf_eq_of_le hBH, map_subgroupOf_eq_of_le hCH] using hm

/-- The universal earlier-source inputs to the proved form of 1.2.4.
Their SQTK, zero two-core, Sylow and local-family hypotheses are retained. -/
structure EarlierEmbeddings (𝒦 : GroupClass.{u}) : Prop where
  a312 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
    B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B
  a38 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ C : Subgroup X, C.IsCComponent →
    C.Normal ∨ (normalizer (C : Set X)).index = 2 ∧ NonnormalCComponentModel C

/-- Construct the local family inside G₁ before applying 1.2.4. The embedding
is between the literal images in G₁/O₂(G₁), and normality is relative to G₁. -/
theorem exists_component_overgroup {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    {L₁ G₁ M H K : Subgroup G} {T : Sylow 2 G}
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) :
    ∃ K₁ : Subgroup G, K₁ ≤ G₁ ∧ (K₁.subgroupOf G₁).IsCComponent ∧ K ≤ K₁ ∧
      (K₁.subgroupOf G₁).Normal ∧
      A312Embedding (Source.starImage G₁ K) (Source.starImage G₁ K₁) := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hTG := hTH.trans hH.2.1
  have hKG := hKH.trans hH.2.1
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  have hlocal := Chapter1.mem_L_of_cComponent hH.1.1 hSyl hKH hK
  have hlocalG : K.subgroupOf G₁ ∈ Chapter1.L G₁ (T.subtype hTG : Subgroup G₁) := by
    rw [Sylow.coe_subtype]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTG hKG).mp ⟨hKG, hlocal⟩
  obtain ⟨C, hC, hKC, _, he, hn⟩ :=
    lemma_1_2_4_of_A_3_12_A_3_8 earlier.a312 earlier.a38 hQ (T.subtype hTG) hlocalG
  let K₁ := C.map G₁.subtype
  have hK₁G : K₁ ≤ G₁ := map_subtype_le C
  have hCeq : K₁.subgroupOf G₁ = C :=
    comap_map_eq_self_of_injective G₁.subtype_injective C
  have hKK₁ : K ≤ K₁ := by
    have hm := map_mono (f := G₁.subtype) hKC
    simpa only [map_subgroupOf_eq_of_le hKG] using hm
  have hTn : (T.subtype hTG : Subgroup G₁) ≤ normalizer (K.subgroupOf G₁ : Set G₁) := by
    rw [Sylow.coe_subtype, ← subgroupOf_normalizer_eq hKG]
    exact comap_mono (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn))
  refine ⟨K₁, hK₁G, hCeq ▸ hC, hKK₁, hCeq ▸ hn hTn, ?_⟩
  simpa only [Source.starImage, hCeq] using he

/-- Precisely the earlier chapter consequences consumed by this paragraph.
The full list of 13.8.21(2) is retained, including A₆ and G₂(2)′. The triple
cover in the binary reduction is the quotient of L, not the solvable L₁. -/
structure UniformComponentFacts (L L₁ T G₁ M : Subgroup G) : Prop where
  base_le : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → L₁ ≤ C
  componentList : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent →
    (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) n 2) ∨
      IsAlternating (C ⧸ pCore 2 C) 6 ∨ IsAlternating (C ⧸ pCore 2 C) 7 ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2)))
  join_eq : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → J = C ⊔ T
  normal : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → (C.subgroupOf J).Normal
  not_A7 : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → ¬ IsAlternating (C ⧸ pCore 2 C) 7
  binaryReduction : ∀ {J C : Subgroup G} {n : ℕ}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → 3 ≤ n → n ≤ 5 →
    ClassicalGroup.IsPSL (C ⧸ pCore 2 C) n 2 →
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 4 2

omit [Finite G] in
private theorem component_quotient_card_le {L L₁ T G₁ M J C : Subgroup G}
    (facts : UniformComponentFacts L L₁ T G₁ M)
    (hJ : J ∈ Source.Hz L₁ T G₁ M) (hCJ : C ≤ J)
    (hC : (C.subgroupOf J).IsCComponent) : Nat.card (C ⧸ pCore 2 C) ≤ 20160 := by
  rcases facts.componentList hJ hCJ hC with ⟨n, hn3, hn5, hn⟩ | ha6 | ha7 | hg2
  · obtain ⟨rfl, _, _⟩ := facts.binaryReduction hJ hCJ hC hn3 hn5 hn
    exact (card_psl4_two hn).le
  · exact (card_alternating_six ha6).le.trans (by decide)
  · exact (facts.not_A7 hJ hCJ hC ha7).elim
  · exact (card_g2_derived_le hg2).trans (by decide)

/-- The overgroup deduction in Aschbacher–Smith 13.8.25, printed p.960.
The source two-subgroup P (V₁ in the application) constructs both required
members of Hz. The chosen K has quotient L₄(2). No component assertion in G₁,
local-family membership, or equality of overgroups is assumed. -/
theorem eq_overgroup_of_uniform_linear_reduction {𝒦 : GroupClass.{u}}
    (earlier : EarlierEmbeddings 𝒦)
    {L L₁ G₁ M H K P : Subgroup G} {T : Sylow 2 G}
    (facts : UniformComponentFacts L L₁ (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ (T : Subgroup G))
    (hPn : G₁ ≤ normalizer (P : Set G))
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁)) : H = G₁ := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hTG := hTH.trans hH.2.1
  have hHjoin := facts.join_eq hH hKH hK
  obtain ⟨K₁, hK₁G, hK₁, hKK₁, _hK₁n, _hEmbed⟩ :=
    exists_component_overgroup earlier hH hKH hK (facts.normal hH hKH hK) hQ
  have hjoinG : K₁ ⊔ (T : Subgroup G) ≤ G₁ := sup_le hK₁G hTG
  have hK₁join : (K₁.subgroupOf (K₁ ⊔ (T : Subgroup G))).IsCComponent :=
    hK₁.subgroupOf_of_le le_sup_left hjoinG
  have hjoinHz : K₁ ⊔ (T : Subgroup G) ∈ Source.Hz L₁ (T : Subgroup G) G₁ M := by
    apply Components.mem_Hz_of_normal_two_subgroup L₁ (T : Subgroup G) G₁ M P _
      hP hp hPbase hPn
    · exact sup_le_sup ((facts.base_le hH hKH hK).trans hKK₁) le_rfl
    · exact hjoinG
    · intro he
      apply hH.2.2
      rw [hHjoin]
      exact (sup_le_sup hKK₁ le_rfl).trans he
  have hcard : Nat.card (K₁ ⧸ pCore 2 K₁) ≤ Nat.card (K ⧸ pCore 2 K) := by
    rw [card_psl4_two hKmodel]
    exact component_quotient_card_le facts hjoinHz le_sup_left hK₁join
  have hKK₁eq := component_eq_of_card_bound hTH hH.2.1 hKH hK hK₁G hK₁ hKK₁ hcard
  have hG₁Hz : G₁ ∈ Source.Hz L₁ (T : Subgroup G) G₁ M := by
    apply Components.mem_Hz_of_normal_two_subgroup L₁ (T : Subgroup G) G₁ M P _
      hP hp hPbase hPn (hH.1.2.trans hH.2.1) le_rfl
    exact fun he => hH.2.2 (hH.2.1.trans he)
  calc
    H = K ⊔ (T : Subgroup G) := hHjoin
    _ = K₁ ⊔ (T : Subgroup G) := congrArg (fun C => C ⊔ (T : Subgroup G)) hKK₁eq
    _ = G₁ := (facts.join_eq hG₁Hz hK₁G hK₁).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Overgroup

end
