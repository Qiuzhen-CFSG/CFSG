module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Overgroup
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Standing
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original

/-!
# The original overgroup step without embedding-classification premises

The proved known-simple 1.2.4 containment theorem lifts the actual local
component to G₁. The full preceding component list and uniform binary
reduction bound the lifted quotient by 20160. Comparing the literal images
in G₁/O₂(G₁) then gives equality: the kernel on K is a two-group, so its
image has order at least |K/O₂(K)|. The original Sylow subgroup absorbs
O₂(G₁), returning containment upstairs and equality of the components.

The source consumer derives the SQTK hypothesis on G₁ and its quotient
from the original nontrivial normalizer line. No general A.3.12 embedding
classification, A.3.8 input, model rigidity, or H = G₁ premise remains.
The uniform binary reduction and the independent A₇ exclusion remain
with their earlier source producers.

Source: Aschbacher–Smith, 13.8.25(2), printed p.960/PDF p.977.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02 CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open Overgroup TransvectionRecognition.Component.ModelExtension
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

/-- Construct the local family inside G₁ before applying 1.2.4. The containment theorem
uses the literal two-core quotient, and normality is relative to G₁. -/
theorem exists_component_overgroup_source
    {L₁ G₁ M H K : Subgroup G} {T : Sylow 2 G}
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal)
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G₁ ⧸ pCore 2 G₁)) :
    ∃ K₁ : Subgroup G, K₁ ≤ G₁ ∧ (K₁.subgroupOf G₁).IsCComponent ∧ K ≤ K₁ ∧
      (K₁.subgroupOf G₁).Normal := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hTG := hTH.trans hH.2.1
  have hKG := hKH.trans hH.2.1
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  have hlocal := Chapter1.mem_L_of_cComponent hH.1.1 hSyl hKH hK
  have hlocalG : K.subgroupOf G₁ ∈ Chapter1.L G₁ (T.subtype hTG : Subgroup G₁) := by
    rw [Sylow.coe_subtype]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTG hKG).mp ⟨hKG, hlocal⟩
  have hTn : (T.subtype hTG : Subgroup G₁) ≤ normalizer (K.subgroupOf G₁ : Set G₁) := by
    rw [Sylow.coe_subtype, ← subgroupOf_normalizer_eq hKG]
    exact comap_mono (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn))
  obtain ⟨C, ⟨hC, hKC, hn⟩, _⟩ :=
    lemma_1_2_4_containment_normality_source hQ (T.subtype hTG) hlocalG hTn
  let K₁ := C.map G₁.subtype
  have hK₁G : K₁ ≤ G₁ := map_subtype_le C
  have hCeq : K₁.subgroupOf G₁ = C :=
    comap_map_eq_self_of_injective G₁.subtype_injective C
  have hKK₁ : K ≤ K₁ := by
    have hm := map_mono (f := G₁.subtype) hKC
    simpa only [map_subgroupOf_eq_of_le hKG] using hm
  exact ⟨K₁, hK₁G, hCeq ▸ hC, hKK₁, hCeq ▸ hn⟩

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
theorem eq_overgroup_of_uniform_reduction
    {L L₁ G₁ M H K P : Subgroup G} {T : Sylow 2 G}
    (facts : UniformComponentFacts L L₁ (T : Subgroup G) G₁ M)
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ (T : Subgroup G))
    (hPn : G₁ ≤ normalizer (P : Set G))
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G₁ ⧸ pCore 2 G₁)) : H = G₁ := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hTG := hTH.trans hH.2.1
  have hHjoin := facts.join_eq hH hKH hK
  obtain ⟨K₁, hK₁G, hK₁, hKK₁, _hK₁n⟩ :=
    exists_component_overgroup_source hH hKH hK (facts.normal hH hKH hK) hQ
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

/-- The source line supplies SQTK, the nontrivial normal two-subgroup and
its placement. Only the preceding uniform component conclusions remain. -/
theorem source_eq_overgroup
    {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : UniformComponentFacts L (sourceOne L T V₁) T G₁ M)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2) : H = G₁ := by
  have hP : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he, card_bot] at hc
    omega
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hPT : V₁ ≤ (T : Subgroup G) := by
    have he := T.is_maximal' (hp.to_sup_of_normal_left' T.isPGroup' d.line_stable) le_sup_right
    exact le_sup_left.trans he.le
  have hlocal : IsTwoLocal G₁ := ⟨V₁, hP, hp, d.first_normalizer⟩
  have hQ := ChapterE.Structure.sqtk_two_quotient (d.counterexample.qtke.twoLocal_sqtk hlocal)
    (pCore 2 G₁) pCore_isPGroup
  exact eq_overgroup_of_uniform_reduction facts hH hKH hK hKmodel
    hP hp (hPT.trans le_sup_right) d.first_normalizer.le hQ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
