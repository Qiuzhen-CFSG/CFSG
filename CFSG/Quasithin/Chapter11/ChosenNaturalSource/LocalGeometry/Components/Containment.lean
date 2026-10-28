module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OrdinaryContainment
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits

/-!
# Containment and relative normality for the chosen flag residuals

Unique containment uses the proved known-simple local-component theorem.
The containing component has at most two conjugates, so invariance of its
seed under a full Sylow two-subgroup forces normality. All normality is
inside the indicated local normalizer. The flag/model producer supplies
local-family membership and the pointwise action of L₁ on V₁; no
embedding-list hypothesis is used for these containment conclusions.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
the first paragraph of the proof of 11.1.1, printed p.761.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G]

/-- Unique containment and normality, transported from the actual local group H. -/
theorem exists_unique_normal_component {H B P : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : Chapter1.IsSylowIn 2 P H) (hBH : B ≤ H)
    (hB : B ∈ Chapter1.L G P) (hPB : P ≤ normalizer (B : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn H K ∧ B ≤ K ∧
      ∀ J : Subgroup G, Source.ComponentIn H J → B ≤ J → J = K := by
  obtain ⟨P₀, hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hrel : B.subgroupOf H ∈ ChapterA.Section03.localCComponents P₀ := by
    have h := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH, hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at h
    exact h.1
  obtain ⟨K₀, ⟨hK₀, hBK₀⟩, hu⟩ :=
    ChapterA.Section03.SourceEmbeddings.existsUnique_containing_cComponent_knownSimple
      hH P₀ hrel
  have hPK : (P₀ : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    intro p hp b
    change (b : G) ∈ B ↔ ((p : G) * (b : G) * (p : G)⁻¹ ∈ B)
    exact hPB (hP₀ ▸ mem_map_of_mem H.subtype hp) b
  have hn : K₀.Normal := cComponent_normal_of_unique_of_orbit_two hK₀ hBK₀
    (fun J hJ hBJ => hu J ⟨hJ, hBJ⟩) P₀ hPK
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source
      (ChapterE.Structure.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup) hK₀)
  have he : (K₀.map H.subtype).subgroupOf H = K₀ :=
    comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨K₀.map H.subtype, ⟨⟨map_subtype_le _, he.symm ▸ hK₀⟩, he.symm ▸ hn⟩,
    ?_, ?_⟩
  · simpa only [map_subgroupOf_eq_of_le hBH] using map_mono (f := H.subtype) hBK₀
  · intro J hJ hBJ
    have hj := hu (J.subgroupOf H) ⟨hJ.2, comap_mono hBJ⟩
    simpa only [map_subgroupOf_eq_of_le hJ.1] using congrArg (map H.subtype) hj

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The containment part of 11.1.1(ii), and the first assertion of 11.1.2
for either flag normalizer, conditional only on preceding local membership. -/
theorem flag_exists_unique_normal_component (i : Fin 2)
    (hlocal : f.Li i ∈ Chapter1.L G T) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) K ∧
      f.Li i ≤ K ∧ K ∈ Chapter1.He G ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) J →
        f.Li i ≤ J → J = K := by
  have hH := S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal i.castSucc)
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hT, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT]⟩
  obtain ⟨K, hK, hLK, hu⟩ := exists_unique_normal_component hH hs
    ((localResidual_le _).trans inf_le_right) hlocal (f.sylow_normalizes_Li i)
  refine ⟨K, hK, hLK, ?_, hu⟩
  apply Chapter1.lemma_1_1_3_1 (f.normalizer_mem_He S i.castSucc) _ hK.1.1 hK.1.2.subnormal
  intro hk
  exact hK.1.2.ne_bot (by rw [hk]; exact bot_subgroupOf _)

/-- 11.1.1(i) also covers arbitrary nontrivial U ≤ V₁. Its Sylow hypothesis
is the literal N_T(U), and no ambient normality of K is asserted. -/
theorem subspace_exists_unique_normal_component (U : Subgroup G) (hU : U ≠ ⊥)
    (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hlocal : f.Li 0 ∈ Chapter1.L G T)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (U : Set G)) K ∧
      f.Li 0 ≤ K ∧ ∀ J : Subgroup G, Source.ComponentIn (normalizer (U : Set G)) J →
        f.Li 0 ≤ J → J = K := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact exists_unique_normal_component
    (S.source.simpleQTKE.twoLocal_sqtk ⟨U, hU, hp, rfl⟩) hSyl
    hUL hlocalP
    (inf_le_left.trans (f.sylow_normalizes_Li 0))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
