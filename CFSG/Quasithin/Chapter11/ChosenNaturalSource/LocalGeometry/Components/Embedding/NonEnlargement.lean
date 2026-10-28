module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating

/-!
# Relative non-enlargement for rank-one and small alternating carriers

Every proper full-Sylow overgroup in a Bender carrier, an even SU₃ cover,
A₅, A₆ or 3.A₆ is solvable. This property lifts through the containing
component's actual two-core. Restriction of the full local Sylow to that
component and C-component minimality then force equality with the flag
residual. In particular, no quasisimplicity of the smaller image in the
ambient two-core quotient is assumed.

The applications include both flag normalizers and every nontrivial
U ≤ V₁ satisfying the original Sylow condition. The preceding rank-one
quotient and pointwise-action inputs belong to
qt-d-1222-natural-flag-cartan; qt-d-1222-natural-local-geometry discharges
them. Refinement.NonEnlargement applies equality at both source indices
and to uniqueness on the entire original V₂.

Source: Aschbacher--Smith A.3.12 and 11.1.1--11.1.3, printed
pp.47--48,761--765, combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Concrete carriers whose proper full-Sylow overgroups are solvable. -/
def NonEnlargingCarrier (A : Type*) [Group A] : Prop :=
  ClassificationModels.IsBenderModel A ∨
    (∃ m, 0 < m ∧ IsSU A 3 (2 ^ m)) ∨
    IsAlternating A 5 ∨ IsAlternating A 6 ∨ IsAlternatingCover A 6

private theorem nonEnlarging_solvable_sylow (h : NonEnlargingCarrier G) :
    SolvableSylowOvergroups G := by
  rcases h with hb | ⟨m,hm,hsu⟩ | h5 | h6 | h6
  · exact SourceEmbeddings.bender_solvable_proper_sylow_overgroup hb
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hsu
    apply SolvableSylowOvergroups.of_equiv e
    intro S P hSP hP
    have hfacts := ChapterF.Source.rankOneSylowFacts_su3 J m hm hF hc S
    let := hfacts.solvable
    have hn := hfacts.unique_maximal P hSP (lt_top_iff_ne_top.mpr hP)
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion hn) (inclusion_injective hn)
  · obtain ⟨e⟩ := h5
    exact .of_equiv e (fun _ P _ hP => alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  · obtain ⟨e⟩ := h6
    exact .of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨hq,_,⟨e⟩⟩ := h6
    let := hq
    exact .of_central_quotient (QuotientGroup.mk' (center G))
      (QuotientGroup.mk'_surjective _) (by simp)
      (.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable)

/-- Lift a concrete Sylow-overgroup calculation through the literal intrinsic
two-core, then apply it inside the original relative local group. -/
theorem relative_eq_of_solvable_sylow_model
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hmodel : SolvableSylowOvergroups (K ⧸ pCore 2 K)) : B = K := by
  obtain ⟨P₀,hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH,hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  let k := subgroupOfEquivOfLe hK.1
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  have he := SourceEmbeddings.eq_of_solvable_sylow_overgroups P₀ hlocal hK.2
    (comap_mono hBK) (isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (SolvableSylowOvergroups.of_equiv kq hmodel))
  simpa only [map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hK.1] using
    congrArg (map H.subtype) he

/-- All Bender, even SU₃ and small alternating quotient rows force actual
relative component equality, with their central covers retained. -/
theorem relative_eq_of_nonEnlarging_carrier
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hmodel : NonEnlargingCarrier (K ⧸ pCore 2 K)) : B = K :=
  relative_eq_of_solvable_sylow_model hP hB hK hBK (nonEnlarging_solvable_sylow hmodel)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both original flag residuals equal their containing components in these rows. -/
theorem flag_eq_of_nonEnlarging_carrier (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : NonEnlargingCarrier (K ⧸ pCore 2 K)) :
    f.Li i = K := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_eq_of_nonEnlarging_carrier hs (flag_mem_local_of_model D S f i hm)
    hK hLK hmodel

/-- The arbitrary-subspace clause of 11.1.1 in the same carrier families. -/
theorem subspace_eq_of_nonEnlarging_carrier
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : NonEnlargingCarrier (K ⧸ pCore 2 K)) :
    f.Li 0 = K := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_eq_of_nonEnlarging_carrier hSyl hlocalP hK hLK hmodel

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
