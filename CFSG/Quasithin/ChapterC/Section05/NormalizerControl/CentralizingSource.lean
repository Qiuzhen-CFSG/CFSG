module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CubicSource
public import Theory.GroupTheory.CommonNormalSubgroup

/-!
# The actual centralizing-core branch of C.5.12

Intersect the C.5.11 Sylow subgroup with the centralizer of V inside
N_X(T₁). Its image is exactly P₁, using U₁≤V and the centralizing-core
branch hypothesis. The Frattini argument reduces control of N_X(T₁)
to the proved C.5.13 bound on N_X(P₁). The A₃ application supplies
that bound and the core identity from the genuine reduced source data.

Source: Aschbacher–Smith C.5.12, printed p.163, first paragraph.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
private theorem sylow_intersection_of_normalizes
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ normalizer (J : Set G)) :
    ∃ P : Sylow 2 J, (P : Subgroup J) = (S : Subgroup G).subgroupOf J := by
  let W := J ⊔ (S : Subgroup G)
  let : (J.subgroupOf W).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le J.le_normalizer hSJ)
  obtain ⟨P,hP⟩ := (S.subtype (show (S : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (J.subgroupOf W)
  let e := subgroupOfEquivOfLe (show J ≤ W from le_sup_left)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,mem_sup_left x.property⟩,x.property⟩,hx,rfl⟩

private theorem relative_sylow_intersection
    (X J T : Subgroup G) (hJX : J ≤ X) (hTJ : T ≤ normalizer (J : Set G))
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    ∃ P : Sylow 2 J, (P : Subgroup J).map J.subtype = T ⊓ J := by
  have hn : (S : Subgroup X) ≤ normalizer (J.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hJX]
    intro s hs
    exact hTJ (hS ▸ mem_map_of_mem X.subtype hs)
  obtain ⟨P,hP⟩ := sylow_intersection_of_normalizes S (J.subgroupOf X) hn
  let e := subgroupOfEquivOfLe hJX
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup (J.subgroupOf X)).map e.toMonoidHom).map J.subtype = _
  rw [hP,Subgroup.map_map]
  ext g
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨hS ▸ mem_map_of_mem X.subtype ha,a.property⟩
  · rintro ⟨hgT,hgJ⟩
    obtain ⟨g,hg,rfl⟩ := hS.symm ▸ hgT
    exact ⟨⟨g,hgJ⟩,hg,rfl⟩

/-- The actual C.5.13 Sylow-normalizer bound suffices in the centralizing-core
branch; no normalization of U by the whole core normalizer is required. -/
theorem normalizer_control_of_source_core_centralizing_sylow
    (X T U V C : Subgroup G) (hUV : U ≤ V)
    (hXV : X ≤ normalizer (V : Set G))
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hcore : T ⊓ centralizer (U : Set G) = C)
    (hCV : C ≤ centralizer (V : Set G))
    (hcontrol : (X ⊓ normalizer (C : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U : Set G) := by
  let N := X ⊓ normalizer (T : Set G)
  let J := N ⊓ centralizer (V : Set G)
  have hTX : T ≤ X := hS ▸ map_subtype_le _
  have hTN : T ≤ N := le_inf hTX T.le_normalizer
  have hNC : N ≤ normalizer (centralizer (V : Set G) : Set G) :=
    (inf_le_left.trans hXV).trans (normalizer_le_normalizer_centralizer V)
  have hNJ : N ≤ normalizer (J : Set G) :=
    (le_inf N.le_normalizer hNC).trans inf_normalizer_le_normalizer_inf
  obtain ⟨P,hP⟩ := relative_sylow_intersection X J T (inf_le_left.trans inf_le_left)
    (hTN.trans hNJ) S hS
  have he : T ⊓ J = C := by
    apply le_antisymm
    · exact (le_inf inf_le_left ((inf_le_right.trans inf_le_right).trans
        (centralizer_le hUV))).trans_eq hcore
    · exact le_inf (hcore.symm.trans_le inf_le_left)
        (le_inf ((hcore.symm.trans_le inf_le_left).trans hTN) hCV)
  have hPC : (P : Subgroup J).map J.subtype = C := hP.trans he
  apply le_normalizer_of_sylow_normalizer_le J N U inf_le_left hNJ
    (inf_le_right.trans (centralizer_le hUV)) P
  rw [hPC]
  rintro g ⟨⟨hgX,hgT⟩,hgC⟩
  exact hcontrol ⟨⟨hgX,hgC⟩,hgT⟩

/-- Frattini transfers the core-normalizer bound to the entire Sylow
normalizer when the actual core centralizes V. -/
theorem normalizer_control_of_source_core_centralizing
    (X T U V C : Subgroup G) (hUV : U ≤ V)
    (hXV : X ≤ normalizer (V : Set G))
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hcore : T ⊓ centralizer (U : Set G) = C)
    (hCV : C ≤ centralizer (V : Set G))
    (hcontrol : X ⊓ normalizer (C : Set G) ≤ normalizer (U : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U : Set G) := by
  exact normalizer_control_of_source_core_centralizing_sylow X T U V C
    hUV hXV S hS hcore hCV (inf_le_left.trans hcontrol)

open ConjugateSource.RankOne
/-- C.5.12 in the actual A₃ centralizing-core branch, using the complete
source C.5.13 normalizer conclusion. -/
theorem alternating_three_source_control_of_core_centralizing
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X V : Subgroup G) (hAX : K ⊔ T ≤ X)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    (hUV : U K ≤ V) (hXV : X ≤ normalizer (V : Set G))
    (hCV : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G))
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  have hcore := (CounterexampleCharacteristic.ReducedMarking.reduced_baumann_core K T
    h.short hT hTK ⟨P,hP⟩).2.2.2.2.2
  exact normalizer_control_of_source_core_centralizing X T (U K) V _ hUV hXV PX hPX hcore hCV
    (alternating_three_source_normalizes_module h ha hT hTK P hP hA X hAX PX hPX hx hnc)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
