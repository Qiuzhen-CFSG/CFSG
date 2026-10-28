module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.BinaryHigher
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.NonEnlargement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SmallSporadic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.JankoTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.JankoFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.Rudvalis
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.OddTernary
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The assembled simple-carrier reduction for the relative components

Apply the checked carrier arguments to every constructor of the actual
Theorem C catalogue. The higher binary rows are excluded; the rank-one,
rank-two, odd ternary and surviving finite rows give the precise 11.1.1
alternative. Only M₁₁, M₁₂, M₂₄ and Held remain in this simple-carrier
reduction, each with an actual isomorphism of the original two-core quotient.
This remaining disjunction is proof debt, not an extra source alternative.

Embedding.SmallMathieu discharges the first two retained exclusions.

The source application derives the catalogue from the original local SQTK
hypothesis whenever that quotient is simple. Neither a same-field model
list nor a desired embedding conclusion is assumed. The final flag and
arbitrary-subspace applications retain the full relative Sylow conditions.
All remaining carriers, covers, refinements and the triangle stay with
qt-d-1222-natural-relative-components. The preceding flag models and
pointwise line action belong to qt-d-1222-natural-flag-cartan, discharged by
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith A.2.3, A.3.12 and 11.1.1, printed pp.33,47--48,761,
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The exact unresolved simple carriers, never asserted to be source outputs. -/
def RemainingSimpleCarrier (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M11) ∨ Nonempty (A ≃* Sporadic.Mathieu.M12) ∨
    Nonempty (A ≃* Sporadic.Mathieu.M24) ∨ Nonempty (A ≃* Held.He)

/-- Exhaust the actual simple carrier catalogue, retaining the four unproved
candidates explicitly and proving every other same-field alternative. -/
theorem relative_simple_catalogue
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : TheoremCModel (K ⧸ pCore 2 K)) :
    ComponentAlternative B K n ∨ RemainingSimpleCarrier (K ⧸ pCore 2 K) := by
  let : Group.IsPerfect B := by
    let := hB.1.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  cases hmodel with
  | alternating d hd he =>
    have hdn : d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 := by omega
    rcases hdn with rfl | rfl | rfl | rfl
    · exact .inl (.equal (relative_eq_of_nonEnlarging_carrier hP hB hK hBK
        (.inr (.inr (.inl he)))))
    · exact .inl (.equal (relative_eq_of_nonEnlarging_carrier hP hB hK hBK
        (.inr (.inr (.inr (.inl he))))))
    · exact .inl (component_alternative_of_small_finite hBK hn hm (.inl he))
    · exact (relative_not_higher_binary hP hB hK hBK hn hm (.inl he)).elim
  | linear_odd p e hp ho he _ hmodel =>
    apply Or.inl
    apply relative_component_alternative_of_rank_one hP hB hK hBK hn hm
    refine .inr ⟨p,hp,ho,?_⟩
    rcases he with rfl | rfl
    · exact .inl (by simpa only [pow_one] using hmodel)
    · exact .inr hmodel
  | three_odd p hp ho u hmodel =>
    obtain ⟨hn2,rfl⟩ := relative_odd_ternary_parameters hP hB hK hBK hPB hn hm hp ho u (.inl hmodel)
    exact .inl (.four hn2 (.three u (.inl hmodel)))
  | rank_one hmodel =>
    exact .inl (.equal (relative_eq_of_nonEnlarging_carrier hP hB hK hBK (.inl hmodel)))
  | rank_two hmodel =>
    exact .inl (relative_component_alternative_of_rank_two hP hB hK hBK hn hm hmodel)
  | binary_linear d hd hmodel =>
    exact (relative_not_higher_binary hP hB hK hBK hn hm (.inr ⟨d,hd,hmodel⟩)).elim
  | sporadic name hne hmodel =>
    cases name with
    | m11 => exact .inr (.inl hmodel)
    | m12 => exact .inr (.inr (.inl hmodel))
    | m22 => exact .inl (component_alternative_of_small_sporadic hBK hn hm (.inl hmodel))
    | m23 => exact .inl (component_alternative_of_small_sporadic hBK hn hm (.inr (.inr (.inl hmodel))))
    | m24 => exact .inr (.inr (.inr (.inl hmodel)))
    | j2 => exact .inl (.four (relative_jankoTwo_parameters hP hK hBK hPB hn hm hmodel) (.j2 hmodel))
    | j3 => exact (hne rfl).elim
    | j4 => exact .inl (.four (relative_jankoFour_parameters hP hK hBK hPB hn hm hmodel) (.j4 hmodel))
    | hs => exact .inl (component_alternative_of_small_sporadic hBK hn hm (.inr (.inr (.inr hmodel))))
    | he => exact .inr (.inr (.inr (.inr hmodel)))
    | ru => exact .inl (.four (relative_rudvalis_parameters hP hK hBK hPB hn hm hmodel) (.ru hmodel))
  | janko_one hmodel =>
    exact .inl (component_alternative_of_small_finite hBK hn hm (.inr (.inr hmodel)))

/-- Derive the full catalogue from the actual relative SQTK group in the
simple-quotient source branch; no catalogue hypothesis remains. -/
theorem relative_simple_source
    {H B K P : Subgroup G} (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative B K n ∨ RemainingSimpleCarrier (K ⧸ pCore 2 K) := by
  let k := subgroupOfEquivOfLe hK.1
  let : Group.IsPerfect (K.subgroupOf H) := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := k.toMonoidHom) k.surjective
  have hs : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv k).mp (hH.subgroup _)
  have hq := ChapterE.Structure.sqtk_two_quotient hs (pCore 2 K) pCore_isPGroup
  have hna := Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K)
  have hc := ChapterA.Section02.theoremC_knownSimple inferInstance hna hq.stronglyQuasithin hq.isKGroup
  exact relative_simple_catalogue hP hB hK hBK hPB hn hm
    (SourceComponents.sourceTheoremC_to_local hna hc)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The source-derived simple-carrier reduction at both original flag normalizers. -/
theorem flag_simple_source (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li i) K S.field.degree ∨ RemainingSimpleCarrier (K ⧸ pCore 2 K) := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_simple_source
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal i.castSucc)) hs
    (flag_mem_local_of_model D S f i hm) hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm

/-- The same source-derived catalogue reduction for arbitrary nontrivial U ≤ V₁. -/
theorem subspace_simple_source
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) [IsSimpleGroup (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li 0) K S.field.degree ∨ RemainingSimpleCarrier (K ⧸ pCore 2 K) := by
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
  exact relative_simple_source (S.source.simpleQTKE.twoLocal_sqtk ⟨U,hU,htwo,rfl⟩)
    hSyl hlocalP hK hLK (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
