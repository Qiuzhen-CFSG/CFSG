module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.Triality
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsSmall

/-!
# Relative embeddings for the complete rank-two Theorem C catalogue

Proper full-Sylow overgroups in PSL₃(2), PSp₄(2)′, G₂(2)′ and the Tits
group are solvable. This property lifts through the actual two-core, so
C-component minimality forces equality in all four small cases. The
nonbinary linear, symplectic, G₂ and Ree cases use their proved parabolic
field comparisons; both genuine triality field relations are retained.
The symplectic central-quotient equivalence supplies the full Sp₄ carrier
required by the original Chapter 11 statement.

The result applies to the whole existing RankTwoTheoremC catalogue, with
its concrete isomorphisms. Its source applications keep both flag
normalizers and arbitrary nontrivial U ≤ V₁ under the original Sylow
hypothesis. Refinement.RankTwo supplies the literal first-normalizer
application. This is the complete rank-two carrier branch of 11.1.1,
not the remaining odd-characteristic, sporadic or nonsimple branches.
The preceding quotient and pointwise-action inputs are produced by
qt-d-1222-natural-flag-cartan and discharged by
qt-d-1222-natural-local-geometry. The relative-components owner retains
all remaining carrier branches, second-component equality and triangle.

Source: Aschbacher--Smith A.3.12(2), Remark A.2.4(C.3), and 11.1.1,
printed pp.33,47--48,761, combined manuscript of 1 March 2004.
The imported concrete model calculations retain their ATLAS attribution
and license; see LICENSES/ATLAS.txt.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterA.Section03
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem small_even_solvable_sylow (hmodel : MovedMaximality.SmallEvenModel G) :
    SolvableSylowOvergroups G := by
  rcases hmodel with h | h | h | h
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    exact .of_equiv e (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF)
  · obtain ⟨e⟩ := h
    exact .of_equiv
      (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
      AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨e⟩ := h
    exact .of_equiv e Atlas.G2.binaryDerived_solvableSylowOvergroups
  · obtain ⟨e⟩ := h
    exact .of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups

private theorem relative_eq_of_solvable_sylow_quotient
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
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

/-- None of the four small even carriers permits a strict relative local
component under the original full Sylow. -/
theorem relative_eq_of_small_even
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hmodel : MovedMaximality.SmallEvenModel (K ⧸ pCore 2 K)) : B = K :=
  relative_eq_of_solvable_sylow_quotient hP hB hK hBK (small_even_solvable_sylow hmodel)

/-- The entire rank-two Theorem C catalogue gives equality or the literal
same-field/cube-field alternatives in 11.1.1. -/
theorem relative_equal_or_lie_of_rank_two
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    B = K ∨ LieOvergroup (K ⧸ pCore 2 K) n := by
  by_cases he : B = K
  · exact .inl he
  cases hmodel with
  | linear m hm h =>
    by_cases hm1 : m = 1
    · subst m
      exact .inl (relative_eq_of_small_even hP hB hK hBK (.inl (by simpa using h)))
    · exact relative_equal_or_lie_of_split_or_ree hP hB hK hBK hn hsmall
        (.inl ⟨m,by omega,.inr (.inl h)⟩)
  | symplectic m hm h =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hSp : Source.IsSp (K ⧸ pCore 2 K) 2 (2 ^ m) :=
      ⟨F,inferInstance,inferInstance,hF,
        ⟨e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm⟩⟩
    exact relative_equal_or_lie_of_split_or_ree hP hB hK hBK hn hsmall
      (.inl ⟨m,hm,.inr (.inr (.inl hSp))⟩)
  | g2 m hm h =>
    exact relative_equal_or_lie_of_split_or_ree hP hB hK hBK hn hsmall
      (.inl ⟨m,hm,.inr (.inr (.inr h))⟩)
  | triality m hm h =>
    rcases relative_triality_parameters hP hB hK (lt_of_le_of_ne hBK he) (by omega)
      (by omega) hsmall h with hnm | hnm
    · exact .inr (.triality (hnm.symm ▸ h))
    · exact .inr (.trialityCube m hm hnm h)
  | ree m hm h =>
    exact relative_equal_or_lie_of_split_or_ree hP hB hK hBK hn hsmall (.inr ⟨m,hm,h⟩)
  | symplectic_derived h =>
    exact .inl (relative_eq_of_small_even hP hB hK hBK (.inr (.inl h)))
  | g2_derived h =>
    exact .inl (relative_eq_of_small_even hP hB hK hBK (.inr (.inr (.inl h))))
  | tits h =>
    exact .inl (relative_eq_of_small_even hP hB hK hBK (.inr (.inr (.inr h))))

/-- The source classification alternative for the full rank-two catalogue. -/
theorem relative_component_alternative_of_rank_two
    {H B K P : Subgroup G}
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    ComponentAlternative B K n :=
  (relative_equal_or_lie_of_rank_two hP hB hK hBK hn hsmall hmodel).elim
    ComponentAlternative.equal ComponentAlternative.lie

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both original flag normalizers, for every rank-two carrier in Theorem C. -/
theorem flag_component_alternative_of_rank_two (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  have hT : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩
  exact relative_component_alternative_of_rank_two hs (flag_mem_local_of_model D S f i hm)
    hK hLK S.nonbinary hm hmodel

/-- The full rank-two catalogue in the arbitrary-U case of 11.1.1. -/
theorem subspace_component_alternative_of_rank_two
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
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
  exact relative_component_alternative_of_rank_two hSyl hlocalP hK hLK S.nonbinary hm hmodel

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
