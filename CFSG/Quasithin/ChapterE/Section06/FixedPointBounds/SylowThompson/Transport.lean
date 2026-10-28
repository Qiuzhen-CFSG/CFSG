module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Contracts
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterE.Section01.Inheritance

/-!
# Transport and rank control for the E.6.27 Sylow preparation

Sylow conjugacy preserves the maximum elementary rank in a subgroup, so each
higher Thompson subgroup of a Sylow image lies in that of the overgroup.
The proper two-local in E.6.1 bounds `r(G,V)` by the rank of `V`; this supplies
the strict rank hypothesis in B.2.3. Uniqueness then controls the normalizer
of any intermediate two-subgroup whose higher Thompson subgroup centralizes
`V`. E-generation and Sylow transport retain the literal subgroup embeddings.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.26--27,
printed pp.256--257, and B.2.3, printed p.75.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
open ChapterB Stellmacher
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine E.1.6 minimum is invariant under isomorphisms, including its empty-set convention. -/
theorem generationParameter_equiv {X : Type*} {Y : Type*}
    [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y) :
    generationParameter X = generationParameter Y := by
  have hs : {i : ℕ | 0 < i ∧ IsEGenerated i X} =
      {i : ℕ | 0 < i ∧ IsEGenerated i Y} := by
    ext i
    exact and_congr_right fun _ => ⟨fun h => h.map_equiv e, fun h => h.map_equiv e.symm⟩
  simp only [generationParameter, Nat.card_congr e.toEquiv, hs]

omit [Finite G] in
/-- Transport the full ambient centralizer under an automorphism. -/
theorem map_centralizer (e : G ≃* G) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, mem_centralizer_iff.mpr ?_, e.apply_symm_apply x⟩
  intro a ha
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    mem_centralizer_iff.mp hx (e a) (mem_map_of_mem _ ha)

/-- Conjugate a two-subgroup into a specified Sylow using an element of the local overgroup. -/
theorem exists_conj_le (C A : Subgroup G) (hAC : A ≤ C)
    (hA : IsPGroup 2 A) (P : Sylow 2 C) :
    ∃ g : C, A.map (MulAut.conj (g : G)).toMonoidHom ≤
      (P : Subgroup C).map C.subtype := by
  obtain ⟨R, hR⟩ := (hA.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C R P
  refine ⟨g, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  have hmem : (MulAut.conj g) (⟨a, hAC ha⟩ : C) ∈ (P : Subgroup C) := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR ha)
  exact mem_map_of_mem C.subtype hmem

omit [Finite G] in
/-- Sylow maximality in ambient subgroup coordinates. -/
theorem sylow_image_maximal {C : Subgroup G} (P : Sylow 2 C)
    {A : Subgroup G} (hp : IsPGroup 2 A)
    (hle : (P : Subgroup C).map C.subtype ≤ A) (hAC : A ≤ C) :
    A = (P : Subgroup C).map C.subtype := by
  have he := P.is_maximal' (hp.comap_subtype (K := C))
    (fun x hx => hle (mem_map_of_mem C.subtype hx))
  have hm := congrArg (fun B : Subgroup C => B.map C.subtype) he
  exact (map_subgroupOf_eq_of_le hAC).symm.trans hm

/-- A Sylow image has the same maximum elementary rank as its overgroup. -/
theorem twoRank_sylow_image {C : Subgroup G} (P : Sylow 2 C) :
    twoRank ((P : Subgroup C).map C.subtype) = twoRank C := by
  unfold twoRank
  congr 1
  apply le_antisymm
  · exact (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ (map_subtype_le _)).1
  · obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty C
    obtain ⟨g, hg⟩ := exists_conj_le C A hA.1 hA.2.1.isPGroup P
    obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty
      ((P : Subgroup C).map C.subtype)
    have hc := hB.2.2 _ hg (hA.2.1.map (MulAut.conj (g : G)).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj (g : G)).injective,
      card_eq_elementaryAbelianMaxOrder C A hA,
      card_eq_elementaryAbelianMaxOrder _ B hB] at hc
    exact hc

/-- Higher Thompson subgroups of a Sylow image lie in those of the overgroup. -/
theorem thompsonJ_sylow_image_le {C : Subgroup G} (P : Sylow 2 C) (j : ℕ) :
    thompsonJ ((P : Subgroup C).map C.subtype) j ≤ thompsonJ C j := by
  apply sSup_le
  intro A hA
  apply le_sSup
  exact ⟨hA.1.trans (map_subtype_le _), hA.2.1,
    (twoRank_sylow_image P) ▸ hA.2.2⟩

/-- The ambient normalizer preserves every higher Thompson subgroup. -/
theorem normalizer_le_normalizer_thompson (A : Subgroup G) (j : ℕ) :
    normalizer (A : Set G) ≤ normalizer (thompsonJ A j : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  exact (thompsonJ_map_equiv (MulAut.conj x) A j).symm.trans
    (congrArg (fun B => thompsonJ B j) (mem_normalizer_iff_map_conj_eq.mp hx))

/-- E.6.1 and `j < r(G,V)` force the strict rank bound required by B.2.3. -/
theorem rank_bound {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V A : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hVA : V ≤ A) {j : ℕ}
    (hj : (j : ℕ∞) < globalR V) : j < twoRank A := by
  let := h.simpleQTKE.simple
  have hM : M ≠ ⊤ := twoLocal_ne_top_of_nonabelian_simple
    h.simpleQTKE.nonabelian h.maximalTwoLocal.1
  have hr : globalR V ≤ (Nat.log 2 (Nat.card V) : ℕ∞) := by
    have hb : ¬ centralizer (↑(⊥ : Subgroup G) : Set G) ≤ normalizer (V : Set G) := by
      intro hn
      apply hM
      apply top_le_iff.mp
      intro x _
      apply h.normalizer_le
      apply hn
      exact mem_centralizer_iff.mpr (by intro a ha; have : a = 1 := ha; subst a; simp)
    simpa only [subgroupCorank, relIndex_bot_left] using globalR_le_corank bot_le hb
  have hjV : j < Nat.log 2 (Nat.card V) := by exact_mod_cast hj.trans_le hr
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty A
  have hc := hB.2.2 V hVA h.elementary
  rw [card_eq_elementaryAbelianMaxOrder _ B hB] at hc
  exact hjV.trans_le (Nat.log_mono_right hc)

/-- The Thompson-normalizer argument of E.6.26 in the genuine E.6.1 setup. -/
theorem normalizer_le_of_control {Kc : GroupClass.{u}} {T : Sylow 2 G}
    {M V A : Subgroup G} (h : HypothesisE61 Kc T M V) {j : ℕ}
    (hj : (j : ℕ∞) < globalR V)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤ A) (hAT : A ≤ T)
    (hJ : thompsonJ A j ≤ centralizer (V : Set G)) :
    normalizer (A : Set G) ≤ M := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hr : j < twoRank A := rank_bound h (h.le_sylowCentralizer.trans hQA) hj
  have hJQ : thompsonJ A 0 ≤ Q :=
    le_inf ((thompsonJ_le A 0).trans hAT)
      ((lemma_B_2_3_1 A (Nat.zero_le j) hr).trans hJ)
  have hJ0 : thompsonJ A 0 = thompsonJ Q 0 :=
    lemma_B_2_3_3 A Q (Nat.zero_le j |>.trans_lt hr) hJQ hQA
  have hne : thompsonJ Q 0 ≠ ⊥ := by
    intro hz
    obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty A
    have hBJ : B ≤ thompsonJ A 0 := by rw [thompsonJ_zero]; exact le_sSup hB
    have hBb : B = ⊥ := le_bot_iff.mp (hJ0 ▸ hBJ |>.trans hz.le)
    have hc := card_eq_elementaryAbelianMaxOrder A B hB
    rw [hBb] at hc
    have hm : elementaryAbelianMaxOrder A = 1 := by simpa using hc.symm
    have hzR : twoRank A = 0 := by simp [twoRank, hm]
    omega
  have hNJ : normalizer (thompsonJ Q 0 : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal h.unique
      (T.isPGroup'.to_le ((thompsonJ_le Q 0).trans inf_le_left)) hne
      (inf_le_right.trans (normalizer_le_normalizer_thompson Q 0))
  exact (normalizer_le_normalizer_thompson A 0).trans (hJ0 ▸ hNJ)

/-- Transport a parabolic Sylow subgroup along its actual injective embedding. -/
theorem exists_sylow_map {X G : Type*} [Group X] [Finite X] [Group G] [Finite G]
    (f : X →* G) (hf : Function.Injective f) (S : Sylow 2 X)
    (H : Subgroup X) (hSH : (S : Subgroup X) ≤ H) :
    ∃ R : Sylow 2 (H.map f), (R : Subgroup (H.map f)).map (H.map f).subtype =
      (S : Subgroup X).map f := by
  let e := H.equivMapOfInjective f hf
  let R := (S.subtype hSH).mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨R, ?_⟩
  change (((S : Subgroup X).subgroupOf H).map e.toMonoidHom).map _ = _
  rw [map_map]
  have he : (H.map f).subtype.comp e.toMonoidHom = f.comp H.subtype := rfl
  rw [he, ← map_map, map_subgroupOf_eq_of_le hSH]

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson

end
