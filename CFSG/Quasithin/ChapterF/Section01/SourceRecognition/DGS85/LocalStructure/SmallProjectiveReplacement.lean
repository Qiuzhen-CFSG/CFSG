module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryObstructionApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitarySections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargedReplacementQuotient

/-!
# The faithful replacement section for the original PSU₃(2) endpoint

Assume contrary adjacent-core normality in the original completion. The
reduced replacement section descends along the literal inclusion to the
original enlarged endpoint modulo its actual two-core. Sylow fixed-space
generation forces this action to be faithful, even if that quotient has
order 144. Quadraticity and the new two-rank bound make the escaping
Thompson image elementary of order two or four.

The section retains its subgroups inside the original replacement span,
its conjugation action and the sharp fixed-space index. The actor order is
identified with the index against the original opposite parabolic core.
The quaternion-by-nine cubic bound contradicts this actor index. Both 6.5
clauses follow on the reduced graph and on the original parabolic cores,
without an enlarged model marking or an exclusion of order 144.
Source: DGS, Groups and Graphs (1985), 6.4--6.5, pp.120--122,
with the fixed-space-generation requirement of corrected 5.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem reduced_core_image (h : HypothesisF11 L S) (i : Fin 2) :
    (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (parabolic L S i).pCoreIn 2 := by
  have hP : P₀ L S i ≤ G₀ L S := by
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le hP, P₀_core h i]

private theorem reduced_small_projective_replacement_section (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2)
    (hn : (P₀ L S (other i)).subgroupOf (G₀ L S) ≤ normalizer
      (↑((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2) ⊓
        (((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2)) : Set (G₀ L S))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    let d := Classical.choice ((reduced_triple h).local_data (other i))
    let M := localEnlargement d
    let e := (M.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_localEnlargement_image h (other i) d))
    let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
    let D := enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (σ : Representation (ZMod 2) D W), IsIrreducible σ ∧ Function.Injective σ ∧
      fixedSpace σ (pResidual 2 D) = ⊥ ∧
      (∀ T : Sylow 2 D, GeneratedByFixedSpace σ T) ∧
      ∃ U C : Subgroup (G₀ L S), U ≤ V ∧ Nonempty (BinaryConjugationSection M U C (σ.comp q)) ∧
      ∃ A : Subgroup (G₀ L S), A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧ A ≤ M ∧
        IsElementaryAbelian 2 ((A.subgroupOf M).map q) ∧
        IsQuadratic σ ((A.subgroupOf M).map q) ∧
        Nat.card ((A.subgroupOf M).map q) =
          ((parabolic L S (other i)).pCoreIn 2).relIndex (A.map (G₀ L S).subtype) ∧
        (Nat.card ((A.subgroupOf M).map q) = 2 ∨ Nat.card ((A.subgroupOf M).map q) = 4) ∧
        Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf M).map q)) ≤
          Nat.card ((A.subgroupOf M).map q) := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let M := localEnlargement d
  let e := (M.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
    (MulEquiv.subgroupCongr (reduced_localEnlargement_image h (other i) d))
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  let D := enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))
  let := d.finite_P
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have hq : Function.Surjective q := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 M := by
    exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 M))
      eQ.toMonoidHom eQ.injective).trans (QuotientGroup.ker_mk' _)
  let : Finite D := Finite.of_surjective q hq
  obtain ⟨W,hW,hWM,hWf,σ,hi,hres,hgen,U,C,hUV,hs,A,hA,hout,hAM,hp,hquad,hcard,hnon,hbound⟩ :=
    source_enlarged_quotient_replacement_section (reduced_triple h) (reduced_borel_core_sylow h)
      i d hn q hq hk
  let := hW
  let := hWM
  let := hWf
  let : IsIrreducible σ := hi
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  have hnt : σ ≠ 1 := by
    intro he
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    apply hw
    apply hres.le
    intro g
    change σ g w = w
    rw [he]
    rfl
  have hf := original_small_projective_enlargement_faithful h (other i) hm σ hgen hnt
  let E := (A.subgroupOf M).map q
  let : IsElementaryAbelian 2 E := elementary_of_faithful_quadratic σ hf E hquad
  have hEc : Nat.card E ≤ 4 := by
    exact (primeRank_le_iff_elementary_card_le D).mp
      (original_small_projective_enlargement_twoRank h (other i) hm) E inferInstance
  have h24 : Nat.card E = 2 ∨ Nat.card E = 4 := by
    obtain ⟨n,he⟩ := hp.exists_card_eq
    change Nat.card E = 2^n at he
    change 1 < Nat.card E at hnon
    have hn2 : n ≤ 2 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      simpa only [←he] using hEc
    interval_cases n
    · have hz : Nat.card E = 1 := by simpa only [pow_zero] using he
      exact (by omega : False).elim
    · exact Or.inl (by simpa only [pow_one] using he)
    · exact Or.inr (by simpa only [show (2:ℕ)^2=4 by decide] using he)
  refine ⟨W,hW,hWM,hWf,σ,hi,hf,hres,hgen,U,C,hUV,hs,A,hA,hout,hAM,
    inferInstance,hquad,?_,h24,hbound⟩
  rw [←reduced_core_image h (other i),relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
  exact hcard

/-- The actual section has a faithful quotient action and an escaping actor of order two or four. -/
theorem original_small_projective_replacement_section (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2)
    (hn : parabolic L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    let d := Classical.choice ((reduced_triple h).local_data (other i))
    let M := localEnlargement d
    let e := (M.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_localEnlargement_image h (other i) d))
    let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
    let D := enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (σ : Representation (ZMod 2) D W), IsIrreducible σ ∧ Function.Injective σ ∧
      fixedSpace σ (pResidual 2 D) = ⊥ ∧
      (∀ T : Sylow 2 D, GeneratedByFixedSpace σ T) ∧
      ∃ U C : Subgroup (G₀ L S), U ≤ V ∧ Nonempty (BinaryConjugationSection M U C (σ.comp q)) ∧
      ∃ A : Subgroup (G₀ L S), A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧ A ≤ M ∧
        IsElementaryAbelian 2 ((A.subgroupOf M).map q) ∧
        IsQuadratic σ ((A.subgroupOf M).map q) ∧
        Nat.card ((A.subgroupOf M).map q) =
          ((parabolic L S (other i)).pCoreIn 2).relIndex (A.map (G₀ L S).subtype) ∧
        (Nat.card ((A.subgroupOf M).map q) = 2 ∨ Nat.card ((A.subgroupOf M).map q) = 4) ∧
        Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf M).map q)) ≤
          Nat.card ((A.subgroupOf M).map q) := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  have hD : (((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Subgroup (G₀ L S)).map
      (G₀ L S).subtype = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,
      reduced_core_image h i, reduced_core_image h (other i)]
  have hn0 : P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S)) := by
    intro x hx
    have hh := le_normalizer_comap (G₀ L S).subtype (hn (P₀_le h (other i) hx))
    rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hh
  exact reduced_small_projective_replacement_section h i hm hn0


/-- Both 6.5 conclusions at an original PSU₃(2) endpoint, including the possible order-144 enlargement. -/
theorem reduced_small_projective_adjacent_core_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    (¬ localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S))) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))),
      (T : Subgroup (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))).map
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).subtype = (P i).pCoreIn 2 := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  have hnfull : ¬ P (other i) ≤ normalizer
      (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S)) := by
    intro hn
    let M := localEnlargement d
    let e := (M.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_localEnlargement_image h (other i) d))
    let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    let q := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
    let D := enlargedEndpoint L S (other i) ⧸ pCore 2 (enlargedEndpoint L S (other i))
    let := d.finite_P
    let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
    let : Finite D := Finite.of_surjective q (eQ.surjective.comp (QuotientGroup.mk'_surjective _))
    obtain ⟨W,hW,hWM,hWf,σ,_,hf,_,_,U,C,_,_,A,_,_,_,hE,hquad,_,h24,hbound⟩ :=
      reduced_small_projective_replacement_section h i hm hn
    let := hW
    let := hWM
    let := hWf
    let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
    let E := (A.subgroupOf M).map q
    have hEE : IsElementaryTwo E := by
      refine ⟨?_,hE⟩
      intro he
      have hc : Nat.card E=1 := card_eq_one.mpr he
      change Nat.card E=2 ∨ Nat.card E=4 at h24
      omega
    have hpow : 2 ^ fixedCodim σ E ≤ 2 ^ rank E := by
      rw [←hEE.card_eq_two_pow_rank]
      change Nat.card (W ⧸ fixedSpace σ E) ≤ Nat.card E at hbound
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hbound
      exact hbound
    have hFF : IsFFModule σ := ⟨E,hEE,
      (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hpow⟩
    have hsmall := (isFFModule_iff_cubicRatio_le_one σ).mp hFF
    have hlarge := original_small_projective_enlargement_cubic_bound h (other i) hm σ hf
    exact (not_lt_of_ge (hsmall.trans (by norm_num))) hlarge
  exact ⟨fun hn => hnfull ((inter_core_local_normal_iff (reduced_triple h) i d).mp hn),
    core_not_sylow_of_inter_not_normal (reduced_triple h) i hnfull⟩

/-- Both obstructions on the original parabolic cores and full-endpoint closure. -/
theorem original_small_projective_obstruction (h : HypothesisF11 L S) (i : Fin 2)
    (hmodel : ClassicalGroup.IsPSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2) :
    (¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    (¬ parabolic L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))),
      (T : Subgroup (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)))).map
        (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype =
          (parabolic L S i).pCoreIn 2 := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let := d.finite_P
  obtain ⟨hn0,hs0⟩ := reduced_small_projective_adjacent_core_obstruction h i hmodel
  have hD : (((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Subgroup (G₀ L S)).map
      (G₀ L S).subtype = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,reduced_core_image h i,
      reduced_core_image h (other i)]
  have hn : ¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G) := by
    intro hh
    apply hn0
    intro x hx
    have hxl : (x : G) ∈ enlargedEndpoint L S (other i) := by
      rw [←reduced_localEnlargement_image h (other i) d]
      exact mem_map_of_mem (G₀ L S).subtype hx
    have hxn := le_normalizer_comap (G₀ L S).subtype (hh hxl)
    rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hxn
  have hEP : enlargedEndpoint L S (other i) ≤ parabolic L S (other i) :=
    sup_le (starredParabolic_le (other i)) ((pCoreIn_le 2 (commonBorel L S)).trans
      (commonBorel_le_parabolic (L := L) (S := S) (other i)))
  refine ⟨hn,(fun hh => hn (hEP.trans hh)),?_⟩
  intro hs
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hX := reduced_core_closure_full_image h i
  let f := (G₀ L S).subtype
  let eX : X ≃* conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)) :=
    (X.equivMapOfInjective f (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  let := (Classical.choice ((reduced_triple h).local_data (other i))).finite_P
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice ((reduced_triple h).local_data i))).trans
      (le_sup_right.trans (Classical.choice ((reduced_triple h).local_data (other i))).supplement.le)
  let : Finite X := Finite.of_injective (inclusion (conjugateSpanBy_le_self hAP))
    (inclusion_injective _)
  let : Finite (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))) :=
    Finite.of_equiv X eX.toEquiv
  obtain ⟨T,hT⟩ := hs
  let T0 := T.mapSurjective (f := eX.symm.toMonoidHom) eX.symm.surjective
  apply hs0
  refine ⟨T0,?_⟩
  apply map_injective (G₀ L S).subtype_injective
  rw [reduced_core_image h i,map_map]
  have hm := congrArg (Subgroup.map
    (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype)
    (show (T0 : Subgroup X).map eX.toMonoidHom = (T : Subgroup _) from by
      change ((T : Subgroup _).map eX.symm.toMonoidHom).map eX.toMonoidHom = _
      rw [map_map]
      simp)
  rw [map_map,hT] at hm
  exact hm

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
