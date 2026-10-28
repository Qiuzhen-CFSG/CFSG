module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceClosure

/-!
# Original parabolic cores in DGS 6.4

The reduced completion embeds into the original group. Its opposite-core
closure maps onto the closure under the full original parabolic, because
the full Borel normalizes both the seed and the reduced endpoint. Transport
of the constructed closure quotient and Sylows therefore gives the literal
original 6.4 conclusions, including both enlarged endpoints. The core product
is O₂ of the original full Borel, without replacing it by the original S.

These applications discharge the extra linear-marking and Sylow premises
of the earlier original-core interfaces. The relative normality premise is
exactly the contrary assumption printed in 6.4. The unrestricted 6.1
order-144 enlargement and final source assembly remain separate.
Source: DGS, Groups and Graphs (1985), pp.95--96, 118,120--121;
Aschbacher--Smith F.1.1 and F.1.9.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem closure_core_image (h : HypothesisF11 L S) (i : Fin 2) :
    (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (parabolic L S i).pCoreIn 2 := by
  have hP : P₀ L S i ≤ G₀ L S := by
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le hP,P₀_core h i]

private theorem closure_normality_pullback (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) :
    localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤ normalizer
      (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)) := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  have hD : ((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
      ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Subgroup (G₀ L S)).map
      (G₀ L S).subtype = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,closure_core_image h i,
      closure_core_image h (other i)]
  intro x hx
  have hxl : (x : G) ∈ enlargedEndpoint L S (other i) := by
    rw [←reduced_localEnlargement_image h (other i) d]
    exact mem_map_of_mem (G₀ L S).subtype hx
  have hxn := le_normalizer_comap (G₀ L S).subtype (hn hxl)
  rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hxn

private theorem sylow_image_transport {A H : Type*} [Group A] [Group H]
    (f : A →* H) (hf : Function.Injective f) (X C : Subgroup A) [Finite X]
    (Y : Subgroup H) (he : X.map f = Y)
    (hs : ∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = C) :
    ∃ T : Sylow 2 Y, (T : Subgroup Y).map Y.subtype = C.map f := by
  let e : X ≃* Y := (X.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he)
  let : Finite Y := Finite.of_equiv X e.toEquiv
  obtain ⟨T,hT⟩ := hs
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((T : Subgroup X).map e.toMonoidHom).map Y.subtype = _
  rw [map_map,←hT,map_map]
  rfl


private theorem core_quotient_pair_image {A H D : Type*} [Group A] [Group H] [Group D]
    (f : A →* H) (hf : Function.Injective f) (X M : Subgroup A) (Y N : Subgroup H)
    (hXY : X.map f = Y) (hMN : M.map f = N)
    (qX : X →* D) (qM : M →* D)
    (hqX : Function.Surjective qX) (hkX : qX.ker = pCore 2 X)
    (hqM : Function.Surjective qM) (hkM : qM.ker = pCore 2 M)
    (hc : ∀ x : X, ∃ y : M, (y : A) = x ∧ qX x = qM y) :
    ∃ (qY : Y →* D) (qN : N →* D),
      Function.Surjective qY ∧ qY.ker = pCore 2 Y ∧
      Function.Surjective qN ∧ qN.ker = pCore 2 N ∧
      ∀ x : Y, ∃ y : N, (y : H) = x ∧ qY x = qN y := by
  let a : X ≃* Y := (X.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hXY)
  let c : M ≃* N := (M.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hMN)
  refine ⟨qX.comp a.symm.toMonoidHom,qM.comp c.symm.toMonoidHom,
    hqX.comp a.symm.surjective,?_,hqM.comp c.symm.surjective,?_,?_⟩
  · rw [←MonoidHom.comap_ker,hkX,←map_equiv_eq_comap_symm']
    exact pCore_map_iso 2 a
  · rw [←MonoidHom.comap_ker,hkM,←map_equiv_eq_comap_symm']
    exact pCore_map_iso 2 c
  · intro x
    obtain ⟨y,hy,he⟩ := hc (a.symm x)
    refine ⟨c y,?_,?_⟩
    · have hh := congrArg f hy
      change (c y : H) = (a (a.symm x) : H) at hh
      simpa only [a.apply_symm_apply] using hh
    · change qX (a.symm x) = qM (c.symm (c y))
      rw [c.symm_apply_apply]
      exact he

/-- The original full-endpoint closure has the exact common-core kernel,
and the core product is Sylow in each actual enlarged endpoint. -/
theorem original_inter_normal_core_sylows (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))
    (∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = (parabolic L S i).pCoreIn 2) ∧
      X.pCoreIn 2 = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 ∧
      (↑((commonBorel L S).pCoreIn 2) : Set G) =
        ((parabolic L S i).pCoreIn 2 : Set G) * ((parabolic L S (other i)).pCoreIn 2 : Set G) ∧
      ∀ j : Fin 2, ∃ T : Sylow 2 (enlargedEndpoint L S j),
        (T : Subgroup _).map (enlargedEndpoint L S j).subtype =
          (parabolic L S i).pCoreIn 2 ⊔ (parabolic L S (other i)).pCoreIn 2 := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let := finite_endpoints (reduced_triple h)
  let := (Classical.choice ((reduced_triple h).local_data (other i))).finite_P
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice ((reduced_triple h).local_data i))).trans
      (le_sup_right.trans (Classical.choice ((reduced_triple h).local_data (other i))).supplement.le))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  obtain ⟨hs,_,_,hcore,hprod,hboth⟩ :=
    reduced_inter_normal_closure_structure h i (closure_normality_pullback h i hn)
  have hX := reduced_core_closure_full_image h i
  refine ⟨?_,?_,?_,?_⟩
  · have hh := sylow_image_transport (G₀ L S).subtype (G₀ L S).subtype_injective
      X ((P i).pCoreIn 2) _ hX hs
    rwa [closure_core_image h i] at hh
  · have hh := congrArg (Subgroup.map (G₀ L S).subtype) hcore
    rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,hX,
      Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,closure_core_image h i,
      closure_core_image h (other i)] at hh
    exact hh
  · have hBG : B₀ L S ≤ G₀ L S :=
      (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
    have hh := congrArg (Set.image (G₀ L S).subtype) hprod
    rw [Set.image_mul] at hh
    change (↑((((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype) : Set G) =
      (↑(((P i).pCoreIn 2).map (G₀ L S).subtype) : Set G) *
      (↑(((P (other i)).pCoreIn 2).map (G₀ L S).subtype) : Set G) at hh
    rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le hBG,B₀_core h,closure_core_image h i,
      closure_core_image h (other i)] at hh
    exact hh
  · intro j
    let d := Classical.choice ((reduced_triple h).local_data j)
    let := d.finite_P
    let : Finite (localEnlargement d) := Finite.of_injective
      (inclusion (localEnlargement_le d)) (inclusion_injective _)
    have hh := sylow_image_transport (G₀ L S).subtype (G₀ L S).subtype_injective
      (localEnlargement d) ((P i).pCoreIn 2 ⊔ (P (other i)).pCoreIn 2)
      (enlargedEndpoint L S j) (reduced_localEnlargement_image h j d) (hboth j)
    rwa [Subgroup.map_sup,closure_core_image h i,closure_core_image h (other i)] at hh

/-- The actual original closure and enlarged endpoint have compatible linear
quotients, with their own two-cores as kernels and the source omega parameter. -/
theorem original_inter_normal_closure_quotient (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))
    let M := enlargedEndpoint L S (other i)
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) ∧
      ∃ (qX : X →* SL(2,F)) (qM : M →* SL(2,F)),
        Function.Surjective qX ∧ qX.ker = pCore 2 X ∧
        Function.Surjective qM ∧ qM.ker = pCore 2 M ∧
        (∀ T : Sylow 2 (M ⧸ pCore 2 M),
          Nat.card (omegaCenterIn (T : Subgroup (M ⧸ pCore 2 M))) = Nat.card F) ∧
        ∀ x : X, ∃ y : M, (y : G) = x ∧ qX x = qM y := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let M := localEnlargement d
  obtain ⟨F,hF,hfin,hchar,e,qX,hqX,hkX,_,hcompat⟩ :=
    reduced_inter_normal_closure_quotient h i (closure_normality_pullback h i hn)
  let := hF
  let := hfin
  let := hchar
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let qM := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hqM : Function.Surjective qM := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkM : qM.ker = pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  obtain ⟨qY,qN,hqY,hkY,hqN,hkN,hc⟩ := core_quotient_pair_image
    (G₀ L S).subtype (G₀ L S).subtype_injective X M _ _
    (reduced_core_closure_full_image h i) (reduced_localEnlargement_image h (other i) d)
    qX qM hqX hkX hqM hkM hcompat
  let a := (QuotientGroup.quotientMulEquivOfEq hkN.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective qN hqN)
  exact ⟨F,hF,hfin,hchar,⟨e⟩,qY,qN,hqY,hkY,hqN,hkN,
    (fun T => Matrix.SpecialLinearGroup.card_omegaCenter_sylow_of_equiv a T),hc⟩

/-- Apply Baumann to the original full-endpoint closure with the 6.4 Sylow
and linear-quotient premises now discharged from the complete source family. -/
theorem original_inter_normal_baumann_commutator (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))
    ⁅X.pCoreIn 2,X⁆ ≤ conjugateSpanBy (omegaCenterIn ((parabolic L S i).pCoreIn 2)) X := by
  have hn₀ := closure_normality_pullback h i hn
  obtain ⟨F,hF,hfin,hchar,⟨e⟩⟩ := reduced_linear_marking_of_inter_normal h i hn₀
  let := hF
  let := hfin
  let := hchar
  have hm := map_mono (f := (G₀ L S).subtype) (reduced_linear_baumann_commutator h i hn₀ e)
  dsimp only at hm ⊢
  rw [map_commutator,map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    reduced_core_closure_full_image h i] at hm
  rw [map_conjugateSpanBy,NilesRankOneKernel.omegaCenterIn_map_injective _ (G₀ L S).subtype_injective,
    closure_core_image h i,reduced_core_closure_full_image h i] at hm
  exact hm

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
