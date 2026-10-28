module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCoreProduct
public import Theory.SpecificGroups.SL2.SylowOmega

/-!
# DGS 6.4 on the original reduced triple

The replacement-section exclusions eliminate every nonlinear original
quotient under the relative normality assumption of 6.4. This includes
PSU₃(2) with its possible strict enlargement, and SU₃(2). The remaining
original linear marking supplies the actual closure quotient, its Sylow,
and the core-product equality. Restriction of the common Borel Sylow gives
both local Sylow clauses. The field size is identified with the omega-center
of every Sylow of the enlarged quotient, exactly the source parameter q.

The full Borel, the two cores and the original quotient representatives
are retained. No enlarged-model or Sylow premise is assumed. These are the
conditional conclusions of 6.4; unrestricted 6.1 model enlargement is a
separate obligation.
Source: DGS, Groups and Graphs (1985), 6.0 and 6.4, pp.118,120--121.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Corrected replacement excludes every nonlinear family before invoking
the linear closure theorem; the original endpoint marking is retained. -/
theorem reduced_linear_marking_of_inter_normal (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nonempty ((L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) := by
  cases h.quotient (other i) with
  | linear n hnpos hm =>
    obtain ⟨F,hF,hfin,hcard,he⟩ := hm
    let := hF
    let := hfin
    let : Fintype F := Fintype.ofFinite F
    have hchar : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact ⟨F,hF,hfin,hchar,he⟩
  | suzuki m hm =>
    exact ((reduced_nonlinear_adjacent_core_obstruction h i (Or.inl ⟨m,hm⟩)).1 hn).elim
  | projective_unitary n hnpos hm =>
    by_cases he : n = 1
    · subst n
      exact ((reduced_small_projective_adjacent_core_obstruction h i (by simpa using hm)).1 hn).elim
    · exact ((reduced_nonlinear_adjacent_core_obstruction h i
        (Or.inr (Or.inl ⟨n,by omega,hm⟩))).1 hn).elim
  | special_unitary n hnpos hm =>
    by_cases he : n = 1
    · subst n
      exact ((reduced_small_unitary_enlargement_obstruction h i
        (Or.inr (original_small_special_enlarged_marking h (other i) (by simpa using hm)))).1 hn).elim
    · exact ((reduced_nonlinear_adjacent_core_obstruction h i
        (Or.inr (Or.inr (Or.inl ⟨n,by omega,hm⟩)))).1 hn).elim
  | dihedral hm =>
    exact ((reduced_nonlinear_adjacent_core_obstruction h i
      (Or.inr (Or.inr (Or.inr hm)))).1 hn).elim

/-- The closure quotient uses the original field and agrees with the actual
enlarged quotient on every completion element. Its field order is the
source q, computed on every Sylow of that enlarged quotient. -/
theorem reduced_inter_normal_closure_quotient (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let d := Classical.choice ((reduced_triple h).local_data (other i))
    let M := localEnlargement d
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      ∃ e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F),
      ∃ qX : X →* SL(2,F), Function.Surjective qX ∧ qX.ker = pCore 2 X ∧
        (∀ T : Sylow 2 (M ⧸ pCore 2 M),
          Nat.card (omegaCenterIn (T : Subgroup (M ⧸ pCore 2 M))) = Nat.card F) ∧
        ∀ x : X, ∃ y : M, (y : G₀ L S) = x ∧
          qX x = reduced_linearEnlargementQuotient h (other i) d e
            (QuotientGroup.mk' (pCore 2 M) y) := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let := d.finite_P
  let M := localEnlargement d
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  obtain ⟨F,hF,hfin,hchar,⟨e⟩⟩ := reduced_linear_marking_of_inter_normal h i hn
  let := hF
  let := hfin
  let := hchar
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  obtain ⟨_,q₀,hq₀,hk₀,hcompat⟩ := source_linear_closure_premises (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i d hn q hq hk
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice ((reduced_triple h).local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  let a := MarkedClosure.coreClosureEquiv (P i) (P (other i)) hAP
  let qX := q₀.comp a.symm.toMonoidHom
  refine ⟨F,hF,hfin,hchar,e,qX,hq₀.comp a.symm.surjective,?_,?_,?_⟩
  · change (q₀.comp a.symm.toMonoidHom).ker = _
    rw [←MonoidHom.comap_ker,hk₀,←map_equiv_eq_comap_symm']
    exact pCore_map_iso 2 a
  · intro T
    exact Matrix.SpecialLinearGroup.card_omegaCenter_sylow_of_equiv f T
  · intro x
    obtain ⟨y,hy,he⟩ := hcompat (a.symm x)
    refine ⟨y,?_,he⟩
    rw [←MarkedClosure.coreClosureEquiv_coe (P i) (P (other i)) hAP,
      a.apply_symm_apply] at hy
    exact hy

/-- All subgroup clauses of 6.4, including both local Sylow conclusions,
with the original complete catalogue and no quotient or Sylow callback. -/
theorem reduced_inter_normal_closure_structure (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    (∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = (P i).pCoreIn 2) ∧
      sylowCenterSpan (P (other i)) ≤ omegaCenterIn (X.pCoreIn 2) ∧
      (∀ C : Subgroup ((P i).pCoreIn 2), C.Characteristic →
        X ≤ normalizer (C.map ((P i).pCoreIn 2).subtype : Set (G₀ L S)) → C = ⊥) ∧
      X.pCoreIn 2 = (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 ∧
      (↑(((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)) =
        ((P i).pCoreIn 2 : Set (G₀ L S)) * ((P (other i)).pCoreIn 2 : Set (G₀ L S)) ∧
      ∀ j : Fin 2, ∃ T : Sylow 2 (localEnlargement (Classical.choice ((reduced_triple h).local_data j))),
        (T : Subgroup _).map (localEnlargement (Classical.choice ((reduced_triple h).local_data j))).subtype =
          (P i).pCoreIn 2 ⊔ (P (other i)).pCoreIn 2 := by
  let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  obtain ⟨F,hF,hfin,hchar,⟨e⟩⟩ := reduced_linear_marking_of_inter_normal h i hn
  let := hF
  let := hfin
  let := hchar
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  have hs := (source_linear_closure_premises (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i d hn q hq hk).1
  have hp := source_linear_core_product_sylows (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i d hn q hq hk
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice ((reduced_triple h).local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  let a := MarkedClosure.coreClosureEquiv (P i) (P (other i)) hAP
  let T := (coreSylow (P i) (P (other i)) hs).mapSurjective (f := a.toMonoidHom) a.surjective
  refine ⟨⟨T,?_⟩,source_center_le_closure_core_omega (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i,?_,
    (source_linear_core_product (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) i d hn q hq hk).2,hp.1,?_⟩
  · change ((coreSylow (P i) (P (other i)) hs : Subgroup _).map a.toMonoidHom).map X.subtype = _
    rw [map_map]
    exact coreSylow_image _ _ hAP hs
  · intro C hC hCX
    let := hC
    exact characteristic_core_eq_bot_of_inter_normal (reduced_triple h)
      (reduced_borel_core_sylow h) i ((inter_core_local_normal_iff (reduced_triple h) i d).mp hn) C hCX
  · intro j
    let c := Classical.choice ((reduced_triple h).local_data j)
    obtain ⟨R,hR⟩ := hp.2 j
    obtain ⟨T,hT⟩ := R.exists_map_subtype_eq_of_le (localEnlargement_le c)
      (source_all_sylows_le_enlargement c (reduced_borel_core_sylow h) (reduced_vertex_sylow h j) R)
    exact ⟨T,hT.trans hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
