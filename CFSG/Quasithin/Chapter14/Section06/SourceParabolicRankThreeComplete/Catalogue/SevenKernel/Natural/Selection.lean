module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Inputs
public import Theory.Representation.BinaryPermutationMulAction

/-!
# Relative block selection from the transposition geometry

A simultaneous conjugation of the actor and natural embedding marks J(R).
Its fixed vectors lie in the omega-center of J(R), so the pointwise-fixer
calculation identifies Baum(R)'s image with the same pair group. The relative
cubic seed then propagates to the original component. Both independent
geometric premises are retained explicitly for the final source assembly.

Source: Aschbacher--Smith C.1.24(a), printed pp.130--131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
open ChapterB.Offenders BinaryPermutation
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The fixed natural vectors control the actual Baumann subgroup of any R. -/
theorem baumann_image_of_marking
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* Sym)
    (f : Multiplicative (natural (Fin 7)) →* V) (hf : Function.Injective f)
    (he : ∀ (g : G) (v : natural (Fin 7)),
      f (Multiplicative.ofAdd (naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v)))
    (E : Subgroup Sym) (hJ : (elementaryAbelianMaxJ R).map q = E)
    (hfix : ∀ g : Sym, (∀ v ∈ fixedSpace (naturalRepresentation (Fin 7)) E,
      naturalRepresentation (Fin 7) g v = v) → g ∈ E) :
    (ChapterB.baumann R).map q = E := by
  let J := elementaryAbelianMaxJ R
  let W := V ⊓ centralizer (J : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ V from inf_le_left)
  have hW : W ≤ omegaOneCenterAmbient J :=
    elementary_centralizer_maxJ_le_omegaCenter R W (inf_le_left.trans hVR) inf_le_right
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    apply hfix
    intro v hv
    let w : V := f (Multiplicative.ofAdd v)
    have hw : (w : G) ∈ W := by
      refine ⟨w.property, ?_⟩
      intro j hj
      have hqj : q j ∈ E := hJ ▸ mem_map_of_mem q hj
      have hvj : naturalRepresentation (Fin 7) (q j) v = v := hv ⟨q j, hqj⟩
      have hh := he j v
      rw [hvj] at hh
      have hc := congrArg (fun x : V => (x : G)) hh.symm
      exact mul_inv_eq_iff_eq_mul.mp hc
    have hcomm := mem_centralizer_iff.mp hg.2 _ (hW hw)
    have hwfix : MulAut.conjNormal g w = w := by
      apply Subtype.ext
      change g*(w:G)*g⁻¹=(w:G)
      rw [←hcomm, mul_inv_cancel_right]
    apply Multiplicative.ofAdd.injective
    apply hf
    exact (he g v).trans hwfix
  · rw [←hJ]
    exact map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann R)

/-- The two independent geometric statements suffice for relative selection. -/
theorem selection_of_coordinates
    (hth : RelativeThompsonInput.{u}) (hgeom : PairGeometryInput)
    (L V : Subgroup G) [L.Normal] [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G = pCore 2 G)
    (hfL : generalizedFitting L = pCore 2 L)
    (R : Subgroup G) (hpR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hQR : pCore 2 G ≤ R) (hgen : L ⊔ R = ⊤)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (hLq : L.map q = alternatingGroup (Fin 7))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) A)
    (s : natural (Fin 7) →ₗ[ZMod 2] Additive V) (hs : Function.Injective s)
    (hse : ∀ g v, s (naturalRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (s v))
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hcore : R ⊓ q.ker = pCore 2 G) :
    (∃ D : Subgroup (ChapterB.baumann R), D.Characteristic ∧ D ≠ ⊥ ∧
      (D.map (ChapterB.baumann R).subtype).Normal) ∨ ChapterC.IsBlock L := by
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  by_cases hJ : elementaryAbelianMaxJ R ≤ q.ker
  · have hn := (ChapterB.lemma_B_2_10_centralizing V R hVR hQR
      (by simpa only [hk] using hcore.symm)
      (by simpa only [ChapterB.thompsonJ_zero, hk] using hJ)).2.2.2
    let : Nontrivial (ChapterB.baumann R) :=
      (nontrivial_iff_ne_bot _).mpr (ChapterC.RankOne.SymmetricSix.baumann_ne_bot R hpR hne)
    exact Or.inl ⟨⊤, inferInstance, top_ne_bot, by
      simpa only [←MonoidHom.range_eq_map, range_subtype] using hn⟩
  obtain ⟨a, k, hk1, hk3, hJa⟩ := hth G V R hpR hVR q hq hk hc hJ
  let q' := (MulAut.conj a⁻¹).toMonoidHom.comp q
  have hq' : Function.Surjective q' := (MulAut.conj a⁻¹).surjective.comp hq
  have hk' : q'.ker = q.ker :=
    MonoidHom.ker_comp_of_injective q (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective
  have hLq' : L.map q' = alternatingGroup (Fin 7) := by
    rw [show L.map q' = (L.map q).map (MulAut.conj a⁻¹).toMonoidHom from (map_map _ _ _).symm,
      hLq]
    apply eq_of_le_of_card_ge
    · rintro _ ⟨g, hg, rfl⟩
      exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem g hg a⁻¹
    · rw [card_map_of_injective (MulAut.conj a⁻¹).injective]
  have hJ' : (elementaryAbelianMaxJ R).map q' = disjointTranspositions 7 k := by
    rw [show (elementaryAbelianMaxJ R).map q' =
      ((elementaryAbelianMaxJ R).map q).map (MulAut.conj a⁻¹).toMonoidHom from (map_map _ _ _).symm,
      hJa]
    exact (disjointTranspositions 7 k).conjBy_inv a
  let f : Multiplicative (natural (Fin 7)) →* V := s.toAddMonoidHom.toMultiplicativeLeft
  have hfi : Function.Injective f :=
    fun v w h => Multiplicative.toAdd.injective (hs (congrArg Additive.ofMul h))
  have he : ∀ (g : G) (v : natural (Fin 7)),
      f (Multiplicative.ofAdd (naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v)) := by
    intro g v
    apply Subtype.ext
    change ((s (naturalRepresentation (Fin 7) (q g) v)).toMul : G) = _
    rw [hse, NormalElementaryQuotient.representation_apply]
    rfl
  let f' := f.comp (naturalMulAction (Fin 7) a).toMonoidHom
  have hf' : Function.Injective f' := hfi.comp (naturalMulAction (Fin 7) a).injective
  have he' : ∀ (g : G) (v : natural (Fin 7)),
      f' (Multiplicative.ofAdd (naturalRepresentation (Fin 7) (q' g) v)) =
        MulAut.conjNormal g (f' (Multiplicative.ofAdd v)) := by
    intro g v
    change f (Multiplicative.ofAdd (naturalRepresentation (Fin 7) a
      (naturalRepresentation (Fin 7) (a⁻¹*q g*a) v))) = _
    rw [←Module.End.mul_apply, ←map_mul]
    rw [show a*(a⁻¹*q g*a)=q g*a from by group]
    rw [map_mul, Module.End.mul_apply, he]
    rfl
  have hBaum := baumann_image_of_marking V R hVR q' f' hf' he'
    (disjointTranspositions 7 k) hJ' (hgeom k hk1 hk3).1
  have hpair : disjointTranspositions 7 k ≤ pairElementary := by
    rw [←ChapterC.RankOne.Alternating.SevenSource.natural_D_eq_pairElementary]
    exact disjointTranspositions_mono hk3
  have hswap : swap01 ∈ (elementaryAbelianMaxJ R).map q' := by
    rw [hJ']
    exact pairSwap_mem (n := 7) 0 hk1
  obtain ⟨P', hP'⟩ : ∃ P' : Sylow 2 q'.ker,
      (P' : Subgroup q'.ker).map q'.ker.subtype = pCore 2 G := by
    rw [hk']
    exact ⟨P,hP⟩
  exact relative_marked_seed L V hL hf hfL R hpR hQR hgen q' hq' hLq'
    f' hf' he' P' hP' (hk' ▸ hcore) hswap
    (hBaum.le.trans hpair) (hBaum ▸ (hgeom k hk1 hk3).2)

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
