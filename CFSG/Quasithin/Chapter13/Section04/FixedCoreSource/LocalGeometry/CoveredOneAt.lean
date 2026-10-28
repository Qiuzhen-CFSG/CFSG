module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredComparisonAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredOne
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaResidualAt

/-!
# The literal covered L₁ normalizer from facts at G,T

The original fixed plane is C_V(L) joined with the escaping point. Weight
separation identifies its normalizer in LT with the point centralizer.
Its two-residual is therefore the literal L₁. Frattini factorization and
the covered Baumann comparison bound N_G(L₁) by N_G(L); the section
centralizer is controlled by the already proved L₀ normalizer.

These are the same proofs as CoveredOne with structural uses restricted to
the original G,T. CoveredPointAt consumes both bounds to exclude the full
L₁ cubic closure. The original five-space, relative normality and quotient
kernels are retained.
Source: Aschbacher--Smith 13.2.2(9), pp.877--878, and 13.3.9, p.887.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable ChapterA.Section04
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem marked_sylow_fixed (D : ChosenModule T L V) (m : CoreMarking D) :
    ∃ P : Sylow 2 (alternatingGroup (Fin 6)), ∀ v : V,
      v.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (m.coordinate v).toAdd =
        (m.coordinate v).toAdd := by
  let X := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_subgroupOf_eq_of_normal N
  let e := subgroupOfEquivOfLe (show L ≤ X from le_sup_left)
  let q : N →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp ((QuotientGroup.mk' (centralCore L)).comp e.toMonoidHom)
  have hq : Function.Surjective q := m.quotient.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.surjective)
  refine ⟨S.mapSurjective hq,?_⟩
  intro v hv a ha
  obtain ⟨b,hb,rfl⟩ := ha
  have hbT : b.val.val ∈ (T : Subgroup G) := by
    rw [hS] at hb
    exact hb
  change BinaryPermutation.coreRepresentation (Fin 6)
    (m.quotient (QuotientGroup.mk' (centralCore L) (e b))).val (m.coordinate v).toAdd = _
  rw [← m.equivariant (e b) v]
  congr 2
  apply Subtype.ext
  change b.val.val * v.val * b.val.val⁻¹ = v.val
  exact mul_inv_eq_iff_eq_mul.mpr
    (((mem_omegaOneCenterAmbient_iff _ _).mp hv).2.2 b.val.val hbT)

omit [Finite G] in
private theorem marked_natural_nonzero (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzL : z.val ∉ centralizer (L : Set G)) :
    BinaryPermutation.coreToNatural (Fin 6) (m.coordinate z).toAdd ≠ 0 := by
  intro he
  apply hzL
  apply (m.mem_fixed_iff z).mpr
  exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val he)

/-- Normalizing the source plane inside LT is the same as centralizing z. -/
private theorem first_flag_normalizer_eq_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    (L ⊔ (T : Subgroup G)) ⊓ normalizer (V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z.val} : Set G) := by
  let W := V ⊓ omegaOneCenterAmbient (T : Subgroup G)
  have hTC : (T : Subgroup G) ≤ centralizer (W : Set G) := by
    intro t ht v hv
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hv.2).2.2 t ht).symm
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (T : Subgroup G) D.sylow_normalizes_component]
      exact hx.1
    obtain ⟨l,hl,t,ht,rfl⟩ := hxprod
    have hln : l ∈ normalizer (W : Set G) := by
      have hh := (normalizer (W : Set G)).mul_mem hx.2
        ((normalizer (W : Set G)).inv_mem (Subgroup.centralizer_le_normalizer _ (hTC ht)))
      simpa only [mul_inv_cancel_right] using hh
    let w := V.normalizerMonoidHom ⟨l,D.normalizes hl⟩ z
    have hw : w.val ∈ W := (mem_normalizer_iff.mp hln z.val).mp ⟨z.property,hz⟩
    obtain ⟨P,hP⟩ := marked_sylow_fixed D m
    have he : w = z := by
      apply m.coordinate.injective
      apply Multiplicative.toAdd.injective
      apply BinaryPermutation.core_sylow_fixed_eq_of_weight P _ _
        (marked_natural_nonzero D m z hzL) (hP z hz) (hP w hw.2)
      rw [m.equivariant ⟨l,hl⟩ z]
      exact (BinaryPermutation.wordWeight_permute
        (m.quotient (QuotientGroup.mk' (centralCore L) ⟨l,hl⟩)).val (m.coordinate z).toAdd.val).symm
    have hlc : l ∈ centralizer ({z.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he))
    exact ⟨hx.1,(centralizer ({z.val} : Set G)).mul_mem hlc (original_sylow_le_centralizer hz ht)⟩
  · intro x hx
    refine ⟨hx.1,?_⟩
    change x ∈ normalizer ((V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) : Set G)
    rw [first_fixed_plane_eq_at h structural D m z hz hzL]
    have hxM : x ∈ normalizer (L : Set G) :=
      (sup_le L.le_normalizer D.sylow_normalizes_component) hx.1
    have hxF := Subgroup.centralizer_le_normalizer _
      (normalizer_component_le_fixed_centralizer_at h structural D m hxM)
    have hxz : x ∈ normalizer (zpowers z.val : Set G) := by
      apply Subgroup.centralizer_le_normalizer _
      rw [zpowers_eq_closure,centralizer_closure]
      exact hx.2
    exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hxF,hxz⟩

omit [Finite G] in
private theorem sectionCentralizer_normalizes_residual
    (X Z : Subgroup G) (hZX : Z ≤ X) (hp : IsPPerfect 2 Z)
    (hn : X.pCoreIn 2 ≤ normalizer (Z : Set G)) :
    twoSectionCentralizer X (normalizer (X : Set G)) ≤ normalizer (Z : Set G) := by
  let Q := X.pCoreIn 2
  let C := twoSectionCentralizer X (normalizer (X : Set G))
  have hCQ : C ≤ normalizer (Q : Set G) :=
    (twoSectionCentralizer_le_normalizer _ _).trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hCZQ : C ≤ normalizer ((Z ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc z hz
    have hm : (Z ⊔ Q).map (MulAut.conj c).toMonoidHom ≤ Z ⊔ Q := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨z,hz,rfl⟩
        have hcomm : ⁅c,z⁆ ∈ Q := hc.2.2 z (hZX hz)
        have hh := (Z ⊔ Q).mul_mem (mem_sup_right hcomm) (mem_sup_left hz)
        change c*z*c⁻¹ ∈ Z ⊔ Q
        simpa only [commutatorElement_def, mul_assoc,
          inv_mul_cancel, mul_one] using hh
      · rintro _ ⟨q,hq,rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hCQ hc) q).mp hq)
    exact hm (mem_map_of_mem (MulAut.conj c).toMonoidHom hz)
  have he : residual (Z ⊔ Q) = Z :=
    embedded_pResidual_join_pGroup Z Q hp (isPGroup_pCoreIn 2 X) hn
  rw [←he]
  exact hCZQ.trans (normalizer_le_residual_normalizer _)

/-- The full covered L₁ is the residual of the original flag normalizer. -/
theorem covered_firstFlagNormalizer_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) =
      firstCentralizerResidual L z.val := by
  have he : parabolic L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G) :=
    (first_flag_normalizer_eq_centralizer_at h structural D m z hzT hzL).trans
      (covered_augmentation_point_parabolic D m hc z hzT hzL).symm
  change (pResidual 2 (parabolic L (T : Subgroup G)
    (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))).map
    (parabolic L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G))).subtype = _
  rw [he]
  exact embedded_pResidual_join_pGroup _ _ (firstCentralizerResidual_twoPerfect L z.val)
    T.isPGroup' (firstCentralizerResidual_sylow_normalizes D hzT)

/-- The original covered L₁ normalizer bound on the augmentation module. -/
theorem covered_firstResidual_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    normalizer (firstCentralizerResidual L z.val : Set G) ≤ normalizer (L : Set G) := by
  let B := firstCentralizerResidual L z.val
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    firstCentralizerResidual_sylow_normalizes D hzT
  have hcore : B.pCoreIn 2 ≤ T := (isPGroup_pCoreIn 2 B).le_sylow_of_normalized T
    (hTB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hC : twoSectionCentralizer B (normalizer (B : Set G)) ≤ normalizer (L : Set G) := by
    apply (sectionCentralizer_normalizes_residual B (zero L)
      (covered_zero_le_firstResidual D m hc z hzL) (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans (D.sylow_normalizes_component.trans (normalizer_le_zero_normalizer L)))).trans
    exact (covered_zero_normalizer h.toHypothesis1221 D.sylow_normalizes_component hc).le
  have hR : normalizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_normalizer_baumann _).trans
      (covered_augmentation_baumann_normalizer_at h structural D m hc z hzT hzL)
  exact (normalizer_core_factorization T B (firstCentralizerResidual_twoPerfect L z.val) hTB).symm.le.trans
    (sup_le hC (inf_le_right.trans hR))

/-- Source 13.2.2(9) for the literal L₁ on the original Sylow-fixed plane. -/
theorem covered_one_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    normalizer (one L (T : Subgroup G)
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) : Set G) ≤ normalizer (L : Set G) := by
  rw [covered_firstFlagNormalizer_residual_at h structural D m hc z hzT hzL]
  exact covered_firstResidual_normalizer_at h structural D m hc z hzT hzL

/-- The ordinary source L₁ is the residual of the same original plane
normalizer, using only structural facts at G,T. -/
theorem ordinary_firstFlagNormalizer_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) =
      firstCentralizerResidual L z.val := by
  have he : parabolic L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G) :=
    (first_flag_normalizer_eq_centralizer_at h structural D m z hzT hzL).trans
      (ordinary_augmentation_point_parabolic D m eL z hzT hzL).symm
  change (pResidual 2 (parabolic L (T : Subgroup G)
    (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))).map
    (parabolic L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G))).subtype = _
  rw [he]
  exact embedded_pResidual_join_pGroup _ _ (firstCentralizerResidual_twoPerfect L z.val)
    T.isPGroup' (firstCentralizerResidual_sylow_normalizes D hzT)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
