module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagCore

/-!
# The original first flag with guarded structural inputs

Weight separation in the original five-dimensional core identifies N_LT(V1)
with C_LT(z). The ordinary centralizer calculation then gives L1T and recovers
its literal two-residual O^{3'}(C_L(z)). These equalities feed the second
Goldschmidt triple without a universal structural record.
Source: Aschbacher--Smith 13.2.1, 13.3.4 and 13.4.7(3), pp.877,885,903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
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
theorem first_flag_normalizer_eq_centralizer_at
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

/-- The source first flag normalizer is the literal residual parabolic. -/
theorem first_flag_normalizer_eq_firstResidual_sylow_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    (L ⊔ (T : Subgroup G)) ⊓ normalizer (V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G) :=
  (first_flag_normalizer_eq_centralizer_at h structural D m z hz hzL).trans
    (local_centralizer_eq_firstResidual_sylow D m e z hz hzL)


/-- The original two-residual definition of L₁ agrees with O^{3′}(C_L(z)). -/
theorem firstFlagNormalizer_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    (pResidual 2 (firstFlagNormalizer T L V)).map (firstFlagNormalizer T L V).subtype =
      firstCentralizerResidual L z.val := by
  have he := first_flag_normalizer_eq_firstResidual_sylow_at h structural D m e z hz hzL
  change firstFlagNormalizer T L V = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) at he
  rw [he]
  exact embedded_pResidual_join_pGroup _ _ (firstCentralizerResidual_twoPerfect L z.val)
    T.isPGroup' (firstCentralizerResidual_sylow_normalizes D hz)


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
