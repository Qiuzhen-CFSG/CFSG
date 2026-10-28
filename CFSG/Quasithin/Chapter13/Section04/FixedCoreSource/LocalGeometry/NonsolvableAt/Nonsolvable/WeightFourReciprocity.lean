module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.Rank
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourReciprocity
public import Theory.Representation.BinaryPermutation.SixCoreWeightFour
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearIndices
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Rank

/-!
# The mutual-normalization step in product weak closure: structure at the original group

Weight-four commutators make sign faithful on the actual permutation image,
so that image has order at most two. A nontrivial such action has fixed
index at least four. Applying these inequalities on both sides shows that
mutually normalizing conjugates of the original augmentation core commute.
The source application obtains every intersection weight from the unique
escaping point and the original normalizer-fusion theorem.

This proves the first conjugate-exclusion step in the weak-closure claim
inside Aschbacher–Smith 13.4.16, printed p.913. It does not assert that an
arbitrary conjugate contained in M commutes with V: that remaining case
requires the rank-three action and its fixed-space family.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/WeightFourReciprocity` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The two literal indices when every nontrivial commutator has weight four. -/
theorem core_weight_four_actor_indices_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAM : A ≤ normalizer (L : Set G))
    (hw : ∀ v : V, v.val ∈ ⁅V,A⁆ → v ≠ 1 → m.weight v = 4) :
    (centralizer (V : Set G)).relIndex A ≤ 2 ∧
      (⁅V,A⁆ ≠ ⊥ → 4 ≤ (centralizer (A : Set G)).relIndex V) := by
  have hn := normalizer_component_le_module_at h structural D m
  obtain ⟨q,hq,_,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hAM)
  have hf (a : A) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨a.val,(hAM.trans hn) a.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (f a) (m.coordinate v).toAdd :=
    hq (inclusion hAM a) v
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hweights : ∀ a ∈ f.range, ∀ v : BinaryPermutation.core (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a v ≠ v →
      BinaryPermutation.wordWeight (BinaryPermutation.coreRepresentation (Fin 6) a v - v).val = 4 := by
    rintro _ ⟨a,rfl⟩ v hv
    let w := m.coordinate.symm (Multiplicative.ofAdd v)
    let c : V := V.normalizerMonoidHom ⟨a.val,(hAM.trans hn) a.property⟩ w * w⁻¹
    have hc : (m.coordinate c).toAdd = BinaryPermutation.coreRepresentation (Fin 6) (f a) v - v := by
      change (m.coordinate (V.normalizerMonoidHom _ w * w⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul, toAdd_inv, ←sub_eq_add_neg]
      change (m.coordinate (V.normalizerMonoidHom _ w)).toAdd - (m.coordinate w).toAdd = _
      rw [hf]
      simp only [w,m.coordinate.apply_symm_apply,toAdd_ofAdd]
    have hcV : c.val ∈ ⁅V,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator a.property w.property
    have hc1 : c ≠ 1 := by
      intro he
      rw [he,map_one] at hc
      exact hv (sub_eq_zero.mp hc.symm)
    have hh := hw c hcV hc1
    change BinaryPermutation.wordWeight (m.coordinate c).toAdd.val = 4 at hh
    rwa [hc] at hh
  have hcard := model_card_range A V (hAM.trans hn)
    (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
    f m.coordinate hf
  rw [inf_relIndex_left] at hcard
  refine ⟨hcard ▸ BinaryPermutation.SixCoreWeightFour.card_le_two f.range hweights,?_⟩
  intro hmove
  have hne : f.range ≠ ⊥ := by
    intro he
    have hc : (centralizer (V : Set G)).relIndex A = 1 := by
      rw [←hcard,he,card_bot]
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (relIndex_eq_one.mp hc)))
  have hd := BinaryPermutation.SixCoreWeightFour.fixedCodim_two_le f.range hne hweights
  rw [model_fixed_index A V (hAM.trans hn) (BinaryPermutation.coreRepresentation (Fin 6))
    f m.coordinate hf]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hd

omit [Finite G] in
private theorem centralizer_index_conj_at (A B : Subgroup G) (g : G) :
    (centralizer (A.conjBy g : Set G)).relIndex (B.conjBy g) =
      (centralizer (A : Set G)).relIndex B := by
  change (centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
    (B.map (MulAut.conj g).toMonoidHom) = _
  rw [coe_map, MulEquiv.coe_toMonoidHom, ← Theory.GroupTheory.map_centralizer_equiv (A : Set G) (MulAut.conj g)]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

/-- An intersection section acting on the full original core has image
of order at most two when the opposite conjugate normalizes it. -/
theorem weight_four_section_actor_index_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hinter : ∀ y : G, y ∉ normalizer (L : Set G) → ∀ v : V,
      v ≠ 1 → v.val ∈ V.conjBy y → m.weight v = 4)
    (y : G) (hy : y ∉ normalizer (L : Set G))
    (A : Subgroup G) (hAy : A ≤ V.conjBy y)
    (hAM : A ≤ normalizer (L : Set G))
    (hVM : V ≤ (normalizer (L : Set G)).conjBy y) :
    (centralizer (V : Set G)).relIndex A ≤ 2 := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAy
  have hn := normalizer_component_le_module_at h structural D m
  have hVy : V ≤ normalizer (V.conjBy y : Set G) := by
    have hh := map_mono (f := (MulAut.conj y).toMonoidHom) hn
    rw [map_equiv_normalizer_eq V] at hh
    exact hVM.trans hh
  exact (core_weight_four_actor_indices_at h structural D m A hAM
    (fun v hv hv1 => hinter y hy v hv1
      (le_normalizer_iff_commutator_le_right.mp hVy
        (commutator_mono le_rfl hAy hv)))).1

/-- In the weight-four branch, mutually normalizing original conjugates commute. -/
theorem weight_four_conjugates_commute_of_mutual_normalization_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hinter : ∀ y : G, y ∉ normalizer (L : Set G) → ∀ v : V,
      v ≠ 1 → v.val ∈ V.conjBy y → m.weight v = 4)
    (y : G) (h₁ : V.conjBy y ≤ normalizer (L : Set G))
    (h₂ : V ≤ (normalizer (L : Set G)).conjBy y) : ⁅V,V.conjBy y⁆ = ⊥ := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (V.conjBy y⁻¹) := IsElementaryAbelian.map _
  have hn := normalizer_component_le_module_at h structural D m
  by_cases hy : y ∈ normalizer (L : Set G)
  · have he : V.conjBy y = V := mem_normalizer_iff_map_conj_eq.mp (hn hy)
    rw [he]
    exact commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer
  have hyi : y⁻¹ ∉ normalizer (L : Set G) := fun hi => hy (inv_mem_iff.mp hi)
  have h₂' : V.conjBy y⁻¹ ≤ normalizer (L : Set G) := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) h₂
    change V.conjBy y⁻¹ ≤ ((normalizer (L : Set G)).conjBy y).conjBy y⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hVN : V ≤ normalizer (V.conjBy y : Set G) := by
    have hh := map_mono (f := (MulAut.conj y).toMonoidHom) hn
    rw [map_equiv_normalizer_eq V] at hh
    exact h₂.trans hh
  have hViN : V ≤ normalizer (V.conjBy y⁻¹ : Set G) := by
    have hh := map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) (h₁.trans hn)
    rw [map_equiv_normalizer_eq] at hh
    change (V.conjBy y).conjBy y⁻¹ ≤ normalizer (V.conjBy y⁻¹ : Set G) at hh
    rwa [conjBy_inv] at hh
  have hb := core_weight_four_actor_indices_at h structural D m (V.conjBy y) h₁
    (fun v hv hv1 => hinter y hy v hv1 (le_normalizer_iff_commutator_le_right.mp hVN hv))
  have hb' := core_weight_four_actor_indices_at h structural D m (V.conjBy y⁻¹) h₂'
    (fun v hv hv1 => hinter y⁻¹ hyi v hv1 (le_normalizer_iff_commutator_le_right.mp hViN hv))
  by_contra hmove
  have hlo := hb.2 hmove
  have hc := centralizer_index_conj_at V (V.conjBy y⁻¹) y
  rw [conjBy_inv'] at hc
  have hhi := hb'.1
  rw [←hc] at hhi
  omega
/-- The actual weight-four product branch supplies the intersection
hypothesis from the unique escaping point and original normalizer fusion. -/
theorem original_weight_four_mutual_conjugates_commute_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hweight : m.weight z = 4)
    (y : G) (h₁ : V.conjBy y ≤ normalizer (L : Set G))
    (h₂ : V ≤ (normalizer (L : Set G)).conjBy y) : ⁅V,V.conjBy y⁆ = ⊥ := by
  apply weight_four_conjugates_commute_of_mutual_normalization_at h structural D m ?_ y h₁ h₂
  intro a ha v hv hvA
  exact (m.conjugate_intersection_weight_of_unique_escape_at h structural z hz1 hzT hzout
    hunique hfusion a ha v hv hvA).trans hweight
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
