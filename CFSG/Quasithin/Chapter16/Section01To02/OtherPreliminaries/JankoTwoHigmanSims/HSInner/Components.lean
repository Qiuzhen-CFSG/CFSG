module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.KernelExclusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# Components and index in the noncentral HS inner alternative

The product C₂ × Aut(A₆) has a normal quasisimple copy of A₆. Component
calculus puts any component inside it or in its centralizer. The latter
centralizer lies in C₂, because an automorphism commuting with all inner
automorphisms of the centerless A₆ fixes each element of A₆. Perfectness
excludes that case. Hence every component is actually isomorphic to A₆.

The checked orders 44352000 and 2 · 1440 give index 15400, divisible by four.
An isomorphism with the actual HS fixed subgroup remains explicit.
Source: Aschbacher–Smith, 16.1.5(10), 16.1.7(h) and 16.1.8, pp.1172–1173.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS

private def componentEmbedding : A6 →* C2 × MulAut A6 :=
  (1 : A6 →* C2).prod MulAut.conj

private theorem componentEmbedding_injective : Function.Injective componentEmbedding := by
  intro a b h
  exact AlternatingSix.ShadowLocal.inner_injective (congrArg Prod.snd h)

private theorem componentEmbedding_normal : componentEmbedding.range.Normal := by
  constructor
  rintro _ ⟨a, rfl⟩ g
  refine ⟨g.2 a, ?_⟩
  apply Prod.ext
  · simp [componentEmbedding]
  · change MulAut.conj (g.2 a) = g.2 * MulAut.conj a * g.2⁻¹
    ext x
    simp

private theorem componentEmbedding_isComponent :
    IsComponent (C2 × MulAut A6) componentEmbedding.range := by
  let : IsQuasisimple A6 := GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 1
  exact ⟨componentEmbedding_normal.isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective componentEmbedding_injective)⟩

/-- Every component of the source product centralizer is the normal A₆ factor. -/
theorem product_component_equiv (K : Subgroup (C2 × MulAut A6)) (hK : IsComponent (C2 × MulAut A6) K) :
    Nonempty (K ≃* A6) := by
  let : componentEmbedding.range.Normal := componentEmbedding_normal
  rcases hK.normal_dichotomy componentEmbedding.range with hle | hc
  · have heq := hK.eq_of_le componentEmbedding_isComponent hle
    exact ⟨(MulEquiv.subgroupCongr heq).trans
      (MonoidHom.ofInjective componentEmbedding_injective).symm⟩
  · have hsnd (k : K) : k.val.2 = 1 := by
      apply MulEquiv.ext
      intro a
      apply AlternatingSix.ShadowLocal.inner_injective
      have hm := (commutator_eq_bot_iff_le_centralizer.mp hc) k.property
        (componentEmbedding a) ⟨a, rfl⟩
      have hma : MulAut.conj a * k.val.2 = k.val.2 * MulAut.conj a := congrArg Prod.snd hm
      calc
        MulAut.conj (k.val.2 a) = k.val.2 * MulAut.conj a * k.val.2⁻¹ := by
          ext x
          simp
        _ = MulAut.conj a := by rw [← hma]; simp [mul_assoc]
    let f : K →* C2 := (MonoidHom.fst C2 (MulAut A6)).comp K.subtype
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact Prod.ext h ((hsnd x).trans (hsnd y).symm)
    let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hf
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

/-- The noncentral product centralizer has index 15400 in the exact HS carrier. -/
theorem fixed_index_of_equiv (r : MulAut Carrier) (e : r.fixedSubgroup ≃* C2 × MulAut A6) :
    r.fixedSubgroup.index = 15400 := by
  have hc : Nat.card r.fixedSubgroup = 2880 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have h2 : Nat.card C2 = 2 := by
      change Nat.card (Multiplicative (ZMod 2)) = 2
      simp
    rw [h2, AlternatingSix.ShadowLocal.card_aut]
  have h := r.fixedSubgroup.card_mul_index
  rw [hc, NormalizerIndex.card_carrier] at h
  omega

/-- An actual fixed-subgroup isomorphism identifies each component with A₆. -/
theorem component_equiv_of_fixed_equiv (r : MulAut Carrier)
    (e : r.fixedSubgroup ≃* C2 × MulAut A6) (K : Subgroup r.fixedSubgroup)
    (hK : IsComponent r.fixedSubgroup K) : Nonempty (K ≃* A6) := by
  obtain ⟨f⟩ := product_component_equiv (K.map e.toMonoidHom) (hK.map_equiv e)
  exact ⟨(e.subgroupMap K).trans f⟩

/-- In the product case the ambient fixed-subgroup index is divisible by four. -/
theorem four_dvd_fixed_index_of_equiv (r : MulAut Carrier)
    (e : r.fixedSubgroup ≃* C2 × MulAut A6) : 4 ∣ r.fixedSubgroup.index := by
  rw [fixed_index_of_equiv r e]
  decide

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
