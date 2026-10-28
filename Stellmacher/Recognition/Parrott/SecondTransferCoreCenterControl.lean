module
public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Theory.GroupTheory.WeakClosurePairFusion

/-!
# Core-center control in Parrott's second transfer quotient

In the second transfer Sylow subgroup, the three nonidentity elements of
Z(O₂(N_G(F))) are exactly the elements conjugate in G to z. This follows
from Ω₁(Y)=F and the two distinct ambient fusion classes in F. Sylow
conjugacy consequently makes its core center stable under the normalizer
of every two-subgroup containing it. Taking preimages proves the same
normalizer control after quotienting by a two-kernel.

This is the normalizer-control part of Parrott's observation (i), with the
literal embedding and quotient retained. It uses the supplied local fusion
data and makes no assumption that G is an N₂-group.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
printed p. 683, proof of Lemma 8.
-/

public section
open Subgroup
open scoped Pointwise
namespace Stellmacher.Recognition.ParrottNormalizerFusionData
variable {G : Type*} [Group G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

private theorem fusion_defined_two_overgroup
    {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) (E : Subgroup A)
    (hES : E ≤ (S : Subgroup A)) (p : A → Prop)
    (hp : ∀ g x : A, p (g * x * g⁻¹) ↔ p x)
    (hE : ∀ x ∈ (S : Subgroup A), x ∈ E ↔ p x)
    (R : Subgroup A) (hR : IsPGroup 2 R) (hER : E ≤ R) :
    ∀ x ∈ R, x ∈ E ↔ p x := by
  obtain ⟨T,hT⟩ := hR.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A T S
  have hRS : R.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup A) := by
    rw [← hg]
    exact map_mono hT
  have hEE : E.map (MulAut.conj g).toMonoidHom = E := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨e,he,rfl⟩
      exact (hE _ (hRS (mem_map_of_mem _ (hER he)))).mpr
        ((hp g e).mpr ((hE e (hES he)).mp he))
    · rw [card_map_of_injective (MulAut.conj g).injective]
  have hgE := mem_normalizer_iff_map_conj_eq.mpr hEE
  intro x hx
  exact (mem_normalizer_iff.mp hgE x).trans
    ((hE _ (hRS (mem_map_of_mem _ hx))).trans (hp g x))

private theorem fusion_defined_normalizer
    {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) (E : Subgroup A)
    (hES : E ≤ (S : Subgroup A)) (p : A → Prop)
    (hp : ∀ g x : A, p (g * x * g⁻¹) ↔ p x)
    (hE : ∀ x ∈ (S : Subgroup A), x ∈ E ↔ p x)
    (R : Subgroup A) (hR : IsPGroup 2 R) (hER : E ≤ R) :
    normalizer (R : Set A) ≤ normalizer (E : Set A) := by
  have he := fusion_defined_two_overgroup S E hES p hp hE R hR hER
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact (he _ ((mem_normalizer_iff.mp hg x).mp (hER hx))).mpr
      ((hp g x).mpr ((he x (hER hx)).mp hx))
  · intro hx
    have hxR := (mem_normalizer_iff.mp hg x).mpr (hER hx)
    exact (he x hxR).mpr ((hp g x).mp ((he _ (hER hx)).mp hx))

include n in
/-- Ambient fusion identifies the core center inside the second-transfer Sylow subgroup. -/
theorem second_transfer_core_center_fusion
    (h : ParrottCentralizerHypotheses z)
    {A : Type*} [Group A] [Finite A]
    (f : A →* G) (hf : Function.Injective f) (S : Sylow 2 A)
    (hOmega : (omega₁ ((S : Subgroup A).map f) (p := 2)).map
      ((S : Subgroup A).map f).subtype = d.F) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let E := ZK.comap f
    E ≤ (S : Subgroup A) ∧
      ∀ x ∈ (S : Subgroup A), x ∈ E ↔ x = 1 ∨ IsConj z (f x) := by
  intro N K ZK E
  let Y := (S : Subgroup A).map f
  have hFY : d.F ≤ Y := by rw [←hOmega]; exact map_subtype_le _
  have hZF : ZK ≤ d.F := n.core_center_le_omega_center.trans
    (n.omega_center_le_inf.trans inf_le_right)
  have hES : E ≤ (S : Subgroup A) := by
    intro x hx
    obtain ⟨s,hs,he⟩ := hFY (hZF hx)
    exact hf he ▸ hs
  refine ⟨hES,?_⟩
  intro x hx
  constructor
  · intro hxE
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      let : IsElementaryAbelian 2 d.F := d.elementary
      have hfx2 : orderOf (f x) = 2 := orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (f x) (hZF hxE))
        (fun he => hx1 (hf (he.trans f.map_one.symm)))
      obtain ⟨g,hg⟩ := n.core_center_fusion (f x) hxE hfx2
      exact isConj_iff.mpr ⟨g,hg⟩
  · rintro (rfl | hzx)
    · exact E.one_mem
    · have hfx2 : (f x)^2 = 1 := by
        obtain ⟨g,hg⟩ := isConj_iff.mp hzx
        rw [←hg]
        change (MulAut.conj g z)^2 = 1
        rw [←map_pow,show z^2=1 from h.involution ▸ pow_orderOf_eq_one z,map_one]
      have hfxF : f x ∈ d.F := by
        rw [←hOmega]
        refine ⟨⟨f x,mem_map_of_mem f hx⟩,subset_closure ?_,rfl⟩
        exact Subtype.ext hfx2
      by_contra hn
      obtain ⟨g,hg⟩ := n.elementary_fusion (f x) hfxF hn
      exact n.not_isConj (hzx.trans (isConj_iff.mpr ⟨(g:G),hg⟩).symm)

include n in
/-- A two-overgroup of the core center has its normalizer in the core-center normalizer. -/
theorem second_transfer_two_overgroup_normalizer
    (h : ParrottCentralizerHypotheses z)
    {A : Type*} [Group A] [Finite A]
    (f : A →* G) (hf : Function.Injective f) (S : Sylow 2 A)
    (hOmega : (omega₁ ((S : Subgroup A).map f) (p := 2)).map
      ((S : Subgroup A).map f).subtype = d.F) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let E := ((center K).map (N.subtype.comp K.subtype)).comap f
    ∀ R : Subgroup A, IsPGroup 2 R → E ≤ R →
      normalizer (R : Set A) ≤ normalizer (E : Set A) := by
  intro N K E R hR hER
  obtain ⟨hES,hE⟩ := n.second_transfer_core_center_fusion h f hf S hOmega
  apply fusion_defined_normalizer S E hES (fun x => x=1 ∨ IsConj z (f x)) _ hE R hR hER
  intro g x
  have hconj : IsConj (f x) (f (g*x*g⁻¹)) :=
    isConj_iff.mpr ⟨f g,by simp only [map_mul,map_inv]⟩
  constructor
  · rintro (he | hc)
    · left
      exact (MulAut.conj g).injective (he.trans (map_one _).symm)
    · exact Or.inr (hc.trans hconj.symm)
  · rintro (rfl | hc)
    · exact Or.inl (by simp)
    · exact Or.inr (hc.trans hconj)


include n in
/-- Core-center normalizer control descends along the actual second-transfer quotient. -/
theorem second_transfer_quotient_two_overgroup_normalizer
    (h : ParrottCentralizerHypotheses z)
    {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* G) (hf : Function.Injective f) (S : Sylow 2 A)
    (hOmega : (omega₁ ((S : Subgroup A).map f) (p := 2)).map
      ((S : Subgroup A).map f).subtype = d.F)
    (q : A →* B) (hq : Function.Surjective q) (hker : IsPGroup 2 q.ker) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let E := ((center K).map (N.subtype.comp K.subtype)).comap f
    ∀ R : Subgroup B, IsPGroup 2 R → E.map q ≤ R →
      normalizer (R : Set B) ≤ normalizer (E.map q : Set B) := by
  intro N K E R hR hER b hb
  obtain ⟨a,rfl⟩ := hq b
  have ha : a ∈ normalizer (R.comap q : Set A) := by
    rw [←comap_normalizer_eq_of_surjective R hq]
    exact hb
  have haE := n.second_transfer_two_overgroup_normalizer h f hf S hOmega
    (R.comap q) (hR.comap_of_ker_isPGroup q hker) (map_le_iff_le_comap.mp hER) ha
  exact E.le_normalizer_map q (mem_map_of_mem q haE)

end Stellmacher.Recognition.ParrottNormalizerFusionData
