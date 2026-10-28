module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.CartanNormalizer
public import Theory.SpecificGroups.ReeF4.SmallCompletion.TorusAction
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Parabolics

/-!
# Cartan-normalizing parabolic reflections in the general Ree group

The full Cartan normalizer calculation and the native BN-pair identify its
intersection with each parabolic: outside the Borel, an element is a torus
multiple of that side's marked reflection. Any product from the two such
cosets has eighth power one. Indeed its fourth power differs from the native
half-turn by a torus element, and the half-turn inverts the entire torus.

This relation is the native algebra needed to extend compatible parabolic
actions after their common Cartan has been aligned. It is not a relation in
an arbitrary completion. Every positive parameter, including q=8, is retained.
Source: GLS3 2.3.4 and Table 2.4; Aschbacher–Smith F.4.3,10,16,
printed pp.274,279,282 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup Parabolics LargeLocalSeeds SectionGeometry.BNPair
open Parabolics.Binary.FixedGeometry
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
attribute [local instance] borel_inf_normalizerWords_normal

private theorem quotient_mem_torus {m : ℕ} (x : normalizerWords m)
    (hx : QuotientGroup.mk' ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)) x = 1) :
    x.val ∈ fixedTorus m := by
  have hh := (QuotientGroup.eq_one_iff x).mp hx
  change x.val ∈ borel m ⊓ normalizerWords m at hh
  rwa [borel_inf_normalizerWords] at hh

private theorem closure_involution {A : Type*} [Group A] (s : A) (hs : s^2=1)
    {w : A} (hw : w∈closure ({s} : Set A)) : w=1 ∨ w=s := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
  | one => exact Or.inl rfl
  | mul a b ha hb iha ihb =>
    rcases iha with rfl | rfl <;> rcases ihb with rfl | rfl <;> simp_all [pow_two]
  | inv a ha iha =>
    rcases iha with rfl | rfl <;> simp_all [pow_two, mul_eq_one_iff_inv_eq]

/-- The full Cartan normalizer in a parabolic has exactly its two native Weyl cosets. -/
theorem parabolic_torus_normalizer_factor {m : ℕ} (hm : 0<m) (s : Side)
    (x : Model m) (hx : x∈parabolic m s)
    (hn : x∈normalizer (fixedTorus m : Set (Model m))) (hb : x∉borel m) :
    ∃ t∈fixedTorus m, x=t*(SmallCompletion.reflection m s).val := by
  have hn' : x∈normalizerWords m := (normalizer_fixedTorus_eq_words hm).le hn
  let n : normalizerWords m := ⟨x,hn'⟩
  let T := titsSystem m
  let q := QuotientGroup.mk' ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m))
  have hp : x∈T.standardParabolic {simpleReflection m s} := by
    rw [standardParabolic_singleton_eq_parabolic m hm,parabolic_eq_rootParabolic]
    exact hx
  obtain ⟨w,hw,hxw⟩ := (T.mem_standardParabolic_iff
    (Set.singleton_subset_iff.mpr (simpleReflection_mem m s)) x).mp hp
  have hqw : q n=w := T.doubleCoset_index_unique
    (T.representative_mem_bruhatCell (q n) n rfl) hxw
  have hqs : q n=simpleReflection m s := by
    rcases closure_involution _ (simpleReflection_sq m s) hw with hw | hw
    · exact (hb (fixedTorus_le_borel m (quotient_mem_torus n (hqw.trans hw)))).elim
    · exact hqw.trans hw
  let t := n*(simpleLift m s)⁻¹
  have ht : t.val∈fixedTorus m := quotient_mem_torus t (by
    change q (n*(simpleLift m s)⁻¹)=1
    rw [map_mul,map_inv,hqs]
    exact mul_inv_cancel _)
  refine ⟨t.val,ht,?_⟩
  change x=(x*(weylLift m s)⁻¹)*weylLift m s
  simp only [inv_mul_cancel_right]

/-- Any pair in the two Cartan-normalizer reflection cosets retains the
native eighth-power relation, with arbitrary torus factors. -/
theorem torus_reflection_product_eight {m : ℕ} (hm : 0<m)
    (x y : Model m) (hx : x∈parabolic m .linear) (hy : y∈parabolic m .suzuki)
    (hxn : x∈normalizer (fixedTorus m : Set (Model m)))
    (hyn : y∈normalizer (fixedTorus m : Set (Model m)))
    (hxb : x∉borel m) (hyb : y∉borel m) : (x*y)^8=1 := by
  obtain ⟨a,ha,rfl⟩ := parabolic_torus_normalizer_factor hm .linear x hx hxn hxb
  obtain ⟨b,hb,rfl⟩ := parabolic_torus_normalizer_factor hm .suzuki y hy hyn hyb
  let w₁ := SmallCompletion.reflection m .linear
  let w₂ := SmallCompletion.reflection m .suzuki
  let u : normalizerWords m := ⟨(a*w₁.val)*(b*w₂.val),
    mul_mem (mul_mem (fixedTorus_le_normalizerWords m ha) (weylLift_mem_normalizerWords m .linear))
      (mul_mem (fixedTorus_le_normalizerWords m hb) (weylLift_mem_normalizerWords m .suzuki))⟩
  let w : normalizerWords m := simpleLift m .linear * simpleLift m .suzuki
  let q := QuotientGroup.mk' ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m))
  have hq (t : Model m) (ht : t∈fixedTorus m) :
      q ⟨t,fixedTorus_le_normalizerWords m ht⟩=1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨fixedTorus_le_borel m ht,fixedTorus_le_normalizerWords m ht⟩
  have huq : q u=q w := by
    change q ((⟨a,fixedTorus_le_normalizerWords m ha⟩*simpleLift m .linear)*
      (⟨b,fixedTorus_le_normalizerWords m hb⟩*simpleLift m .suzuki))=q _
    simp only [map_mul,hq a ha,hq b hb,one_mul,w]
  let c := u^4*(w^4)⁻¹
  have hc : c.val∈fixedTorus m := quotient_mem_torus c (by
    change q (u^4*(w^4)⁻¹)=1
    rw [map_mul,map_inv,map_pow,map_pow,huq,mul_inv_cancel])
  have hu : (u.val)^4=c.val*(w.val)^4 := by
    change (u.val)^4=((u.val)^4*((w.val)^4)⁻¹)*(w.val)^4
    simp only [inv_mul_cancel_right]
  have hw : (w.val)^8=1 := SmallCompletion.reflection_product_eight m
  have hcw : (w.val)^4*c.val*((w.val)^4)⁻¹=c.val⁻¹ :=
    SmallCompletion.reflection_product_four_inverts m ⟨c.val,hc⟩
  change u.val^8=1
  calc
    _ = (u.val^4)^2 := by rw [←pow_mul]
    _ = (c.val*w.val^4)^2 := by rw [hu]
    _ = c.val*(w.val^4*c.val*(w.val^4)⁻¹)*(w.val)^8 := by
      rw [show (8:ℕ)=4+4 from rfl,pow_add,pow_two]
      group
    _ = 1 := by rw [hcw,hw,mul_inv_cancel,mul_one]
end ReeF4.SourceCompletion
