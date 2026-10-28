module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Level0
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Level1
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Level2
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Shapes

/-!
# The exact order of the second marked Rudvalis involution centralizer

The certified orbital colors bound the images of points 0 and 1 by sets of
sizes 2240 and 52. Actual words centralizing the original ATLAS generator a
realize both sets and fix the earlier point. The checked two-point rigidity
makes their products a bijection with the full literal centralizer.
Consequently its order is 116480 and is indivisible by three, hence by nine.
No centralizer product decomposition or ambient simplicity is assumed.

Source: ATLAS RuG1-p4060B0, with conventions and attribution in
Model.PermutationData; GLS3 Table 5.3r; Aschbacher–Smith, Quasithin
16.1.5(11), used in E.6.18 and E.6.23. Reproduction data are in Second/source/.
-/

namespace Rudvalis.InvolutionCentralizers
open Subgroup OuterNormalizer SecondCertificate

private theorem preserves (g : Model) : g.val ∈ relationAut :=
  model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.property

private theorem commutes (g : Model) (hg : g ∈ Centralizer a) :
    ∀ x, g.val (aPerm x) = aPerm (g.val x) := by
  intro x
  exact congrArg (fun t : Model => t.val x) (mem_centralizer_singleton_iff.mp hg)

private theorem fix_two (g : Model) (hg : g ∈ Centralizer a)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) : g = 1 := by
  apply Subtype.ext
  apply fix_two_eq_one g.val (preserves g) (commutes g hg)
  intro x hx
  have he : x = 0 ∨ x = 1 := by
    have he : x.val = 0 ∨ x.val = 1 := by omega
    exact he.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  rcases he with rfl | rfl
  · exact h0
  · exact h1

private theorem eq_of_two (g h : Model) (hg : g ∈ Centralizer a) (hh : h ∈ Centralizer a)
    (h0 : g.val 0 = h.val 0) (h1 : g.val 1 = h.val 1) : g = h := by
  have he : h⁻¹ * g = 1 := by
    apply fix_two _ ((Centralizer a).mul_mem ((Centralizer a).inv_mem hh) hg)
    · change h⁻¹ • (g • (0 : Fin 4060)) = 0
      change g • (0 : Fin 4060) = h • (0 : Fin 4060) at h0
      rw [h0,inv_smul_smul]
    · change h⁻¹ • (g • (1 : Fin 4060)) = 1
      change g • (1 : Fin 4060) = h • (1 : Fin 4060) at h1
      rw [h1,inv_smul_smul]
  exact (inv_mul_eq_one.mp he).symm

private def pair (v : Fin 2240 × Fin 52) : Centralizer a :=
  ⟨rep0 v.1 * rep1 v.2,(Centralizer a).mul_mem (rep0_mem _) (rep1_mem _)⟩

private theorem pair_injective : Function.Injective pair := by
  rintro ⟨i,j⟩ ⟨k,l⟩ he
  have hh : rep0 i * rep1 j = rep0 k * rep1 l := congrArg Subtype.val he
  have h0 := congrArg (fun g : Model => g.val 0) hh
  change (rep0 i).val ((rep1 j).val 0) = (rep0 k).val ((rep1 l).val 0) at h0
  rw [rep1_fix,rep1_fix,rep0_point,rep0_point] at h0
  have hi : i = k := by
    have hp := congrArg pointInv0 h0
    simpa only [point0_left] using hp
  subst k
  have hl : rep1 j = rep1 l := mul_left_cancel hh
  have h1 := congrArg (fun g : Model => g.val 1) hl
  rw [rep1_point,rep1_point] at h1
  have hj : j = l := by
    have hp := congrArg pointInv1 h1
    simpa only [point1_left] using hp
  subst l
  rfl

private theorem pair_surjective : Function.Surjective pair := by
  intro g
  obtain ⟨i,hi⟩ := image0_mem_range g.val.val (preserves g.val) (commutes g.val g.property)
    (fun _ hx => by omega)
  let q : Model := (rep0 i)⁻¹ * g.val
  have hq : q ∈ Centralizer a :=
    (Centralizer a).mul_mem ((Centralizer a).inv_mem (rep0_mem i)) g.property
  have hq0 : q.val 0 = 0 := by
    change (rep0 i)⁻¹ • (g.val • (0 : Fin 4060)) = 0
    apply inv_smul_eq_iff.mpr
    exact hi.symm.trans (rep0_point i).symm
  obtain ⟨j,hj⟩ := image1_mem_range q.val (preserves q) (commutes q hq) (by
    intro x hx
    have he : x = 0 := Fin.ext (by omega)
    subst x
    exact hq0)
  have he : q = rep1 j := eq_of_two q (rep1 j) hq (rep1_mem j)
    (hq0.trans (rep1_fix j).symm) (hj.symm.trans (rep1_point j).symm)
  refine ⟨(i,j),Subtype.ext ?_⟩
  change rep0 i * rep1 j = g.val
  rw [←he]
  exact mul_inv_cancel_left _ _

public theorem second_centralizer_card : Nat.card (Centralizer a) = 116480 := by
  rw [←Nat.card_congr (Equiv.ofBijective pair ⟨pair_injective,pair_surjective⟩),Nat.card_prod,
    Nat.card_fin,Nat.card_fin]

public theorem second_centralizer_not_three : ¬ 3 ∣ Nat.card (Centralizer a) := by
  rw [second_centralizer_card]
  decide

public theorem second_centralizer_not_nine : ¬ 9 ∣ Nat.card (Centralizer a) := by
  rw [second_centralizer_card]
  decide
end Rudvalis.InvolutionCentralizers
