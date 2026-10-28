module
public import Theory.SpecificGroups.MinusExtraspecial.CentralStructure
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.SpecificGroups.MinusExtraspecial.Factors
public import Theory.GroupTheory.QuaternionDihedralInvolutionCosets
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Fusion of involutions in a minus extraspecial core

For a self-centralizing two-core isomorphic to Q₈ * D₈, the action on
its five singular central cosets has exactly the core as kernel. If the
quotient order is divisible by five, the noncentral core involutions form
one class in the overgroup. A returning conjugate of the central involution
then fuses all core involutions in an ambient group, retaining the embedding.

Source: Aschbacher, *Sporadic Groups* (1994), 46.1(2), p.251;
Aschbacher–Smith 14.2.17, printed pp.986–987.
-/

public noncomputable section
open Subgroup
namespace MinusExtraspecial
variable {H : Type*} [Group H] [Finite H]

private theorem quotientAut_kernel_congr {Q : Type*} [Group Q]
    (U V : Subgroup Q) [U.Characteristic] [V.Characteristic] (h : U = V) :
    (quotientAut U).ker = (quotientAut V).ker := by subst V; rfl

/-- Noncentral involutions in a minus core fuse in its overgroup when five
acts on the core's central quotient. -/
theorem pCore_noncentral_involutions_isConj
    (he : Nonempty (pCore 2 H ≃* Model))
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfive : 5 ∣ (pCore 2 H).index)
    (x y : pCore 2 H) (hx : orderOf x = 2) (hxZ : x ∉ center (pCore 2 H))
    (hy : orderOf y = 2) (hyZ : y ∉ center (pCore 2 H)) : IsConj (x:H) (y:H) := by
  obtain ⟨e⟩ := he
  let : IsExtraspecial 2 (pCore 2 H) := IsExtraspecial.of_mulEquiv e.symm inferInstance
  obtain ⟨B,C,hB,hC,hcomm,hgen⟩ := factors_of_equiv e
  have hcard : Nat.card (pCore 2 H) = 32 := (Nat.card_congr e.toEquiv).trans card_model
  have hpoints := quaternion_dihedral_central_involution_cosets_card hcard B C hB hC hcomm hgen
  have hker : ((centralInvolutionCosetAction (H := pCore 2 H)).comp
      (MulAut.conjNormal : H →* MulAut (pCore 2 H))).ker = pCore 2 H := by
    rw [← MonoidHom.comap_ker,
      quaternion_dihedral_central_involution_coset_kernel B C hB hC hcomm hgen,
      ← quotientAut_kernel_congr (frattini (pCore 2 H)) (center (pCore 2 H))
        IsExtraspecial.frattini_eq_center_two, MonoidHom.comap_ker]
    exact pCore_frattini_action_kernel 2 hc
  apply isConj_noncentral_involutions_of_five_cosets (pCore 2 H) hpoints ?_ x y hx hxZ hy hyZ
  rwa [← index_ker,hker]

/-- A returning noncentral core involution fuses the entire core to its
central involution in the ambient group. The embedding and returning
conjugacy are literal. -/
theorem pCore_involution_isConj_of_returning
    {G : Type*} [Group G] (f : H →* G) (hf : Function.Injective f)
    (he : Nonempty (pCore 2 H ≃* Model))
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfive : 5 ∣ (pCore 2 H).index)
    (z : pCore 2 H) (hz : orderOf z = 2) (hzZ : z ∈ center (pCore 2 H))
    (ht : ∃ t : pCore 2 H, IsConj (f z) (f t) ∧ t ≠ z)
    (u : pCore 2 H) (hu : orderOf u = 2) : IsConj (f z) (f u) := by
  let : IsExtraspecial 2 (pCore 2 H) := IsExtraspecial.of_mulEquiv he.some.symm inferInstance
  have hcent (x : pCore 2 H) (hx : orderOf x = 2) (hxZ : x ∈ center (pCore 2 H)) : x = z := by
    let : IsCyclic (center (pCore 2 H)) := isCyclic_of_prime_card (IsExtraspecial.center_order_p 2 _)
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨x,hxZ⟩ : center (pCore 2 H))) (y := ⟨z,hzZ⟩)
      ((orderOf_coe _).symm.trans hx) ((orderOf_coe _).symm.trans hz))
  by_cases huZ : u ∈ center (pCore 2 H)
  · rw [hcent u hu huZ]
  obtain ⟨t,hzt,htz⟩ := ht
  have hto : orderOf t = 2 := by
    rw [← orderOf_coe,← orderOf_injective f hf]
    obtain ⟨a,ha⟩ := isConj_iff.mp hzt
    exact (congrArg orderOf ha).symm.trans (((MulAut.conj a).orderOf_eq _).trans
      ((orderOf_injective f hf _).trans ((orderOf_coe z).trans hz)))
  have htZ : t ∉ center (pCore 2 H) := fun hh => htz (hcent t hto hh)
  exact hzt.trans (f.map_isConj (pCore_noncentral_involutions_isConj he hc hfive t u hto htZ hu huZ))
end MinusExtraspecial
