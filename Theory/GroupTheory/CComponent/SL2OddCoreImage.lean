module

public import Theory.GroupTheory.CComponent.SimpleImageKernel
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.SpecificGroups.SL2.OddCoreAndRank

/-!
# Simple images of C-components with an odd-by-SL₂ quotient

A nonquasisimple intrinsic C-component has trivial ordinary layer, so its
Fitting subgroup is killed by every simple quotient. A finite quasisimple
group with trivial two-core cannot surject onto odd-characteristic SL₂:
the kernel is central, and prime cores map onto prime cores across a central
surjection, whereas SL₂ contains the central involution minus identity.

The resulting obstruction retains the actual odd-core quotient and the full
special-linear center. Source application: Aschbacher--Smith 11.1.2(1) and
11.5.8, printed p.784.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.GroupTheory

/-- C-component minimality kills the layer in the nonquasisimple case. -/
theorem fitting_killed_of_nonquasisimple_component
    {Q J : Type*} [Group Q] [Finite Q] [Group J] [IsSimpleGroup J]
    (hQ : (⊤ : Subgroup Q).IsCComponent) (hnq : ¬ IsQuasisimple Q)
    (f : Q →* J) (hf : Function.Surjective f) : generalizedFitting Q ≤ f.ker := by
  have hE : componentLayer Q = ⊥ := by
    apply sSup_eq_bot.mpr
    intro C hC
    have htop := hC.isCComponent.eq_of_le hQ le_top
    let : IsQuasisimple (⊤ : Subgroup Q) := htop ▸ hC.2
    exact (hnq (IsQuasisimple.of_mulEquiv topEquiv)).elim
  rw [generalizedFitting, hE, sup_bot_eq,
    kernel_eq_solvableRadical_of_top_isCComponent hQ f hf]
  exact le_solvableRadical _ inferInstance inferInstance

private theorem twoCore_SL2_ne_bot {F : Type*} [Field F] [Finite F] (hF : (2 : F) ≠ 0) :
    pCore 2 SL(2,F) ≠ ⊥ := by
  let Z := zpowers (-1 : SL(2,F))
  have hZc : Z ≤ center SL(2,F) := by
    apply zpowers_le.mpr
    exact mem_center_iff.mpr fun x => by simp
  have hZn : Z.Normal := ⟨fun x hx g => by
    have hc := mem_center_iff.mp (hZc hx) g
    rw [hc]
    simpa [mul_assoc] using hx⟩
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF, pow_one])
  have hle : Z ≤ pCore 2 SL(2,F) := le_sSup ⟨hZn, hZp⟩
  intro hb
  have he : (-1 : SL(2,F)) = 1 := mem_bot.mp (hb ▸ hle (mem_zpowers _))
  have ho := Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF
  rw [he, orderOf_one] at ho
  norm_num at ho

private theorem not_quasisimple_of_twoCore_trivial_SL2_quotient
    {Q F : Type*} [Group Q] [Finite Q] [Field F] [Finite F]
    (hcore : pCore 2 Q = ⊥) (hF : (2 : F) ≠ 0)
    (f : Q →* SL(2,F)) (hf : Function.Surjective f) : ¬ IsQuasisimple Q := by
  intro hQ
  let := hQ
  have hk : f.ker ≤ center Q := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    obtain ⟨x, hx⟩ := hf (-1)
    have hfone : f = 1 := MonoidHom.ker_eq_top_iff.mp ht
    have hfx : f x = 1 := by rw [hfone]; rfl
    have he : (-1 : SL(2,F)) = 1 := hx.symm.trans hfx
    have ho := Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hF
    rw [he, orderOf_one] at ho
    norm_num at ho
  have hm := f.map_pCore_of_central_kernel (p := 2) hf hk
  rw [hcore, Subgroup.map_bot] at hm
  exact twoCore_SL2_ne_bot hF hm.symm

/-- No simple image detects F* in the odd-by-SL₂ branch with trivial two-core. -/
theorem generalizedFitting_le_ker_of_odd_SL2_quotient
    {Q F J : Type*} [Group Q] [Finite Q] [Field F] [Finite F]
    [Group J] [IsSimpleGroup J]
    (hQ : (⊤ : Subgroup Q).IsCComponent) (hcore : pCore 2 Q = ⊥)
    (hF : (2 : F) ≠ 0) (e : (Q ⧸ pPrimeCore 2 Q) ≃* SL(2,F))
    (f : Q →* J) (hf : Function.Surjective f) : generalizedFitting Q ≤ f.ker := by
  apply fitting_killed_of_nonquasisimple_component hQ _ f hf
  exact not_quasisimple_of_twoCore_trivial_SL2_quotient hcore hF
    (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

end Theory.GroupTheory
