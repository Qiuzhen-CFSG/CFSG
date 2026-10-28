module

public import Theory.Representation.BinaryOffender.CubicConjugateDimension
public import Theory.Representation.CentralizerField
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.InvolutionAutomorphismGeneration

/-!
# Conjugate generation in an actual binary central-cover actor

Let a normal perfect subgroup L act faithfully and irreducibly in
characteristic two. An inner-conjugate generation bound for its specified
central quotient lifts to the given ambient group. The conjugators lift
from the simple carrier to L. Schur's lemma excludes a nonidentity
involution in the action kernel; that kernel embeds in the cyclic linear
centralizer of L. Perfectness then recovers L by taking commutators.

The kernel need not be central in the ambient group, and no hypothesis on
the full linear normalizer is used. The commutator argument is the same as
in `ThreeConjugateNormalizer.CentralCover`, here with arbitrary finite
length and the original ambient group throughout.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, (2.5)--(2.6)
and Proposition 5.1; Aschbacher--Smith K.4, printed p.457.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative

/-- Perfect containment lifts when an abelian kernel centralizes the smaller group. -/
private theorem lift_abelian_kernel {G D : Type*} [Group G] [Group D]
    (f : G →* D) (H J : Subgroup G) [Group.IsPerfect H]
    [IsMulCommutative f.ker]
    (hc : f.ker ≤ centralizer (H : Set G))
    (h : H.map f ≤ J.map f) : H ≤ J := by
  rw [← commutator_eq_self (H := H)]
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha, hfa⟩ := h (mem_map_of_mem f hx)
  obtain ⟨b, hb, hfb⟩ := h (mem_map_of_mem f hy)
  let k := a * x⁻¹
  let l := b * y⁻¹
  have hk : k ∈ f.ker := by simp only [k, MonoidHom.mem_ker, map_mul, map_inv, hfa, mul_inv_cancel]
  have hl : l ∈ f.ker := by simp only [l, MonoidHom.mem_ker, map_mul, map_inv, hfb, mul_inv_cancel]
  have hkx : Commute k x := (mem_centralizer_iff.mp (hc hk) x hx).symm
  have hky : Commute k y := (mem_centralizer_iff.mp (hc hk) y hy).symm
  have hlx : Commute l x := (mem_centralizer_iff.mp (hc hl) x hx).symm
  have hly : Commute l y := (mem_centralizer_iff.mp (hc hl) y hy).symm
  have hkl : Commute k l := congrArg Subtype.val (mul_comm (⟨k, hk⟩ : f.ker) ⟨l, hl⟩)
  have hkly := hkl.mul_right hky
  have hkcomm : Commute k ⁅x,l*y⁆ := by
    rw [commutatorElement_def]
    exact ((hkx.mul_right hkly).mul_right hkx.inv_right).mul_right hkly.inv_right
  have hlcomm : Commute l ⁅x,y⁆ := by
    rw [commutatorElement_def]
    exact ((hlx.mul_right hly).mul_right hlx.inv_right).mul_right hly.inv_right
  have he : ⁅k*x,l*y⁆ = ⁅x,y⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hkly.commutator_eq,
      mul_one, hkcomm.eq, mul_inv_cancel_right,
      commutatorElement_mul_right_eq_mul_conj, hlx.symm.commutator_eq,
      one_mul, hlcomm.eq, mul_inv_cancel_right]
  have hea : k*x = a := by simp [k]
  have heb : l*y = b := by simp [l]
  rw [hea, heb] at he
  rw [← he, commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

namespace Representation.BinaryOffender
open Theory.GroupTheory

variable {G V S : Type*} [Group G] [Group S]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Inner conjugators on the actual central quotient lift to the given actor,
including arbitrary central covers and permitted outer actions. -/
theorem involutionConjugateGenerationBound_of_centralCover
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [Group.IsPerfect L] (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp L.subtype))
    (e : L ⧸ center L ≃* S) {n : ℕ}
    (hgen : InvolutionInnerConjugateGenerationBound S n) :
    InvolutionConjugateGenerationBound L n := by
  let := hi
  let σ := ρ.comp L.subtype
  let q := MulAut.centralQuotientAction e
  have hq : Function.Injective q := MulAut.centralQuotientAction_injective e
  let f : G →* MulAut S := q.comp (MulAut.conjNormal (H := L))
  have hker (g : G) : g ∈ f.ker ↔ g ∈ centralizer (L : Set G) := by
    change q (MulAut.conjNormal g) = 1 ↔ _
    rw [← map_one q, hq.eq_iff]
    change g ∈ (MulAut.conjNormal (H := L)).ker ↔ _
    rw [MulAut.conjNormal_ker_eq_centralizer]
  let C := CentralizerField.linearCentralizer σ
  let : IsCyclic (IntertwiningMap σ σ)ˣ := CentralizerField.units_isCyclic σ
  let : IsCyclic C := isCyclic_of_injective (CentralizerField.centralizerUnitsEquiv σ).toMonoidHom
    (CentralizerField.centralizerUnitsEquiv σ).injective
  let j : f.ker →* C := (ρ.asGroupHom.comp f.ker.subtype).codRestrict C (by
    intro g
    apply mem_centralizer_iff.mpr
    rintro _ ⟨l, rfl⟩
    change ρ.asGroupHom (l : G) * ρ.asGroupHom (g : G) =
      ρ.asGroupHom (g : G) * ρ.asGroupHom (l : G)
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.asGroupHom ((hker g).mp g.property l l.property))
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply hf
    exact congrArg (fun c : C => c.val.val) h
  let : IsCyclic f.ker := isCyclic_of_injective j hj
  have hc : f.ker ≤ centralizer (L : Set G) := fun g hg => (hker g).mp hg
  have hinc (l : L) : f (l : G) = MulAut.conj (e (QuotientGroup.mk' (center L) l)) := by
    change q (MulAut.conjNormal (l : G)) = _
    rw [MulAut.conjNormal_val]
    exact MulAut.centralQuotientAction_conj e l
  intro t ht ht2
  have hft : f t ≠ 1 := by
    intro he
    exact ht (BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L hf ht2
      ((hker t).mp he))
  obtain ⟨c, hcgen⟩ := hgen (f t) hft (by rw [← map_pow, ht2, map_one])
  have hsurj : Function.Surjective (fun l : L => e (QuotientGroup.mk' (center L) l)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center L))
  choose d hd using fun i => hsurj (c i)
  refine ⟨fun i => (d i : G), ?_⟩
  let J := closure (Set.range fun i => (d i : G) * t * (d i : G)⁻¹)
  apply lift_abelian_kernel f L J hc
  have hJ : J.map f = closure
      (Set.range fun i => MulAut.conj (c i) * f t * (MulAut.conj (c i))⁻¹) := by
    change (Subgroup.closure _).map f = _
    rw [MonoidHom.map_closure]
    congr 1
    ext a
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and,
      map_mul, map_inv, hinc, hd]
  rw [hJ]
  apply le_trans _ hcgen
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨e (QuotientGroup.mk' (center L) ⟨l, hl⟩), (hinc ⟨l, hl⟩).symm⟩

end Representation.BinaryOffender
