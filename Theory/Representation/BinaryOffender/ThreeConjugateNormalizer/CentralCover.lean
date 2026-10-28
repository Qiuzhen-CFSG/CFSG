module

public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer
public import Theory.Representation.CentralizerField
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.ThreeConjugateAutomorphisms

/-!
# Three-conjugate generation through binary central covers

For a faithful irreducible binary action of a finite quasisimple group, the
three-conjugate automorphism condition on its specified central quotient lifts
to generation containing the actual image in its full linear normalizer.

Conjugation descends faithfully through the perfect central quotient. Schur's
lemma excludes centralizing involutions, and the two inner conjugators lift
through the quotient map. The remaining kernel is contained in the cyclic
linear centralizer. Although it need not be central in the whole normalizer,
it is abelian and centralizes the perfect image; commutators therefore lift
the required subgroup containment.

This discharges the central-cover transfer in the three-conjugate route to
Aschbacher–Smith B.1.13, printed pp.73–74. The concrete simple-group generation
condition remains an explicit input, as in `ThreeConjugateAutomorphisms`.
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
variable {G V S : Type*} [Group G] [Group S] [AddCommGroup V] [Module (ZMod 2) V]
    [IsQuasisimple G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- Three-conjugate generation on the actual simple quotient lifts to the full
linear normalizer of every faithful irreducible binary central-cover action. -/
theorem normalizerThreeConjugates_of_centralCover
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (e : G ⧸ center G ≃* S) (hgen : ThreeConjugateAutomorphisms S) :
    NormalizerThreeConjugates ρ := by
  let := hi
  have hk : ρ.ker ≤ center G := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf]
    exact bot_le
  let A := actionImage ρ
  let N := linearNormalizer ρ
  let I := A.subgroupOf N
  let : Group.IsPerfect A := Group.IsPerfect.range ρ.asGroupHom
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe A.le_normalizer).symm.toMonoidHom)
    (subgroupOfEquivOfLe A.le_normalizer).symm.surjective
  let eA : A ⧸ center A ≃* S := (simpleQuotientEquivImage ρ hk).symm.trans e
  let q := MulAut.centralQuotientAction eA
  have hq : Function.Injective q := MulAut.centralQuotientAction_injective eA
  let f : N →* MulAut S := q.comp A.normalizerMonoidHom
  have hker (n : N) : n ∈ f.ker ↔ n.val ∈ CentralizerField.linearCentralizer ρ := by
    change q (A.normalizerMonoidHom n) = 1 ↔ _
    rw [← map_one q, hq.eq_iff]
    change n ∈ A.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  let C := CentralizerField.linearCentralizer ρ
  let : IsCyclic (IntertwiningMap ρ ρ)ˣ := CentralizerField.units_isCyclic ρ
  let : IsCyclic C := isCyclic_of_injective (CentralizerField.centralizerUnitsEquiv ρ).toMonoidHom
    (CentralizerField.centralizerUnitsEquiv ρ).injective
  let j : f.ker →* C :=
    ((N.subtype.comp f.ker.subtype).codRestrict C (fun n => (hker n).mp n.property))
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => c.val) h
  let : IsCyclic f.ker := isCyclic_of_injective j hj
  have hc : f.ker ≤ centralizer (I : Set N) := by
    intro n hn
    apply mem_centralizer_iff.mpr
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp ((hker n).mp hn) a.val ha)
  let inc : A →* N := inclusion A.le_normalizer
  have hinc (a : A) : f (inc a) = MulAut.conj (eA (QuotientGroup.mk' (center A) a)) := by
    have he : A.normalizerMonoidHom (inc a) = MulAut.conj a := by
      ext b
      rfl
    change q (A.normalizerMonoidHom (inc a)) = _
    rw [he]
    exact MulAut.centralQuotientAction_conj eA a
  intro t ht ht2
  have hft : f t ≠ 1 := by
    intro he
    apply ht
    apply Subtype.ext
    let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
    let : Representation.IsIrreducible (τ.comp A.subtype) := imageRepresentation_isIrreducible ρ hi
    apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one τ A
      (fun _ _ h => Units.ext h)
    · exact congrArg Subtype.val ht2
    · exact (hker t).mp he
  obtain ⟨g, h, hgh⟩ := hgen (f t) hft (by rw [← map_pow, ht2, map_one])
  obtain ⟨ag, hag⟩ := ((eA.surjective).comp (QuotientGroup.mk'_surjective (center A))) g
  obtain ⟨ah, hah⟩ := ((eA.surjective).comp (QuotientGroup.mk'_surjective (center A))) h
  change eA (QuotientGroup.mk' (center A) ag) = g at hag
  change eA (QuotientGroup.mk' (center A) ah) = h at hah
  refine ⟨inc ag, inc ah, ?_⟩
  let J := zpowers t ⊔ zpowers (inc ag * t * (inc ag)⁻¹) ⊔
    zpowers (inc ah * t * (inc ah)⁻¹)
  apply lift_abelian_kernel f I J hc
  have hJ : J.map f = zpowers (f t) ⊔
      zpowers (MulAut.conj g * f t * (MulAut.conj g)⁻¹) ⊔
      zpowers (MulAut.conj h * f t * (MulAut.conj h)⁻¹) := by
    simp only [J, Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv, hinc, hag, hah]
  rw [hJ]
  apply le_trans _ hgh
  rintro _ ⟨a, ha, rfl⟩
  let a' : A := ⟨a.val, ha⟩
  have he : inc a' = a := rfl
  rw [← he, hinc]
  exact ⟨_, rfl⟩

end Representation.BinaryOffender
