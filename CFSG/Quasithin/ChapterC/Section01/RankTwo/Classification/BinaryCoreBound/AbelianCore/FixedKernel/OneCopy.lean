module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.Reduction
public import Theory.Representation.ElementaryAbelianAction.Commutator
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Fixed kernels over one binary natural module

Let D = [O₂(J),L] be abelian and suppose its quotient by the literal fixed
subgroup C_D(L) is the natural SL₃(2) module. The exponent reduction makes D
an elementary abelian group, and the descended action turns the given
projection into a module cover: it is surjective, its kernel is fixed, and
[D,L] = D supplies commutator generation.

Every such cover is a quotient of the universal cover. Its fixed kernel has
dimension at most dim H¹(SL₃(2), V*). The inverse-transpose automorphism and
dot-product identification transport the proved natural H¹ calculation to
V*, so this dimension is at most one and |C_D(L)| ≤ 2.

This is only the one-copy branch. It does not exclude nontrivial fixed
extensions of two natural copies; that requires the local MS3 argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(1),(5),
printed pp.136–137, and the universal-cover discussion I.1.5–6, printed p.408.
-/

public section

open Representation Representation.OneCohomology Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS

private theorem dual_natural_h1 :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) 3).dual) = 1 := by
  let e := BinaryLinearThree.AutomorphismAction.graphNaturalDual
  let a := BinaryLinearThree.AutomorphismAction.graph
  have he : ∀ g v, e.symm (BinaryLinearThree.W.dual g v) =
      BinaryLinearThree.W (a g) (e.symm v) := by
    intro g v
    change e.symm (BinaryLinearThree.W.dual g v) =
      (BinaryLinearThree.W.comp a.toMonoidHom) g (e.symm v)
    exact LinearMap.congr_fun (e.symm.isIntertwining' g) v
  exact (H1Congr _ _ a e.symm.toLinearEquiv he).finrank_eq.trans
    SLHigherNatural.finrank_H1_sl3_two

private theorem cover_kernel_bound {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) W}
    (p : σ.IntertwiningMap (specialLinearNatural (k := ZMod 2) 3))
    (hp : IsCover p) : Nat.card p.toLinearMap.ker ≤ 2 := by
  let ρ := specialLinearNatural (k := ZMod 2) 3
  obtain ⟨t, ht, htp⟩ := exists_universalCover_quotient p hp
  let s : (universalCoverProjection ρ).toLinearMap.ker →ₗ[ZMod 2] p.toLinearMap.ker :=
    (t.toLinearMap.comp (universalCoverProjection ρ).toLinearMap.ker.subtype).codRestrict
      p.toLinearMap.ker (by
        intro u
        change p (t u.val) = 0
        rw [htp]
        exact u.property)
  have hs : Function.Surjective s := by
    intro w
    obtain ⟨u, hu⟩ := ht w.val
    have hu0 : u ∈ (universalCoverProjection ρ).toLinearMap.ker := by
      change universalCoverProjection ρ u = 0
      rw [← htp, hu]
      exact w.property
    exact ⟨⟨u, hu0⟩, Subtype.ext hu⟩
  have hdim : Module.finrank (ZMod 2) p.toLinearMap.ker ≤ 1 := by
    have hd := LinearMap.finrank_le_finrank_of_surjective hs
    rw [finrank_ker_universalCoverProjection, dual_natural_h1] at hd
    exact hd
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq (by norm_num)

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- A natural one-copy quotient of the actual abelian commutator core has a
fixed kernel of order at most two. No bound on that kernel is an input. -/
theorem Input.abelianCore_fixedKernel_le_two_of_oneCopy (h : Input κ L R)
    (hc : IsMulCommutative (commutatorCore L))
    (q : AbelianCore.NaturalQuotient h 1) : Nat.card (coreFixed L) ≤ 2 := by
  let := h.abelianCore_elementary_of_naturalQuotient hc q
  let : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (commutatorCore L) := MulDistribMulAction.compHom (commutatorCore L) (q.action h hc)
  let σ := ofElementaryAbelianAction (A := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (G := commutatorCore L) (p := 2)
  let f : Additive (commutatorCore L) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    (LinearMap.proj (0 : Fin 1)).comp (q.projection.toAdditiveLeft.toZModLinearMap 2)
  let p : σ.IntertwiningMap (specialLinearNatural (k := ZMod 2) 3) :=
    { toLinearMap := f
      isIntertwining' g := by
        ext d : 1
        exact q.action_equivariant h hc g d.toMul 0 }
  have hpker (d : Additive (commutatorCore L)) :
      p d = 0 ↔ d.toMul ∈ coreFixed L := by
    rw [← q.kernel]
    change (q.projection d.toMul).toAdd 0 = 0 ↔ q.projection d.toMul = 1
    constructor
    · intro hd
      apply Multiplicative.toAdd.injective
      funext i
      change (q.projection d.toMul).toAdd i = 0
      simpa only [Subsingleton.elim i 0] using hd
    · intro hd
      rw [hd]
      rfl
  have hp : IsCover p := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      obtain ⟨d, hd⟩ := q.surjective (Multiplicative.ofAdd (fun _ => v))
      exact ⟨Additive.ofMul d, congrArg (fun x => x.toAdd 0) hd⟩
    · intro d hd g
      obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
      have he : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
        rw [hl, MulEquiv.apply_symm_apply]
      change Additive.ofMul (q.action h hc g d.toMul) = d
      apply Additive.toMul.injective
      rw [← he, q.action_component]
      apply Subtype.ext
      change (h.coreConjugate l d.toMul : J) = (d.toMul : J)
      rw [h.coreConjugate_val]
      have hdC := (hpker d).mp hd
      have hec : (l : J) * (d.toMul : J) = (d.toMul : J) * (l : J) :=
        hdC l l.property
      rw [hec, mul_inv_cancel_right]
    · let C : Subgroup (commutatorCore L) := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'
      have hDC : commutatorCore L ≤ C.map (commutatorCore L).subtype := by
        conv_lhs => rw [← h.commutatorCore_idempotent, commutator_comm]
        apply commutator_le.mpr
        intro l hl d hd
        let d' : Additive (commutatorCore L) := Additive.ofMul ⟨d,hd⟩
        let g := q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
        refine ⟨(σ g d' - d').toMul, Coinvariants.sub_mem_ker g d', ?_⟩
        change ((q.action h hc g ⟨d,hd⟩ : commutatorCore L) : J) / d = ⁅l,d⁆
        rw [q.action_component, h.coreConjugate_val, div_eq_mul_inv]
        rfl
      apply top_unique
      intro d _
      obtain ⟨w, hw, he⟩ := hDC d.toMul.property
      have heq : w = d.toMul := Subtype.ext he
      have : d.toMul ∈ C := heq ▸ hw
      exact this
  let e : coreFixed L ≃ p.toLinearMap.ker :=
    { toFun d := ⟨Additive.ofMul d.val, (hpker _).mpr d.property⟩
      invFun d := ⟨d.val.toMul, (hpker _).mp d.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e]
  exact cover_kernel_bound p hp

end CFSG.Quasithin.ChapterC.BinaryMS
