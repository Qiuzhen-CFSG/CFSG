module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.ReducedFF
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.ModuleCriterion
public import Theory.Representation.ElementaryAbelianAction.Commutator

/-!
# From MS3 to an offender on the actual abelian core

Let D = [O₂(J),L] be abelian with a natural two-copy quotient D/C_D(L).
The centralizer C_J(D) lies in O₂(J): its intersection with L is O₂(L),
and its quotient conjugation image centralizes every inner automorphism.
Consequently the maximum elementary subgroup supplied by MS3 acts nontrivially
on D. The faithful conjugation action of J/C_J(D) on D is therefore an FF-module.

The intrinsic O₂(L) centralizes D, so the actual L-action descends to SL₃(2).
Its image in J/C_J(D) is normal. The given projection is a module cover, since
its kernel is fixed and [D,L] = D. Applying the explicitly assumed pure module
criterion now gives |C_D(L)| = 1.

This constructs the group-theoretic side of the argument without identifying D
with Ω₁Z(O₂(J)) or assuming that O₂(J) is abelian. The unqualified two-copy
rigidity theorem is still contingent on proving `DoubleCopy.CoverRigidity`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31(MS3),
C.1.34(2),(5), printed pp.135–137; the maximum-elementary counting argument
is B.2.4, pp.75–76, and covers are discussed in I.1.5–6, p.408.
-/

public section
open Representation Representation.OneCohomology Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- The whole centralizer of D lies in the ambient two-core. Faithfulness
of the given natural quotient determines its intersection with L; the quotient
conjugation action then kills the entire centralizer. -/
theorem Input.abelianCore_centralizer_le_twoCore_of_twoCopies (h : Input κ L R)
    (q : AbelianCore.NaturalQuotient h 2) :
    centralizer (commutatorCore L : Set J) ≤ pCore 2 J := by
  let := h.component_normal
  let C := centralizer (commutatorCore L : Set J)
  have hCL : C ⊓ L ≤ pCore 2 J := by
    intro x hx
    let l : L := ⟨x, hx.2⟩
    let g := q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)
    have hg : specialLinearNatural (k := ZMod 2) 3 g = specialLinearNatural 3 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨d, hd⟩ := q.surjective (Multiplicative.ofAdd (fun _ => v))
      have hfix : h.coreConjugate l d = d := by
        apply Subtype.ext
        rw [h.coreConjugate_val]
        rw [← hx.1 d d.property, mul_inv_cancel_right]
      have he := q.equivariant l d 0
      rw [hfix, hd] at he
      change v = specialLinearNatural 3 g v at he
      rw [map_one]
      exact he.symm
    have hg1 : g = 1 := Matrix.SpecialLinearGroup.toLin'_injective
      (LinearEquiv.toLinearMap_injective hg)
    have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
      (q.quotientEquiv.map_eq_one_iff.mp hg1)
    exact (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hl)).1
  have hk : ⁅C, L⁆ ≤ h.quotientAction.ker := by
    rw [h.quotientAction_kernel]
    exact (commutator_le_inf C L).trans hCL
  have hi : L.map h.quotientAction = MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    apply le_antisymm
    · rintro a ⟨l, hl, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩,
        (h.quotientAction_component ⟨l, hl⟩).symm⟩
    · rintro a ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
      exact ⟨l, l.property, h.quotientAction_component l⟩
  have hcomm : ⁅C.map h.quotientAction, MulAut.innerSubgroup (L ⧸ pCore 2 L)⁆ = ⊥ := by
    rw [← hi, ← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr hk
  have hzero : C.map h.quotientAction = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (MulAut.centralizer_innerSubgroup_eq_bot h.quotient_center).le
  have hle := (Subgroup.map_eq_bot_iff C).mp hzero
  rwa [h.quotientAction_kernel] at hle

/-- Conditional assembly through the independent module criterion. Every
group-theoretic premise of that criterion, including its faithful FF-action on
the actual D, is proved here. The criterion itself remains a proof obligation. -/
theorem Input.abelianCore_fixedKernel_eq_one_of_twoCopies_of_coverRigidity
    (h : Input κ L R) (hc : IsMulCommutative (commutatorCore L))
    (q : AbelianCore.NaturalQuotient h 2)
    (hrig : AbelianCore.DoubleCopy.CoverRigidity.{u, u}) :
    Nat.card (coreFixed L) = 1 := by
  let := h.component_normal
  let := h.abelianCore_elementary_of_naturalQuotient hc q
  let D := commutatorCore L
  let C := centralizer (D : Set J)
  let π := QuotientGroup.mk' C
  have hπ : π.ker = C := QuotientGroup.ker_mk' _
  let δ := NormalElementaryQuotient.representation D π (QuotientGroup.mk'_surjective C) hπ
  have hfactor : pCore 2 L ≤ (π.comp L.subtype).ker := by
    intro n hn
    change π (n : J) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    intro d hd
    exact (h.abelianCore_componentCore_centralizes_of_naturalQuotient hc q hd
      n (mem_map_of_mem L.subtype hn)).symm
  let ι : AbelianCore.DoubleCopy.MatrixGroup →* (J ⧸ C) :=
    (QuotientGroup.lift (pCore 2 L) (π.comp L.subtype) hfactor).comp
      q.quotientEquiv.symm.toMonoidHom
  have hι (l : L) : ι (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) = π l := by
    simp only [ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rfl
  have hιrange : ι.range = L.map π := by
    apply le_antisymm
    · rintro x ⟨g, rfl⟩
      obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
      have he : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
        rw [hl, MulEquiv.apply_symm_apply]
      rw [← he, hι]
      exact mem_map_of_mem π l.property
    · rintro x ⟨l, hl, rfl⟩
      exact ⟨q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩), hι ⟨l,hl⟩⟩
  have hnormal : ι.range.Normal := by
    rw [hιrange]
    exact (inferInstance : L.Normal).map π (QuotientGroup.mk'_surjective C)
  let σ : Representation (ZMod 2) AbelianCore.DoubleCopy.MatrixGroup (Additive D) := δ.comp ι
  have hσ (l : L) (d : Additive D) :
      σ (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) d =
        Additive.ofMul (h.coreConjugate l d.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((δ (ι (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))) d).toMul : J) = _
    rw [hι]
    change ((δ (π l) d).toMul : J) = (h.coreConjugate l d.toMul : J)
    rw [h.coreConjugate_val]
    exact NormalElementaryQuotient.representation_apply D π _ hπ l d
  let f := q.projection.toAdditiveLeft.toZModLinearMap 2
  let p : σ.IntertwiningMap AbelianCore.DoubleCopy.natural :=
    { toLinearMap := f
      isIntertwining' g := by
        apply LinearMap.ext
        intro d
        funext i
        obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
        have he : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
          rw [hl, MulEquiv.apply_symm_apply]
        change f (σ g d) i = specialLinearNatural 3 g (f d i)
        rw [← he, hσ]
        exact q.equivariant l d.toMul i }
  have hpker (d : Additive D) : p d = 0 ↔ d.toMul ∈ coreFixed L := by
    rw [← q.kernel]
    change (q.projection d.toMul).toAdd = 0 ↔ q.projection d.toMul = 1
    exact Multiplicative.toAdd.injective.eq_iff
  have hp : IsCover p := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      obtain ⟨d, hd⟩ := q.surjective (Multiplicative.ofAdd v)
      exact ⟨Additive.ofMul d, congrArg Multiplicative.toAdd hd⟩
    · intro d hd g
      obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (q.quotientEquiv.symm g)
      have he : q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
        rw [hl, MulEquiv.apply_symm_apply]
      change σ g d = d
      rw [← he, hσ]
      apply Additive.toMul.injective
      apply Subtype.ext
      change (h.coreConjugate l d.toMul : J) = (d.toMul : J)
      have hcomm : (l : J) * (d.toMul : J) = (d.toMul : J) * (l : J) :=
        (hpker d).mp hd l l.property
      rw [h.coreConjugate_val, hcomm, mul_inv_cancel_right]
    · let K : Subgroup D := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'
      have hDK : D ≤ K.map D.subtype := by
        change commutatorCore L ≤ _
        conv_lhs => rw [← h.commutatorCore_idempotent, commutator_comm]
        apply commutator_le.mpr
        intro l hl d hd
        let d' : Additive D := Additive.ofMul ⟨d,hd⟩
        let g := q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
        refine ⟨(σ g d' - d').toMul, Coinvariants.sub_mem_ker g d', ?_⟩
        change ((σ g d').toMul : J) / d = ⁅l,d⁆
        rw [hσ]
        change (h.coreConjugate ⟨l,hl⟩ ⟨d,hd⟩ : J) / d = ⁅l,d⁆
        rw [h.coreConjugate_val, div_eq_mul_inv]
        rfl
      apply top_unique
      intro d _
      obtain ⟨w, hw, he⟩ := hDK d.toMul.property
      have heq : w = d.toMul := Subtype.ext he
      change d.toMul ∈ K
      exact heq ▸ hw
  have hFF : BinaryOffender.IsFFModule δ := by
    apply NormalElementaryQuotient.isFFModule_of_thompson_not_le D π
      (QuotientGroup.mk'_surjective C) hπ R
    · exact (commutator_le_left _ _).trans h.radical.twoCore_le
    · intro hle
      apply h.thompson_not_le_core
      rw [hπ] at hle
      exact hle.trans (h.abelianCore_centralizer_le_twoCore_of_twoCopies q)
  have hz := hrig δ ι (NormalElementaryQuotient.representation_injective D π _ hπ)
    hnormal p hp hFF
  let e : coreFixed L ≃ p.toLinearMap.ker :=
    { toFun d := ⟨Additive.ofMul d.val, (hpker _).mpr d.property⟩
      invFun d := ⟨d.val.toMul, (hpker _).mp d.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, hz]
  exact Nat.card_unique

end CFSG.Quasithin.ChapterC.BinaryMS
