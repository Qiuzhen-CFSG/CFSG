module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction
public import Theory.GroupTheory.RelativeQuotientMaps
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Noncentral binary sections in two-perfect actors

If a normal binary section of a two-perfect group is noncentral, every chief
refinement of that interval has a noncentral binary factor. The interval may
have arbitrary endpoints. The binary condition passes to its subintervals by
an injective quotient map followed by a surjective quotient map.

The key step makes centrality transitive: if B/A and C/B are central and B/A
is a p-group, then for c in C the commutator map x ↦ [x,c]A takes values in
the central p-subgroup BA/A of H/A. It is a homomorphism, so p-perfectness
of H makes it trivial. Induction along the series proves the assertion.
Finiteness is needed only to specialize to the actual p-residual.

The final application discharges the refinement premise of the existing
residual chief-count comparison. Survival on restricting the actor remains
a separate premise. Source application: Aschbacher–Smith 14.7.70, printed
p.1074 (PDF p.1091), the comparison with the chief factors of the left residual.
-/

public section
open Subgroup
open scoped commutatorElement

namespace NoncentralChiefRefinement
variable {H : Type*} [Group H]

/-- A subinterval of a p-group section is a p-group, through the literal
inclusion and denominator-enlargement maps of relative quotients. -/
theorem section_isPGroup_subinterval {p : ℕ} {A B C D : NormalNode H}
    (hp : IsPGroup p (Section A B)) (hAC : A ≤ C) (hDB : D ≤ B) :
    IsPGroup p (Section C D) := by
  have hAD : IsPGroup p (Section A D) :=
    hp.of_injective (QuotientGroup.quotientMapSubgroupOfOfLe (le_refl A.val) hDB)
      (QuotientGroup.quotientMapSubgroupOfOfLe_injective D.val B.val A.val hDB)
  exact hAD.of_surjective (QuotientGroup.quotientMapSubgroupOfOfLe hAC (le_refl D.val))
    (QuotientGroup.quotientMapSubgroupOfOfLe_surjective D.val A.val C.val hAC)

/-- Two successive central sections combine to a central section when the
lower section is a p-group and the ambient actor is p-perfect. -/
theorem IsCentral.trans_of_isPPerfect {p : ℕ} [Fact p.Prime]
    {A B C : NormalNode H} (hH : IsPPerfect p H)
    (hp : IsPGroup p (Section A B)) (hAB : IsCentral A B) (hBC : IsCentral B C) :
    IsCentral A C := by
  let q := QuotientGroup.mk' A.val
  let P := B.val.map q
  have hk : (q.subgroupMap B.val).ker = A.val.subgroupOf B.val := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  let e : Section A B ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap B.val)
        (q.subgroupMap_surjective B.val))
  have hpP : IsPGroup p P := hp.of_equiv e
  rw [isCentral_iff_commutator_le, commutator_le] at hBC ⊢
  intro x _ c hc
  have hm (y : H) : ⁅y, c⁆ ∈ B.val := hBC y (mem_top _) c hc
  let f : H →* P := {
    toFun y := ⟨q ⁅y, c⁆, mem_map_of_mem q (hm y)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' y z := by
      apply Subtype.ext
      change q ⁅y * z, c⁆ = q ⁅y, c⁆ * q ⁅z, c⁆
      have hyz := mem_center_iff.mp (hAB (mem_map_of_mem q (hm z))) (q y)
      have hzy := mem_center_iff.mp (hAB (mem_map_of_mem q (hm y))) (q ⁅z, c⁆)
      rw [commutatorElement_mul_left_eq_conj_mul, map_mul, map_mul, map_mul,
        map_inv, hyz, mul_inv_cancel_right]
      exact hzy }
  have hf := hH.hom_eq_one_of_isPGroup hpP f
  have hx := congrArg (fun g : H →* P => (g x : H ⧸ A.val)) hf
  exact (QuotientGroup.eq_one_iff _).mp hx

/-- A p-group interval with central steps is central in a p-perfect actor.
No assumption that the endpoints are bottom and top is used. -/
theorem ChiefSeries.isCentral_of_isPPerfect_of_central_steps
    {p : ℕ} [Fact p.Prime] (s : ChiefSeries H) (hH : IsPPerfect p H)
    (hp : IsPGroup p (Section s.head s.last))
    (hc : ∀ i : Fin s.length, IsCentral (s i.castSucc) (s i.succ)) :
    IsCentral s.head s.last := by
  have hall : ∀ i : Fin (s.length + 1), IsCentral s.head (s i) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [isCentral_iff_commutator_le]
      exact commutator_le_right _ _
    | succ i ih =>
      exact IsCentral.trans_of_isPPerfect hH
        (section_isPGroup_subinterval hp le_rfl (CompositionSeries.le_last i.castSucc))
        ih (hc i)
  exact hall (Fin.last s.length)

/-- Every chief refinement of a noncentral binary normal interval in a
two-perfect actor contains a noncentral binary chief factor. -/
theorem ChiefSeries.exists_noncentralTwo_of_isPPerfect
    (s : ChiefSeries H) (hH : IsPPerfect 2 H)
    (h : IsNoncentralTwo s.head s.last) :
    ∃ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) := by
  classical
  by_contra hn
  apply h.2
  apply s.isCentral_of_isPPerfect_of_central_steps hH h.1
  intro i
  by_contra hc
  apply hn
  exact ⟨i, section_isPGroup_subinterval h.1
    (CompositionSeries.head_le i.castSucc) (CompositionSeries.le_last i.succ), hc⟩

/-- The exact local refinement premise for the intrinsic two-residual.
Its two-perfectness follows from finiteness, rather than being an extra input. -/
theorem ChiefSeries.exists_noncentralTwo_pResidual [Finite H]
    (s : ChiefSeries (pResidual 2 H)) (h : IsNoncentralTwo s.head s.last) :
    ∃ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) :=
  s.exists_noncentralTwo_of_isPPerfect (Subgroup.isPPerfect_pResidual 2) h

/-- Apply the residual specialization to the literal restriction/counting
assembly, discharging its `hrefine` premise. Only survival of each original
section under restriction to the residual remains to be supplied. -/
theorem ChiefSeries.exists_comparison_pResidual_of_section_survival [Finite H]
    (s : ChiefSeries H) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hsection : ∀ i : Fin s.length,
      IsNoncentralTwo (s i.castSucc) (s i.succ) →
        IsNoncentralTwo (restrictNormalNode (pResidual 2 H) (s i.castSucc))
          (restrictNormalNode (pResidual 2 H) (s i.succ))) :
    ∃ (t : ChiefSeries (pResidual 2 H))
      (ι : Fin (s.length + 1) →o Fin (t.length + 1)),
      (∀ i, t (ι i) = restrictNormalNode (pResidual 2 H) (s i)) ∧
      ι 0 = 0 ∧ ι (Fin.last s.length) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ ∧ s.noncentralTwoCount ≤ t.noncentralTwoCount := by
  exact s.exists_comparison_of_restriction_survival (pResidual 2 H) h0 h1 hsection
    (fun t => t.exists_noncentralTwo_pResidual)

end NoncentralChiefRefinement
