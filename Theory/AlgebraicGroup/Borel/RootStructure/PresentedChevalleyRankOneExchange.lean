module

public import Theory.AlgebraicGroup.Borel.RootStructure.GeneralChevalleyRelatorAPI

/-!
# Rank-one exchange in a presented Chevalley group

This module proves the elementary rank-one step used when extending a
Chevalley--Bruhat normal form by a simple-root factor.  In the quotient by the
general Chevalley relators, a zero-parameter root element is absorbed by the
chosen reflection representative.  For a nonzero parameter `t`, the product
`x_alpha(t) n_alpha(1)` is exchanged for an opposite-root factor, one torus
factor, and one positive-root factor.  The torus parameter is
the inverse of `s = reflectionSign alpha alpha * t`, as is the parameter of the
final positive-root factor, so the convention-dependent sign is retained
explicitly.

The proof is internal to the presentation.  It expands `n` and `h`, cancels
root elements with the root-addition relation, moves root elements with the
torus and reflection conjugation relations, and uses the reflection-square and
torus-multiplication relations.  `IsRootSystemRealization` supplies only the
rank-one identities that self-reflection negates a root and that the opposite
root has Cartan pairing `-2`.  No collection theorem, Bruhat uniqueness,
evaluation injectivity, or presentation-kernel result is used.
-/

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma presented_relation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    {data : ChevalleyRelationData D P e base}
    {weights : base.support → TorusWeight T}
    {lhs rhs : FreeGroup (FormalChevalleyGenerator D.Root k)}
    (h : formalRelation lhs rhs ∈ generalChevalleyRelators data weights) :
    (PresentedGroup.mk (generalChevalleyRelators data weights) lhs :
      PresentedGroup (generalChevalleyRelators data weights)) =
      PresentedGroup.mk (generalChevalleyRelators data weights) rhs := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (by simpa [formalRelation_eq] using h)

private lemma p_root_addition
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) (t s : k) :
    (PresentedGroup.of (.x α t) :
      PresentedGroup (generalChevalleyRelators data weights)) *
      PresentedGroup.of (.x α s) = PresentedGroup.of (.x α (t + s)) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyX_eq] using
      (IsCommonChevalleyRelator.rootAddition (data := data) α t s)

private lemma p_root_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) :
    (PresentedGroup.of (.x α 0) :
      PresentedGroup (generalChevalleyRelators data weights)) = 1 := by
  have h := p_root_addition (data := data) (weights := weights) α 0 0
  have hcancel :
      (PresentedGroup.of (.x α 0) :
          PresentedGroup (generalChevalleyRelators data weights)) *
          PresentedGroup.of (.x α 0) =
        PresentedGroup.of (.x α 0) * 1 := by
    simpa using h
  exact mul_left_cancel hcancel

private lemma p_n_definition
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) (t : kˣ) :
    (PresentedGroup.of (.n α t) :
      PresentedGroup (generalChevalleyRelators data weights)) =
      PresentedGroup.of (.x α (t : k)) *
        PresentedGroup.of (.x (D.neg α) (-((t : k)⁻¹))) *
        PresentedGroup.of (.x α (t : k)) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyN_eq, formalChevalleyX_eq] using
      (IsCommonChevalleyRelator.nDefinition (data := data) α t)

private lemma p_h_definition
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) (t : kˣ) :
    (PresentedGroup.of (.h α t) :
      PresentedGroup (generalChevalleyRelators data weights)) =
      (PresentedGroup.of (.n α 1) :
        PresentedGroup (generalChevalleyRelators data weights))⁻¹ *
        PresentedGroup.of (.n α t) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyH_eq, formalChevalleyN_eq] using
      (IsCommonChevalleyRelator.hDefinition (data := data) α t)

private lemma p_h_multiplication
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) (s t : kˣ) :
    (PresentedGroup.of (.h α s) :
      PresentedGroup (generalChevalleyRelators data weights)) *
      PresentedGroup.of (.h α t) = PresentedGroup.of (.h α (s * t)) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyH_eq] using
      (IsCommonChevalleyRelator.torusMultiplication (data := data) α s t)

private lemma p_torus_conjugation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α β : D.Root) (t : k) (s : kˣ) :
    (PresentedGroup.of (.h β s) :
        PresentedGroup (generalChevalleyRelators data weights))⁻¹ *
      PresentedGroup.of (.x α t) * PresentedGroup.of (.h β s) =
      PresentedGroup.of (.x α ((s : k) ^ D.pairing α β * t)) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyH_eq, formalChevalleyX_eq] using
      (IsCommonChevalleyRelator.torusConjugatesRoot (data := data) α β t s)

private lemma p_reflection_conjugation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α β : D.Root) (t : k) :
    (PresentedGroup.of (.n β 1) :
        PresentedGroup (generalChevalleyRelators data weights))⁻¹ *
      PresentedGroup.of (.x α t) * PresentedGroup.of (.n β 1) =
      PresentedGroup.of (.x (D.reflect β α)
        ((data.reflectionSign α β : k) * t)) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyN_eq, formalChevalleyX_eq] using
      (IsCommonChevalleyRelator.reflectionConjugatesRoot (data := data) α β t)

private lemma p_reflection_square
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (α : D.Root) :
    (PresentedGroup.of (.n α 1) :
        PresentedGroup (generalChevalleyRelators data weights)) *
      PresentedGroup.of (.n α 1) = PresentedGroup.of (.h α (-1)) := by
  apply presented_relation (data := data) (weights := weights)
  rw [mem_generalChevalleyRelators (e := e) (base := base)]
  exact Or.inl <| by
    rw [mem_universalChevalleyRelators]
    simpa only [formalChevalleyN_eq, formalChevalleyH_eq] using
      (IsCommonChevalleyRelator.reflectionSquare (data := data) α)

/-- Multiplying a chosen rank-one reflection representative on the left by its
root element either absorbs a zero parameter or exchanges a nonzero parameter
for opposite-root, torus, and positive-root factors.  The statement holds for
every realized root, and hence in particular for every simple root. -/
public theorem presentedChevalley_rankOneExchange
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type u} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {e : D.Root ≃ ι} {base : P.Base}
    (data : ChevalleyRelationData D P e base)
    (weights : base.support → TorusWeight T)
    (hActual : IsRootSystemRealization D P e base)
    (α : D.Root) :
    (∀ t : k, t = 0 →
      (PresentedGroup.of (.x α t) :
        PresentedGroup (generalChevalleyRelators data weights)) *
        PresentedGroup.of (.n α 1) = PresentedGroup.of (.n α 1)) ∧
    (∀ (t : k) (ht : t ≠ 0),
      let ε := data.reflectionSign α α
      let s : kˣ := Units.mk0 ((ε : k) * t)
        (mul_ne_zero (Units.ne_zero ε) ht)
      (PresentedGroup.of (.x α t) :
          PresentedGroup (generalChevalleyRelators data weights)) *
          PresentedGroup.of (.n α 1) =
        PresentedGroup.of (.x (D.neg α) (t⁻¹)) *
          PresentedGroup.of (.h α s⁻¹) *
          PresentedGroup.of (.x α (s : k)⁻¹)) := by
  have hself : D.reflect α α = D.neg α := by
    apply e.injective
    rw [hActual.2.1 α α, hActual.2.2.1 α]
  have hpair : D.pairing (D.neg α) α = -2 := by
    have h := hActual.1 (D.neg α) α
    rw [hActual.2.2.1 α, P.pairing_reflectionPerm_self_left,
      P.pairing_same] at h
    exact_mod_cast h
  constructor
  · intro t ht
    subst t
    rw [p_root_zero (data := data) (weights := weights), one_mul]
  · intro t ht
    let ε : kˣ := data.reflectionSign α α
    let s : kˣ := Units.mk0 ((ε : k) * t)
      (mul_ne_zero (Units.ne_zero ε) ht)
    have hconj :
        (PresentedGroup.of (.n α 1) :
            PresentedGroup (generalChevalleyRelators data weights))⁻¹ *
          PresentedGroup.of (.x α t) * PresentedGroup.of (.n α 1) =
        PresentedGroup.of (.x (D.neg α) ((ε : k) * t)) := by
      rw [p_reflection_conjugation (data := data) (weights := weights) α α t, hself]
    have hcross :
        (PresentedGroup.of (.x α t) :
            PresentedGroup (generalChevalleyRelators data weights)) *
          PresentedGroup.of (.n α 1) =
        PresentedGroup.of (.n α 1) *
          PresentedGroup.of (.x (D.neg α) ((ε : k) * t)) := by
      rw [← hconj]
      group
    let q : kˣ := Units.mk0 (-((s : k)⁻¹))
      (neg_ne_zero.mpr (inv_ne_zero (Units.ne_zero s)))
    have hq : (q : k) = -((s : k)⁻¹) := rfl
    have hcancel₁ :
        (PresentedGroup.of (.x α (-((s : k)⁻¹))) :
            PresentedGroup (generalChevalleyRelators data weights)) =
          (PresentedGroup.of (.x α ((s : k)⁻¹)))⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [p_root_addition (data := data) (weights := weights)]
      simpa using p_root_zero (data := data) (weights := weights) α
    have hcancel₂ :
        (PresentedGroup.of (.x (D.neg α) (-((-((s : k)⁻¹))⁻¹))) :
            PresentedGroup (generalChevalleyRelators data weights)) =
          PresentedGroup.of (.x (D.neg α) (s : k)) := by
      congr 2
      simp
    have hsolve :
        (PresentedGroup.of (.x (D.neg α) (s : k)) :
            PresentedGroup (generalChevalleyRelators data weights)) =
          PresentedGroup.of (.x α (s : k)⁻¹) *
            PresentedGroup.of (.n α 1) *
            PresentedGroup.of (.h α q) *
            PresentedGroup.of (.x α (s : k)⁻¹) := by
      have hnq := p_n_definition (data := data) (weights := weights) α q
      have hhq := p_h_definition (data := data) (weights := weights) α q
      rw [hq] at hnq
      rw [hhq]
      group
      rw [hnq]
      rw [hcancel₂]
      rw [hcancel₁]
      group
    have hmove :
        (PresentedGroup.of (.n α 1) :
            PresentedGroup (generalChevalleyRelators data weights)) *
          PresentedGroup.of (.x α ((s : k)⁻¹)) =
        PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
          PresentedGroup.of (.n α 1) := by
      have hc := p_reflection_conjugation (data := data) (weights := weights)
        α α ((s : k)⁻¹)
      rw [hself] at hc
      have hsquare := p_reflection_square (data := data) (weights := weights) α
      have htorus := p_torus_conjugation (data := data) (weights := weights)
        (D.neg α) α ((ε : k) * (s : k)⁻¹) (-1 : kˣ)
      rw [hpair] at htorus
      norm_num at htorus
      have hcomm :
          (PresentedGroup.of (.h α (-1)) :
              PresentedGroup (generalChevalleyRelators data weights)) *
            PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) =
          PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
            PresentedGroup.of (.h α (-1)) := by
        calc
          _ = PresentedGroup.of (.h α (-1)) *
              ((PresentedGroup.of (.h α (-1)) :
                  PresentedGroup (generalChevalleyRelators data weights))⁻¹ *
                PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
                PresentedGroup.of (.h α (-1))) := by rw [htorus]
          _ = _ := by group
      calc
        _ = (PresentedGroup.of (.n α 1) * PresentedGroup.of (.n α 1)) *
              PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              (PresentedGroup.of (.n α 1))⁻¹ := by rw [← hc]; group
        _ = PresentedGroup.of (.h α (-1)) *
              PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              (PresentedGroup.of (.n α 1))⁻¹ := by rw [hsquare]
        _ = PresentedGroup.of (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              PresentedGroup.of (.h α (-1)) *
              (PresentedGroup.of (.n α 1))⁻¹ := by rw [hcomm]
        _ = _ := by rw [← hsquare]; group
    have hcross' :
        (PresentedGroup.of (.n α 1) :
            PresentedGroup (generalChevalleyRelators data weights)) *
          PresentedGroup.of (.x (D.neg α) ((ε : k) * t)) =
        PresentedGroup.of (.x (D.neg α) (t⁻¹)) *
          PresentedGroup.of (.h α s⁻¹) *
          PresentedGroup.of (.x α ((ε : k) * t)⁻¹) := by
      -- This is the rank-one triangular exchange after the `n` and `h` laws.
      rw [show (ε : k) * t = (s : k) by rfl]
      rw [hsolve]
      have hunit : (-1 : kˣ) * q = s⁻¹ := by
        apply Units.ext
        simp [q]
      have hlower : (ε : k) * (s : k)⁻¹ = t⁻¹ := by
        change (ε : k) * (((ε : k) * t)⁻¹) = t⁻¹
        field_simp
      calc
        _ = ((PresentedGroup.of (.n α 1) :
                PresentedGroup (generalChevalleyRelators data weights)) *
              PresentedGroup.of (.x α ((s : k)⁻¹))) *
            PresentedGroup.of (.n α 1) * PresentedGroup.of (.h α q) *
            PresentedGroup.of (.x α ((s : k)⁻¹)) := by group
        _ = (PresentedGroup.of
                (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              PresentedGroup.of (.n α 1)) *
            PresentedGroup.of (.n α 1) * PresentedGroup.of (.h α q) *
            PresentedGroup.of (.x α ((s : k)⁻¹)) := by rw [hmove]
        _ = PresentedGroup.of
                (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              (PresentedGroup.of (.n α 1) * PresentedGroup.of (.n α 1)) *
              PresentedGroup.of (.h α q) *
              PresentedGroup.of (.x α ((s : k)⁻¹)) := by group
        _ = PresentedGroup.of
                (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              PresentedGroup.of (.h α (-1)) * PresentedGroup.of (.h α q) *
              PresentedGroup.of (.x α ((s : k)⁻¹)) := by
                rw [p_reflection_square (data := data) (weights := weights) α]
        _ = PresentedGroup.of
                (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              (PresentedGroup.of (.h α (-1)) * PresentedGroup.of (.h α q)) *
              PresentedGroup.of (.x α ((s : k)⁻¹)) := by group
        _ = PresentedGroup.of
                (.x (D.neg α) ((ε : k) * (s : k)⁻¹)) *
              PresentedGroup.of (.h α ((-1 : kˣ) * q)) *
              PresentedGroup.of (.x α ((s : k)⁻¹)) := by
                rw [p_h_multiplication (data := data) (weights := weights)]
        _ = _ := by rw [hunit, hlower]
    exact hcross.trans hcross'

end Theory.AlgebraicGroup
