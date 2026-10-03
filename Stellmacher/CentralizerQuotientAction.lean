module

public import Stellmacher.MaxElementaryOffender

/-!
# Faithful action of a centralizer quotient

Let `V` be a normal subgroup of `H`, and let `q : H → X` be a surjective
homomorphism whose kernel is `C_H(V)`.  This module equips `V` with the induced
faithful action of `X`.  The defining lift factors conjugation through `q`;
the public computation theorem records that a lift `q g` acts as conjugation
by `g`, without exposing the construction itself.

The remaining results transport fixed points and action commutators back to
subgroups of `H`.  In the finite elementary-abelian setting, the fixed-point
cardinality identity combines with the maximal-elementary subgroup bound to
show that images of maximal elementary abelian subgroups are Section One
offenders.

This is the source-neutral quotient-action interface used in Stellmacher
(2.2) and in the selected-factor step of (3.9), from journal pages 20 and 24
of `refs/files/stellmacher-n-group.pdf` (transcribed in
`refs/latex/stellmacher-n-group.tex`).
-/

namespace Stellmacher

universe u

/-- The action induced on a normal subgroup by quotienting its ambient group
by its exact centralizer. -/
public noncomputable abbrev centralizerQuotientAction
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H)) :
    MulDistribMulAction X V := by
  classical
  letI : V.Normal := hVnormal
  let act : H →* MulAut V := MulAut.conjNormal
  have hact : q.ker ≤ act.ker := by
    intro g hg
    rw [hker] at hg
    rw [Subgroup.mem_centralizer_iff] at hg
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g * (x : H) * g⁻¹ = x
    rw [← hg x x.property, mul_inv_cancel_right]
  exact MulDistribMulAction.compHom V
    (q.liftOfSurjective hq ⟨act, hact⟩)

/-- An element represented by `g : H` acts on `V` by conjugation by `g`. -/
public theorem centralizerQuotientAction_smul_coe
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (g : H) (x : V) :
    letI := centralizerQuotientAction V hVnormal q hq hker
    ((q g • x : V) : H) = g * (x : H) * g⁻¹ := by
  let : V.Normal := hVnormal
  change (((q.liftOfSurjective hq _ : X →* MulAut V) (q g)) x : H) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- The action induced by the exact centralizer quotient is faithful. -/
public theorem centralizerQuotientAction_faithful
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H)) :
    letI := centralizerQuotientAction V hVnormal q hq hker
    fixingSubgroup X (Set.univ : Set V) = ⊥ := by
  let := centralizerQuotientAction V hVnormal q hq hker
  apply bot_unique
  intro b hb
  obtain ⟨g, rfl⟩ := hq b
  have hg : g ∈ q.ker := by
    rw [hker]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [mem_fixingSubgroup_iff] at hb
    have hfix := hb ⟨x, hx⟩ (Set.mem_univ _)
    have heq := congrArg Subtype.val hfix
    rw [centralizerQuotientAction_smul_coe
      V hVnormal q hq hker] at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  exact hg

/-- Fixed points of the image of `A` map exactly onto `V ∩ C_H(A)`. -/
public theorem centralizerQuotientAction_fixedPoints_image_map
    {H : Type u} [Group H]
    (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (A : Subgroup H) :
    letI := centralizerQuotientAction V hVnormal q hq hker
    (FixedPoints.subgroup (A.map q) V).map V.subtype =
      V ⊓ Subgroup.centralizer (A : Set H) := by
  let := centralizerQuotientAction V hVnormal q hq hker
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    change (y : H) ∈ Subgroup.centralizer (A : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfix := (FixedPoints.mem_subgroup (M := A.map q) (a := y)).mp hy
      ⟨q a, Subgroup.mem_map_of_mem q ha⟩
    change q a • y = y at hfix
    have heq := congrArg Subtype.val hfix
    rw [centralizerQuotientAction_smul_coe
      V hVnormal q hq hker] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · rintro ⟨hxV, hxA⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    change (⟨x, hxV⟩ : V) ∈ FixedPoints.subgroup (A.map q) V
    rw [FixedPoints.mem_subgroup]
    intro a
    obtain ⟨a₀, ha₀, heq⟩ := a.property
    apply Subtype.ext
    change ((a.val • (⟨x, hxV⟩ : V) : V) : H) = x
    rw [← heq, centralizerQuotientAction_smul_coe
      V hVnormal q hq hker]
    change x ∈ Subgroup.centralizer (A : Set H) at hxA
    rw [Subgroup.mem_centralizer_iff] at hxA
    rw [hxA a₀ ha₀, mul_inv_cancel_right]

/-- Cardinality form of the fixed-point image identity. -/
public theorem centralizerQuotientAction_fixedPoints_card
    {H : Type u} [Group H]
    (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (A : Subgroup H) :
    letI := centralizerQuotientAction V hVnormal q hq hker
    Nat.card (FixedPoints.subgroup (A.map q) V) =
      Nat.card (V ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) := by
  let := centralizerQuotientAction V hVnormal q hq hker
  rw [← centralizerQuotientAction_fixedPoints_image_map
      V hVnormal q hq hker A,
    Subgroup.card_map_of_injective V.subtype_injective]

/-- A maximal elementary abelian subgroup maps to a Section One offender for
the faithful centralizer-quotient action. -/
public theorem centralizerQuotientAction_maxElementary_map_mem_oneA
    {H : Type u} [Group H] [Finite H]
    (T V A : Subgroup H) (hVnormal : V.Normal) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hA : A ∈ elementaryAbelianMaxSubgroups T)
    {X : Type u} [Group X] [Finite X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H)) :
    letI := centralizerQuotientAction V hVnormal q hq hker
    SectionOne.oneA (V := V) (T.map q) (A.map q) := by
  let := centralizerQuotientAction V hVnormal q hq hker
  have hbound := maxElementary_card_le_fixed_mul_image T V A hVT hA q hker
  rw [← centralizerQuotientAction_fixedPoints_card
    V hVnormal q hq hker A] at hbound
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map q, ?_⟩
  unfold SectionOne.m
  have hpos : 0 < (Nat.card (FixedPoints.subgroup (A.map q) V) : ℚ) *
      (Nat.card (A.map q) : ℚ) := by
    exact_mod_cast Nat.mul_pos Nat.card_pos Nat.card_pos
  apply (div_le_one hpos).mpr
  exact_mod_cast hbound

/-- The image in `H` of the action commutator of `q(A)` on `W` is the
ambient subgroup commutator of the image of `W` with `A`. -/
public theorem centralizerQuotientAction_commutatorSubgroup_image_map
    {H : Type u} [Group H]
    (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (A : Subgroup H) (W : Subgroup V) :
    letI := centralizerQuotientAction V hVnormal q hq hker
    (commutatorSubgroup (A.map q) V W).map V.subtype =
      ⁅W.map V.subtype, A⁆ := by
  let := centralizerQuotientAction V hVnormal q hq hker
  rw [commutatorSubgroup, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨a, w, hw, rfl⟩, rfl⟩
    obtain ⟨a₀, ha₀, heq⟩ := a.property
    refine ⟨(w : H)⁻¹,
      Subgroup.mem_map_of_mem V.subtype (W.inv_mem hw),
      a₀, ha₀, ?_⟩
    rw [commutatorElement_def]
    change (w : H)⁻¹ * a₀ * (w : H)⁻¹⁻¹ * a₀⁻¹ =
      ((w⁻¹ * (a.val • w) : V) : H)
    rw [← heq]
    have hcoe : ((w⁻¹ * (q a₀ • w) : V) : H) =
        (w : H)⁻¹ * ((q a₀ • w : V) : H) := rfl
    rw [hcoe, centralizerQuotientAction_smul_coe
      V hVnormal q hq hker]
    group
  · rintro ⟨_, ⟨w₀, hw₀, rfl⟩, a, ha, rfl⟩
    let abar : A.map q := ⟨q a, Subgroup.mem_map_of_mem q ha⟩
    refine ⟨(w₀⁻¹)⁻¹ * (abar • w₀⁻¹),
      ⟨abar, w₀⁻¹, W.inv_mem hw₀, rfl⟩, ?_⟩
    rw [commutatorElement_def]
    change (w₀ : H)⁻¹⁻¹ * ((q a • w₀⁻¹ : V) : H) =
      (w₀ : H) * a * (w₀ : H)⁻¹ * a⁻¹
    rw [centralizerQuotientAction_smul_coe
      V hVnormal q hq hker]
    have hi : ((w₀⁻¹ : V) : H) = (w₀ : H)⁻¹ := rfl
    rw [hi]
    group

end Stellmacher
