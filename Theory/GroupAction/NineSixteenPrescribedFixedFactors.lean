module
public import Theory.GroupAction.Invariant
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup

/-!
# Prescribed complementary fixed factors on binary sixteen

Suppose an elementary abelian three-group acts on an elementary abelian
group X of order sixteen with trivial whole-group fixed subgroup. For any
prescribed complementary actor subgroups K,L of order three, if both fixed
subgroups are nontrivial, then each has order four and they complement one
another in X. Faithfulness of the supplied action is not assumed.

Because K and L generate the actor group, their fixed subgroups intersect
trivially. Each opposite actor line acts on the other's fixed subgroup,
with no nonidentity fixed point. Orbit counting modulo three makes each
nontrivial fixed subgroup have at least four elements. Their disjoint
product lies in the sixteen-element group, so both lower bounds are equalities
and their join is X. All restricted actions come from the given action.

This is the second use of the same chosen actor lines in Stellmacher
(10.1), printed p.64, on the residual quotient U/V in the order-nine branch.
-/

open scoped IsMulCommutative

public theorem nine_sixteen_prescribed_fixed_factors
    {A X:Type*} [Group A] [Finite A] [Group X] [Finite X]
    [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 X]
    [MulDistribMulAction A X]
    (hX:Nat.card X=16) (K L:Subgroup A)
    (hK:Nat.card K=3) (hL:Nat.card L=3) (hcompl:IsCompl K L)
    (hfixed:FixedPoints.subgroup (⊤:Subgroup A) X=⊥)
    (hKne:FixedPoints.subgroup K X≠⊥) (hLne:FixedPoints.subgroup L X≠⊥) :
    Nat.card (FixedPoints.subgroup K X)=4 ∧
      Nat.card (FixedPoints.subgroup L X)=4 ∧
      IsCompl (FixedPoints.subgroup K X) (FixedPoints.subgroup L X) := by
  have hinf : FixedPoints.subgroup K X⊓FixedPoints.subgroup L X=⊥ := by
    apply bot_unique
    intro x hx
    have hKst : K≤MulAction.stabilizer A x:=fun a ha=>hx.1 ⟨a,ha⟩
    have hLst : L≤MulAction.stabilizer A x:=fun a ha=>hx.2 ⟨a,ha⟩
    have htop : (⊤:Subgroup A)≤MulAction.stabilizer A x:=
      hcompl.sup_eq_top ▸ sup_le hKst hLst
    exact hfixed.le (show x∈FixedPoints.subgroup (⊤:Subgroup A) X from fun a=>htop a.property)
  have hlower (Y Z:Subgroup A) (hZ:Nat.card Z=3)
      (hYZ:FixedPoints.subgroup Y X⊓FixedPoints.subgroup Z X=⊥)
      (hY:FixedPoints.subgroup Y X≠⊥) : 4≤Nat.card (FixedPoints.subgroup Y X) := by
    let C:=FixedPoints.subgroup Y X
    have hstable (z:Z) (x:X) (hx:x∈C) : z • x∈C := by
      intro y
      change (y:A) • ((z:A) • x)=(z:A) • x
      rw [←mul_smul,mul_comm (y:A),mul_smul]
      exact congrArg (fun v:X=>(z:A) • v) (hx y)
    let _ : IsInvariant Z X C:=⟨fun z x=>⟨hstable z x,fun h=>by
      have hh:=hstable z⁻¹ (z • x) h
      simpa only [inv_smul_smul] using hh⟩⟩
    have hfix : FixedPoints.subgroup Z C=⊥ := by
      apply bot_unique
      intro c hc
      change c=1
      apply Subtype.ext
      have hcz : (c:X)∈FixedPoints.subgroup Z X:=fun z=>congrArg (fun v:C=>(v:X)) (hc z)
      have hh : (c:X)∈FixedPoints.subgroup Y X⊓FixedPoints.subgroup Z X:=⟨c.property,hcz⟩
      exact hYZ.le hh
    have hthree : IsPGroup 3 Z:=IsPGroup.of_card (n:=1) (by simpa using hZ)
    have hmod:=hthree.card_modEq_card_fixedPoints C
    change Nat.ModEq 3 (Nat.card C) (Nat.card (FixedPoints.subgroup Z C)) at hmod
    rw [hfix,Subgroup.card_bot] at hmod
    have hneone : Nat.card C≠1:=fun h=>hY (Subgroup.card_eq_one.mp h)
    have hpos : 0<Nat.card C:=Nat.card_pos
    rw [Nat.ModEq] at hmod
    change 4≤Nat.card C
    omega
  have hKlow:=hlower K L hL hinf hKne
  have hLlow:=hlower L K hK (by rwa [inf_comm]) hLne
  have hprod:=Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (FixedPoints.subgroup K X) (FixedPoints.subgroup L X)
      (by rw [Subgroup.normalizer_eq_top];exact le_top)
  rw [hinf,Subgroup.card_bot,one_mul] at hprod
  have hbound : Nat.card (FixedPoints.subgroup K X⊔FixedPoints.subgroup L X:Subgroup X)≤16:=by
    have hh:=Subgroup.card_le_of_le (show FixedPoints.subgroup K X⊔FixedPoints.subgroup L X≤⊤ from le_top)
    simpa only [Subgroup.card_top,hX] using hh
  have hKcard : Nat.card (FixedPoints.subgroup K X)=4:=by nlinarith
  have hLcard : Nat.card (FixedPoints.subgroup L X)=4:=by nlinarith
  have htop : FixedPoints.subgroup K X⊔FixedPoints.subgroup L X=⊤:=
    Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top,hX,←hprod,hKcard,hLcard])
  exact ⟨hKcard,hLcard,IsCompl.of_eq hinf htop⟩
