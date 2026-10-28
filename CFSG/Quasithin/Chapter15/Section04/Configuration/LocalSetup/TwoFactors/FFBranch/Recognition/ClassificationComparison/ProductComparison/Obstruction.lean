module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Prepared
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SymmetricThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SylowBound
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.FFLinearPrimeCore

/-!
# The ambient component obstruction in the three product FF branches

The actual internal factors of B.5.6(3) and (5) are nonabelian and subnormal
in the ambient actor. A quasisimple generalized Fitting subgroup would lie
in both factors, by the component dichotomy and self-centralization, which
contradicts their commutation. In (4), normality of A₆ follows from the actual
product and the specified outer action. The separate C₃ factor then contradicts
self-centralization. No splitting of the outer extension or of the module is used.

These are branch obstructions, not an assertion of the F.6.18 model structure.
They apply to the literal normal offender subgroup without identifying it with
the ambient group. Natural, double-natural, indecomposable and hyperplane actions
all retain their original source records.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3)–(5), pp.105–110, and the comparison in 15.4.18, p.1163.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison
open FFAlternatives
/-- The three full source branches being compared, retaining all actual factors,
representations, hyperplane data and nonsplit extensions. -/
@[expose] def Branch {A : Type*} [Group A]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) : Prop :=
  Nonempty (SourceTwoFactorCase σ) ∨ Nonempty (OuterSixThreeCase σ) ∨
    Nonempty (HyperplaneCase σ)

variable {D : Type*} [Group D]

private theorem commutative_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) [IsMulCommutative B] : IsMulCommutative A :=
  ⟨⟨fun a b => hf (by simp only [map_mul, mul_comm'])⟩⟩

private theorem linearTwo_not_commutative (F : BinaryField) :
    ¬ IsMulCommutative SL(2,F.Carrier) := by
  intro hc
  let := hc
  let a : SL(2,F.Carrier) := ⟨!![1,1;0,1], by simp [Matrix.det_fin_two]⟩
  let b : SL(2,F.Carrier) := ⟨!![1,0;1,1], by simp [Matrix.det_fin_two]⟩
  have he := congrArg (fun g : SL(2,F.Carrier) => g.val 0 0) (mul_comm' a b)
  change (a.val * b.val) 0 0 = (b.val * a.val) 0 0 at he
  norm_num [a, b, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero] at he

/-- Each actual factor in B.5.6(3) is nonabelian, including SL₂(2). -/
theorem factor_not_commutative (h : FactorModel D) : ¬ IsMulCommutative D := by
  intro hc
  let := hc
  cases h with
  | linearTwo F e =>
    exact linearTwo_not_commutative F (commutative_of_injective e.symm.toMonoidHom e.symm.injective)
  | symmetricFive e =>
    let := commutative_of_injective e.symm.toMonoidHom e.symm.injective
    have hn : (Equiv.swap (0 : Fin 5) 1) * Equiv.swap 1 2 ≠
        Equiv.swap 1 2 * Equiv.swap 0 1 := by decide
    exact hn (mul_comm' _ _)
  | linearThree F _ e =>
    let := Atlas.sl_perfect (F := F.Carrier) 3 (by decide)
    let : Nontrivial SL(3,F.Carrier) :=
      (QuotientGroup.mk'_surjective (center SL(3,F.Carrier))).nontrivial
    exact Group.IsPerfect.not_isMulCommutative SL(3,F.Carrier)
      (commutative_of_injective e.symm.toMonoidHom e.symm.injective)

private theorem product_first_normal {A B : Subgroup D} (c : InternalProduct A B) : A.Normal := by
  constructor
  intro x hx g
  obtain ⟨⟨a,b⟩, rfl⟩ := c.equiv.surjective g
  let a' : A := a * ⟨x,hx⟩ * a⁻¹
  have he : c.equiv (a',1) = c.equiv (a,b) * x * (c.equiv (a,b))⁻¹ := by
    rw [show x = c.equiv (⟨x,hx⟩,1) by simp [c.apply_eq], ← map_inv, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [a']
  have hm : c.equiv (a',1) ∈ A := by simp [c.apply_eq]
  exact he ▸ hm

private def product_symm {A B : Subgroup D} (c : InternalProduct A B) : InternalProduct B A where
  equiv := (MulEquiv.prodComm : B × A ≃* A × B).trans c.equiv
  apply_eq b a := by
    have he : c.equiv (a,1) * c.equiv (1,b) = c.equiv (1,b) * c.equiv (a,1) := by
      rw [← map_mul, ← map_mul]
      simp
    change c.equiv (a,b) = _
    rw [c.apply_eq]
    simpa [c.apply_eq] using he

private theorem product_commute {A B : Subgroup D} (c : InternalProduct A B) :
    ⁅A,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  have he : c.equiv (⟨a,ha⟩,1) * c.equiv (1,⟨b,hb⟩) =
      c.equiv (1,⟨b,hb⟩) * c.equiv (⟨a,ha⟩,1) := by
    rw [← map_mul, ← map_mul]
    simp
  simpa [c.apply_eq] using he.symm

private theorem nonabelian_subnormal_contains_fitting [Finite D]
    (hL : IsQuasisimple (generalizedFitting D)) (A : Subgroup D)
    (hA : A.IsSubnormal) (hna : ¬ IsMulCommutative A) : generalizedFitting D ≤ A := by
  let L := generalizedFitting D
  have hcomp : IsComponent D L := ⟨(inferInstance : L.Normal).isSubnormal, hL⟩
  rcases hcomp.subnormal_dichotomy A hA with h | h
  · exact h
  · have ha : A ≤ centralizer (L : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using h)
    have hal : A ≤ L := ha.trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    apply (hna ?_).elim
    exact ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.mp (ha a.property) b (hal b.property)).symm⟩⟩

/-- Two commuting nonabelian subnormal subgroups rule out a quasisimple F*.
The subnormality is with respect to the actual ambient group. -/
theorem not_quasisimple_of_commuting_subnormal [Finite D] (A B : Subgroup D)
    (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hna : ¬ IsMulCommutative A) (hnb : ¬ IsMulCommutative B) (hc : ⁅A,B⁆ = ⊥) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  intro hL
  let := hL
  let : IsSimpleGroup (generalizedFitting D ⧸ center (generalizedFitting D)) := hL.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  have ha := nonabelian_subnormal_contains_fitting hL A hA hna
  have hb := nonabelian_subnormal_contains_fitting hL B hB hnb
  have hh : ⁅generalizedFitting D, generalizedFitting D⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono ha hb).trans hc.le)
  rw [commutator_eq_self] at hh
  exact (nontrivial_iff_ne_bot _).mp inferInstance hh

/-- A normal actual internal product of two FF factors is incompatible
with a quasisimple ambient generalized Fitting subgroup. -/
theorem product_not_quasisimple [Finite D] (N : Subgroup D) [N.Normal]
    {A B : Subgroup N} (c : InternalProduct A B)
    (ha : FactorModel A) (hb : FactorModel B) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  let := product_first_normal c
  let := product_first_normal (product_symm c)
  apply not_quasisimple_of_commuting_subnormal (A.map N.subtype) (B.map N.subtype)
    ((inferInstance : A.Normal).isSubnormal.trans' (inferInstance : N.Normal).isSubnormal)
    ((inferInstance : B.Normal).isSubnormal.trans' (inferInstance : N.Normal).isSubnormal)
  · intro h
    let := h
    exact factor_not_commutative ha (commutative_of_injective
      (equivMapOfInjective A N.subtype N.subtype_injective).toMonoidHom
      (equivMapOfInjective A N.subtype N.subtype_injective).injective)
  · intro h
    let := h
    exact factor_not_commutative hb (commutative_of_injective
      (equivMapOfInjective B N.subtype N.subtype_injective).toMonoidHom
      (equivMapOfInjective B N.subtype N.subtype_injective).injective)
  · rw [← map_commutator, product_commute c, Subgroup.map_bot]

private theorem pair_commute {A B : Subgroup D} (f : (A × B) →* D)
    (hf : ∀ a b, f (a,b) = (a : D) * (b : D)) : ⁅A,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  have he : f (⟨a,ha⟩,1) * f (1,⟨b,hb⟩) = f (1,⟨b,hb⟩) * f (⟨a,ha⟩,1) := by
    rw [← map_mul, ← map_mul]
    simp
  simpa [hf] using he.symm

private theorem pair_disjoint {A B : Subgroup D} (f : (A × B) →* D)
    (hi : Function.Injective f) (hf : ∀ a b, f (a,b) = (a : D) * (b : D)) :
    Disjoint A B := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  have he : f (⟨x,hx.1⟩,1) = f (1,⟨x,hx.2⟩) := by simp [hf]
  have hh := congrArg (fun y : A × B => (y.1 : D)) (hi he)
  exact hh

private theorem not_quasisimple_of_disjoint [Finite D] (A B : Subgroup D)
    (hA : A.IsSubnormal) (hna : ¬ IsMulCommutative A) (hne : B ≠ ⊥)
    (hc : ⁅A,B⁆ = ⊥) (hd : Disjoint A B) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  intro hL
  have ha := nonabelian_subnormal_contains_fitting hL A hA hna
  have hb : B ≤ centralizer (A : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using hc)
  have hbL : B ≤ generalizedFitting D :=
    (hb.trans (centralizer_le ha)).trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  apply hne
  exact le_bot_iff.mp ((le_inf (hbL.trans ha) le_rfl).trans (disjoint_iff.mp hd).le)

variable [Finite D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
attribute [local instance] offenderSubgroup_normal

/-- B.5.6(3), with every full source module alternative retained. -/
theorem sourceTwoFactor_not_quasisimple
    (c : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    ¬ IsQuasisimple (generalizedFitting D) :=
  product_not_quasisimple (offenderSubgroup ρ) c.product
    (c.firstCase.factorModel _) (c.secondCase.factorModel _)

/-- The hyperplane module has the same obstruction; no module splitting
or identification of N with D is required. -/
theorem hyperplane_not_quasisimple
    (c : HyperplaneCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    ¬ IsQuasisimple (generalizedFitting D) :=
  product_not_quasisimple (offenderSubgroup ρ) c.product
    (.linearThree BinaryField.two (by decide) c.firstEquiv) (c.secondCase.factorModel _)

/-- B.5.6(4) also has nonquasisimple ambient F*. The C₃ factor cannot
centralize a quasisimple self-centralizing subgroup contained in the
separate A₆ factor. The outer extension need not split. -/
theorem outerSixThree_not_quasisimple
    (c : OuterSixThreeCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  let N := offenderSubgroup ρ
  let f : (c.first × c.second) →* N :=
    (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hf : ∀ a b, f (a,b) = (a : N) * (b : N) := c.product_apply
  have hc : ⁅c.first,c.second⁆ = ⊥ := pair_commute f hf
  have hd : Disjoint c.first c.second := pair_disjoint f
    (Subtype.val_injective.comp c.product.injective) hf
  let : c.first.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← c.generates]
    refine sup_le (sup_le c.first.le_normalizer ?_) (zpowers_le.mpr c.firstOuter.mem_normalizer)
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [commutator_comm] using hc)).trans (Subgroup.centralizer_le_normalizer _)
  have hna : ¬ IsMulCommutative c.first := by
    intro h
    let := h
    have hcomm := commutative_of_injective c.firstEquiv.symm.toMonoidHom c.firstEquiv.symm.injective
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp hcomm
    norm_num at hh
  have hne : c.second.map N.subtype ≠ ⊥ := by
    let : Nontrivial c.second := c.secondEquiv.symm.injective.nontrivial
    let : Nontrivial (c.second.map N.subtype) :=
      (equivMapOfInjective c.second N.subtype N.subtype_injective).injective.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  refine not_quasisimple_of_disjoint (c.first.map N.subtype) (c.second.map N.subtype)
    ((inferInstance : c.first.Normal).isSubnormal.trans' (inferInstance : N.Normal).isSubnormal)
    ?_ hne ?_ ?_
  · intro h
    let := h
    exact hna (commutative_of_injective
      (equivMapOfInjective c.first N.subtype N.subtype_injective).toMonoidHom
      (equivMapOfInjective c.first N.subtype N.subtype_injective).injective)
  · rw [← map_commutator, hc, Subgroup.map_bot]
  · exact disjoint_map N.subtype_injective hd

/-- Every one of the three retained product branches excludes quasisimplicity
of the ambient generalized Fitting subgroup. -/
theorem branch_not_quasisimple (h : Branch (ρ.comp (offenderSubgroup ρ).subtype)) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  unfold Branch at h
  rcases h with h | h | h <;> obtain ⟨h⟩ := h
  · exact sourceTwoFactor_not_quasisimple ρ h
  · exact outerSixThree_not_quasisimple ρ h
  · exact hyperplane_not_quasisimple ρ h

end ProductComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
