module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.Obstruction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.OuterShape
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Exhaustive FF branch reduction on the actual actor

A finite actor with quasisimple generalized Fitting subgroup cannot be
trivial or solvable. Its two-factor and hyperplane alternatives contain
commuting nonabelian normal factors, contrary to the component dichotomy
and self-centralization. This includes the exceptional indecomposable
factor, whose action identifies its actual SL₃(2) actor.

In the outer A₆–C₃ case, the literal product and specified outer generator
make A₆ normal. The component dichotomy places F* in this nonabelian
factor, so self-centralization places the separate C₃ there as well,
contrary to their disjointness. Only the group configuration is used;
no fixed-space splitting or split group extension is assumed.

The surviving witness retains every B.5.1 action clause. Separate exports
support both the preserved full interface and the corrected projective-line
convention. The SourceReduction parent applies them to J(I)* on U_I,
without identifying that actor with an unrelated offender subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99–103, B.5.6, p.105, and 15.3.26–31, pp.1130–1132.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives

variable {D : Type*} [Group D]

private theorem quasisimple_not_solvable (h : IsQuasisimple D) :
    ¬ Group.IsSolvable D := by
  let _ := h
  let _ := h.simple
  let _ : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let _ : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))

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
  exact congrArg (fun y : A × B => (y.1 : D)) (hi he)

private theorem product_first_normal {A B : Subgroup D} (c : InternalProduct A B) :
    A.Normal := by
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

private theorem product_second_normal {A B : Subgroup D} (c : InternalProduct A B) :
    B.Normal := by
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (pair_commute c.equiv.toMonoidHom c.apply_eq)
  apply product_first_normal (A := B) (B := A)
  refine ⟨(MulEquiv.prodComm : B × A ≃* A × B).trans c.equiv, ?_⟩
  intro b a
  exact (c.apply_eq a b).trans
    (mem_centralizer_iff.mp (hc a.property) b b.property).symm

private theorem product_not_quasisimple [Finite D] {A B : Subgroup D}
    (c : InternalProduct A B) (ha : FactorModel A) (hb : FactorModel B) :
    ¬ IsQuasisimple (generalizedFitting D) :=
  ProductComparison.not_quasisimple_of_commuting_subnormal A B
    (product_first_normal c).isSubnormal (product_second_normal c).isSubnormal
    (ProductComparison.factor_not_commutative ha)
    (ProductComparison.factor_not_commutative hb)
    (pair_commute c.equiv.toMonoidHom c.apply_eq)

/-- The actual outer A₆–C₃ group configuration already rules out a
quasisimple F*. No assertion about splitting its module is used. -/
theorem outerShape_not_quasisimple [Finite D] (c : ChapterB.OuterSixThreeShape D) :
    ¬ IsQuasisimple (generalizedFitting D) := by
  intro hL
  let f : (c.first × c.second) →* D :=
    (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have hc : ⁅c.first,c.second⁆ = ⊥ := pair_commute f c.product_apply
  have hd : Disjoint c.first c.second := pair_disjoint f
    (Subtype.val_injective.comp c.product.injective) c.product_apply
  have ho : InducesOuter c.first c.element := c.firstOuter
  have hn : c.first.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← c.generates]
    refine sup_le (sup_le c.first.le_normalizer ?_) (zpowers_le.mpr ho.mem_normalizer)
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [commutator_comm] using hc)).trans (Subgroup.centralizer_le_normalizer _)
  have hna : ¬ IsMulCommutative c.first := by
    intro h
    let _ := h
    have hcomm : IsMulCommutative (alternatingGroup (Fin 6)) :=
      ⟨⟨fun a b => c.firstEquiv.symm.injective (by simp only [map_mul, mul_comm'])⟩⟩
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp hcomm
    norm_num at hh
  have hcomp : IsComponent D (generalizedFitting D) :=
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hL⟩
  have ha : generalizedFitting D ≤ c.first := by
    rcases hcomp.subnormal_dichotomy c.first hn.isSubnormal with h | h
    · exact h
    · have hz : c.first ≤ centralizer (generalizedFitting D : Set D) :=
        commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using h)
      have hle := hz.trans ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
      exact (hna ⟨⟨fun a b => Subtype.ext
        (mem_centralizer_iff.mp (hz a.property) b (hle b.property)).symm⟩⟩).elim
  have hb : c.second ≤ c.first := by
    have hz : c.second ≤ centralizer (c.first : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp (by simpa [commutator_comm] using hc)
    exact ((hz.trans (centralizer_le ha)).trans
      ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le).trans ha
  have hz : c.second = ⊥ := le_bot_iff.mp
    ((le_inf hb le_rfl).trans (disjoint_iff.mp hd).le)
  let _ : Nontrivial c.second := c.secondEquiv.symm.injective.nontrivial
  exact (nontrivial_iff_ne_bot _).mp inferInstance hz

variable [Finite D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private theorem not_nonquasisimple (hL : IsQuasisimple (generalizedFitting D)) :
    ¬ NonQuasisimpleAlternative ρ := by
  intro h
  cases h with
  | symmetricThree c =>
    let _ := symmetricThree_solvable
    let _ : Group.IsSolvable D :=
      Group.isSolvable_of_isSolvable_injective (f := c.equiv.toMonoidHom) c.equiv.injective
    exact quasisimple_not_solvable hL inferInstance
  | twoFactors c => exact product_not_quasisimple c.product c.firstModel c.secondModel hL
  | outerSixThree c => exact outerShape_not_quasisimple c.toGroupShape hL
  | hyperplane c =>
    exact product_not_quasisimple c.product
      (.linearThree BinaryField.two (by decide) c.firstEquiv) (c.secondCase.factorModel _) hL

/-- Every nonquasisimple source branch is excluded on the same finite actor,
retaining the full B.5.1 action witness in the surviving branch. -/
theorem quasisimple_source_of_sourceAlternative
    (hL : IsQuasisimple (generalizedFitting D)) (h : SourceAlternative ρ) :
    Nonempty (QuasisimpleSourceConclusion ρ (generalizedFitting D)) := by
  cases h with
  | trivial ht =>
    let _ := ht
    exact (quasisimple_not_solvable hL inferInstance).elim
  | quasisimple _ c => exact ⟨c⟩
  | symmetricThree c => exact (not_nonquasisimple ρ hL (.symmetricThree c)).elim
  | twoFactors c => exact (not_nonquasisimple ρ hL (.twoFactors (c.toBasic ρ))).elim
  | outerSixThree c => exact (not_nonquasisimple ρ hL (.outerSixThree c)).elim
  | hyperplane c => exact (not_nonquasisimple ρ hL (.hyperplane c)).elim

/-- The same exhaustive reduction with the source-correct projective-line
convention in the irreducible triple-cover clause. -/
theorem quasisimple_source_of_projectiveLineAlternative
    (hL : IsQuasisimple (generalizedFitting D)) (h : ProjectiveLine.SourceAlternative ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D)) := by
  cases h with
  | trivial ht =>
    let _ := ht
    exact (quasisimple_not_solvable hL inferInstance).elim
  | quasisimple _ c => exact ⟨c⟩
  | symmetricThree c => exact (not_nonquasisimple ρ hL (.symmetricThree c)).elim
  | twoFactors c => exact (not_nonquasisimple ρ hL (.twoFactors (c.toBasic ρ))).elim
  | outerSixThree c => exact (not_nonquasisimple ρ hL (.outerSixThree c)).elim
  | hyperplane c => exact (not_nonquasisimple ρ hL (.hyperplane c)).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
