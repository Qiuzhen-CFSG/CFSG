module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointQuasisimpleComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Structure
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleSolvableComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Comparing the surviving point components and rank-one source rows

The actual surjection from the O₃′ quotient to the faithful point-span
quotient has solvable kernel. B.5.1 supplies a two-group quotient above the
normal offender component. The two successive normal quotients identify
that component's image with both the generalized Fitting subgroup and the
two-residual of the faithful action. Lifting through the original map gives
the same residual identity on the source quotient and an isomorphism of
component central quotients, with all inclusion squares retained.

For source Sylows of order at most eight, every odd prime in an embedded
simple perfect subgroup survives the solvable kernel and divides the
actual offender group. Its corrected B.5 spectrum bounds that prime by
seven. This excludes F.6.18(4),(5) and reduces the corrected dihedral PSL₂
rows to fields of order seven or nine; order twenty-five is excluded by
its additional prime divisor thirteen. All other source rows and all six
B.5 module clauses remain available to subsequent comparisons.

SourceAssembly/PointComparison applies these results to the actual paired
point action after every original rechoice. No Sylow fixed-space equality,
ambient quotient isomorphism, or extra source classification is assumed.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and F.6.18.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

private theorem simple_perfect_injective_through_solvable
    {D E A : Type*} [Group D] [Group E] [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A]
    (g : D →* E) [Group.IsSolvable g.ker]
    (i : A →* D) (hi : Function.Injective i) : Function.Injective (g.comp i) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (g.comp i).ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let j : A →* g.ker := i.codRestrict g.ker (fun a => h.ge (mem_top a))
    have hj : Function.Injective j := fun a b he => hi (congrArg Subtype.val he)
    exact (Group.IsPerfect.not_isSolvable A
      (Group.isSolvable_of_isSolvable_injective (f := j) hj)).elim

private theorem low_sylow_prime_bound
    {D E A : Type*} [Group D] [Group E] [Group A] [Finite D] [Finite E]
    [IsSimpleGroup A] [Group.IsPerfect A]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    (g : D →* E) (hg : Function.Surjective g) [Group.IsSolvable g.ker]
    (S : Sylow 2 D) (hs : Nat.card S ≤ 8)
    (i : A →* D) (hi : Function.Injective i)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card A) : p ≤ 7 := by
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  have h16 : ¬ 16 ∣ Nat.card N := by
    intro hh
    have hh' := S.pow_dvd_card_of_pow_dvd_card
      (show 2^4 ∣ Nat.card D from hh.trans
        (N.card_subgroup_dvd_card.trans (card_dvd_of_surjective g hg)))
    have hl := Nat.le_of_dvd (Nat.card_pos (α := S)) hh'
    omega
  have he : p ∣ Nat.card E := hd.trans (card_dvd_of_injective (g.comp i)
    (simple_perfect_injective_through_solvable g i hi))
  have hn : p ∣ Nat.card N := by
    obtain ⟨k,hk⟩ := hq.exists_card_eq
    have hc : Nat.card E = Nat.card N * 2^k := by
      rw [←hk,←index_eq_card,card_mul_index]
    rw [hc] at he
    exact ((Nat.coprime_two_right.mpr ho).pow_right k).dvd_of_dvd_mul_right he
  exact LowRows.PrimeProduct.FFSpectrum.prime_le_seven_projectiveLine
    (ρ.comp N.subtype) (offenderSubgroup_restrict_eq_top ρ) h16
    (.quasisimple b.quasisimple b.source) p hp hn

private theorem psl_perfect {F : Type*} [Field F] [Finite F]
    (hlarge : 4 ≤ Nat.card F) : Group.IsPerfect PSL(2,F) := by
  obtain ⟨x,hx⟩ : IsCyclic Fˣ := inferInstance
  apply Group.IsPerfect.mk
  apply SL2Simple.PSL_commutator_eq_top
  refine ⟨x,Units.ne_zero x,?_⟩
  intro hh
  have hb := orderOf_le_of_pow_eq_one zero_lt_two (Units.ext hh)
  rw [orderOf_eq_card_of_forall_mem_zpowers hx,Nat.card_units] at hb
  omega

variable {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    (g : D →* E) (hg : Function.Surjective g) [Group.IsSolvable g.ker]
    (S : Sylow 2 D) (hs : Nat.card S ≤ 8)
include b hq hg hs

/-- A large odd rank-one field embedding must have defining prime at most seven. -/
theorem point_comparison_rank_one_prime_bound
    (F : FSource.FieldParameter) (hodd : Odd (Nat.card F.Carrier))
    (hlarge : 4 ≤ Nat.card F.Carrier)
    (i : PSL(2,F.Carrier) →* D) (hi : Function.Injective i) : F.prime ≤ 7 := by
  let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : Group.IsPerfect PSL(2,F.Carrier) := psl_perfect hlarge
  have ho : Odd F.prime := by
    have hd : F.prime ∣ Nat.card F.Carrier := F.card ▸
      dvd_pow_self F.prime (by have := F.degree_pos; omega)
    exact Odd.of_dvd_nat hodd hd
  have hd : F.prime ∣ Nat.card PSL(2,F.Carrier) := by
    apply ((Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_right)
    rw [Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice hodd]
    exact (show F.prime ∣ Nat.card F.Carrier from F.card ▸
      dvd_pow_self F.prime (by have := F.degree_pos; omega)).trans (dvd_mul_right _ _)
  exact low_sylow_prime_bound ρ b hq g hg S hs i hi F.prime_isPrime ho hd

/-- The prime-field components of F.6.18(4),(5) cannot survive the actual map. -/
theorem point_comparison_not_prime_rows
    (F : FSource.FieldParameter) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (i : PSL(2,F.Carrier) →* D) (hi : Function.Injective i) : False := by
  have hc : Nat.card F.Carrier = F.prime := by rw [F.card,hn,pow_one]
  have ho : Odd (Nat.card F.Carrier) := by rw [hc,Nat.odd_iff]; omega
  have hh := point_comparison_rank_one_prime_bound ρ b hq g hg S hs F ho
    (by rw [hc]; omega) i hi
  omega

/-- The corrected dihedral PSL₂ rows leave only field orders seven and nine. -/
theorem point_comparison_dihedral_field
    (F : FSource.FieldParameter) (hn : F.degree ≤ 2)
    (hm : Nat.card F.Carrier % 16 = 7 ∨ Nat.card F.Carrier % 16 = 9)
    (i : PSL(2,F.Carrier) →* D) (hi : Function.Injective i) :
    Nat.card F.Carrier = 7 ∨ Nat.card F.Carrier = 9 := by
  have ho : Odd (Nat.card F.Carrier) := Nat.odd_iff.mpr (by omega)
  have hb := point_comparison_rank_one_prime_bound ρ b hq g hg S hs F ho (by omega) i hi
  have hp := F.prime_isPrime
  have hnpos := F.degree_pos
  have hp3 : F.prime = 3 ∨ F.prime = 5 ∨ F.prime = 7 := by
    have hpo : Odd F.prime := Odd.of_dvd_nat ho (F.card ▸ dvd_pow_self F.prime (by omega))
    interval_cases hpv : F.prime <;> norm_num at hp <;> norm_num at hpo <;> omega
  have hcard : Nat.card F.Carrier = 7 ∨ Nat.card F.Carrier = 9 ∨ Nat.card F.Carrier = 25 := by
    rw [F.card] at hm ⊢
    rcases hp3 with he | he | he <;> rw [he] at hm ⊢ <;>
      interval_cases hd : F.degree <;> norm_num at hm <;> norm_num
  rcases hcard with h | h | hc
  · exact Or.inl h
  · exact Or.inr h
  · have hlarge : 4 ≤ Nat.card F.Carrier := by omega
    let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    let : Group.IsPerfect PSL(2,F.Carrier) := psl_perfect hlarge
    have hh := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice ho
    rw [hc] at hh
    have horder : Nat.card PSL(2,F.Carrier) = 7800 := by norm_num at hh; omega
    have h13 := low_sylow_prime_bound ρ b hq g hg S hs i hi (by decide : Nat.Prime 13)
      (by decide : Odd 13) (by rw [horder]; decide)
    omega
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
variable {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    (hc : pCore 2 E = ⊥)
    (g : D →* E) (hg : Function.Surjective g)
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]

include b hq hc hg

/-- Both residuals are the actual components; the component map and its central
quotient isomorphism retain the original source map and offender inclusion. -/
theorem point_comparison_components :
    let N := offenderSubgroup ρ
    g.ker ≤ (center (generalizedFitting D)).map (generalizedFitting D).subtype ∧
    pResidual 2 D = generalizedFitting D ∧
    pResidual 2 E = generalizedFitting E ∧
    generalizedFitting E = (generalizedFitting N).map N.subtype ∧
    ∃ c : generalizedFitting N ≃* generalizedFitting E,
      (∀ n, (c n : E) = ((n : N) : E)) ∧
      ∃ a : generalizedFitting D →* generalizedFitting N,
        Function.Surjective a ∧ (∀ x, ((a x : N) : E) = g x) ∧
        ∃ e : generalizedFitting D ⧸ center (generalizedFitting D) ≃*
            generalizedFitting N ⧸ center (generalizedFitting N),
          ∀ x, e (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (a x) := by
  intro N
  let : N.Normal := offenderSubgroup_normal ρ
  let := b.quasisimple
  have hf := normalTwoTower_fitting N (generalizedFitting N) b.actorQuotient_twoGroup hq hc
  have hr := normalTwoTower_residual N (generalizedFitting N) b.actorQuotient_twoGroup hq
  have hquot : IsPGroup 2 (E ⧸ generalizedFitting E) :=
    (normalTwoTower_quotient N (generalizedFitting N) b.actorQuotient_twoGroup hq).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hf.symm)
  let c : generalizedFitting N ≃* generalizedFitting E :=
    ((generalizedFitting N).equivMapOfInjective N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr hf.symm)
  have hcoe (n : generalizedFitting N) : (c n : E) = ((n : N) : E) := rfl
  let a : generalizedFitting D →* generalizedFitting N :=
    c.symm.toMonoidHom.comp (solvableImageComponent g hg)
  have ha : Function.Surjective a := c.symm.surjective.comp
    (solvableImageComponent_surjective g hg)
  have hact (x : generalizedFitting D) : ((a x : N) : E) = g x := by
    rw [←hcoe]
    change ((c (c.symm (solvableImageComponent g hg x))) : E) = g x
    rw [c.apply_symm_apply,solvableImageComponent_coe]
  let : IsSimpleGroup (generalizedFitting N ⧸ center (generalizedFitting N)) :=
    IsQuasisimple.simple
  let : Nontrivial (generalizedFitting N) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting N))).nontrivial
  exact ⟨solvable_kernel_le_fitting_center g,solvableImage_residual_eq_fitting g hg hquot,
    hr.trans hf.symm,hf,c,hcoe,a,ha,hact,
    IsQuasisimple.centralQuotientEquiv a ha,IsQuasisimple.centralQuotientEquiv_mk a ha⟩
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization


@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v w

/-- Results of the original quotient comparison. The component maps are actual
maps, and the low-Sylow conclusions apply to embedded PSL₂ models. -/
structure PointQuotientComparison
    {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (g : D →* E) : Prop where
  kernel : g.ker ≤ (center (generalizedFitting D)).map (generalizedFitting D).subtype
  source_residual : pResidual 2 D = generalizedFitting D
  action_residual : pResidual 2 E = generalizedFitting E
  component_image : generalizedFitting E =
    (generalizedFitting (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype
  components :
    ∃ c : generalizedFitting (offenderSubgroup ρ) ≃* generalizedFitting E,
      (∀ n, (c n : E) = ((n : offenderSubgroup ρ) : E)) ∧
      ∃ a : generalizedFitting D →* generalizedFitting (offenderSubgroup ρ),
        Function.Surjective a ∧ (∀ x, ((a x : offenderSubgroup ρ) : E) = g x) ∧
        ∃ e : generalizedFitting D ⧸ center (generalizedFitting D) ≃*
            generalizedFitting (offenderSubgroup ρ) ⧸ center (generalizedFitting (offenderSubgroup ρ)),
          ∀ x, e (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (a x)
  not_prime_rows : ∀ (S : Sylow 2 D), Nat.card S ≤ 8 →
    ∀ (F : FSource.FieldParameter.{u}), F.degree = 1 →
      (F.prime % 24 = 11 ∨ F.prime % 24 = 13) →
      ∀ i : PSL(2,F.Carrier) →* D, ¬ Function.Injective i
  dihedral_fields : ∀ (S : Sylow 2 D), Nat.card S ≤ 8 →
    ∀ (F : FSource.FieldParameter.{u}), F.degree ≤ 2 →
      (Nat.card F.Carrier % 16 = 7 ∨ Nat.card F.Carrier % 16 = 9) →
      ∀ i : PSL(2,F.Carrier) →* D, Function.Injective i →
        Nat.card F.Carrier = 7 ∨ Nat.card F.Carrier = 9

/-- Construct the comparison from the proved bounded branch and the actual
solvable-kernel surjection. No Sylow fixed-space hypothesis is used. -/
theorem point_quotient_comparison
    {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    (hc : pCore 2 E = ⊥)
    (g : D →* E) (hg : Function.Surjective g)
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker] :
    PointQuotientComparison ρ g := by
  obtain ⟨hk,hr,hr',he,hcomponents⟩ := point_comparison_components ρ b hq hc g hg
  exact ⟨hk,hr,hr',he,hcomponents,
    point_comparison_not_prime_rows ρ b hq g hg,
    point_comparison_dihedral_field ρ b hq g hg⟩
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u v w
variable {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}
    (c : PointQuotientComparison ρ g)
include c

/-- Apply the exclusion to the actual ambient isomorphism of F.6.18(4). -/
theorem PointQuotientComparison.not_prime_linear_row {S : Sylow 2 D}
    (hs : Nonempty (S ≃* FSource.E4))
    (F : FSource.FieldParameter.{u}) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (e : D ≃* PSL(2,F.Carrier)) : False := by
  apply c.not_prime_rows S _ F hn hm e.symm.toMonoidHom e.symm.injective
  rw [Nat.card_congr hs.some.toEquiv]
  norm_num [FSource.E4,FSource.C,Nat.card_prod]

/-- Apply the exclusion to the actual component isomorphism of F.6.18(5). -/
theorem PointQuotientComparison.not_prime_projective_row {S : Sylow 2 D}
    (hs : Nonempty (S ≃* DihedralGroup 4))
    (F : FSource.FieldParameter.{u}) (hn : F.degree = 1)
    (hm : F.prime % 24 = 11 ∨ F.prime % 24 = 13)
    (e : generalizedFitting D ≃* PSL(2,F.Carrier)) : False := by
  apply c.not_prime_rows S _ F hn hm
    ((generalizedFitting D).subtype.comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective)
  rw [Nat.card_congr hs.some.toEquiv,DihedralGroup.nat_card]

/-- Both prime congruences in the corrected dihedral source row are retained. -/
theorem PointQuotientComparison.dihedral_source_field {S : Sylow 2 D}
    (r : FSource.DihedralPSL2Row S) :
    Nat.card r.field.Carrier = 7 ∨ Nat.card r.field.Carrier = 9 := by
  apply c.dihedral_fields S _ r.field r.degree r.congruence
    r.model.symm.toMonoidHom r.model.symm.injective
  rw [Nat.card_congr r.sylow.some.toEquiv,DihedralGroup.nat_card]
/-- The surviving field parameters give actual original ambient model
isomorphisms through the checked exceptional comparisons. -/
theorem PointQuotientComparison.dihedral_source_models {S : Sylow 2 D}
    (r : FSource.DihedralPSL2Row S) :
    Nonempty (D ≃* PSL(3,ZMod 2)) ∨ Nonempty (D ≃* alternatingGroup (Fin 6)) := by
  rcases c.dihedral_source_field r with h | h
  · exact Or.inl ⟨r.model.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two h)⟩
  · exact Or.inr ⟨r.model.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 h)⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
