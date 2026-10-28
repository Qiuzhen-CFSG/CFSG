module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes
public import Theory.GroupTheory.NormalizedSupCard
public import GorensteinWalter.PSL2Cardinality

/-!
# The pointwise fixer of the actual residual image in J₁

The image of the original flag residual is a centerless group of order sixty.
Its centralizer in J₁ has order dividing 2·7·11·19, by the disjoint product
order formula. The certified involution calculations exclude each odd prime:
the residual contains an involution, whereas elements of orders 7, 11 and 19
commute with none. Every J₁ automorphism is inner, so the pointwise fixer
in the full automorphism group is a two-group as well.

Transport along the supplied component marking applies this to the literal
image in K/O₂(K). Consequently the odd section centralizer acts trivially
on that quotient and K normalizes the original displacement [X,T]. Both
terminal contradiction consumers now need no pointwise-fixer premise.
The cubic, SL₃/Sp₄ geometry, G₂ exclusion and construction of the exceptional
configuration remain with qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.16, printed p.591; the intrinsic J₁ facts
are proved by the imported model certificates and automorphism theorem.
-/

public noncomputable section
open Subgroup

private theorem no_commuting_involution_of_representative {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p^2 ∣ Nat.card Janko1.Model) (r : Janko1.Model) (hr : orderOf r = p)
    (hno : ∀ t : Janko1.Model, orderOf t = 2 → ¬ Commute t r)
    (x t : Janko1.Model) (hx : orderOf x = p) (ht : orderOf t = 2) :
    ¬ Commute t x := by
  obtain ⟨k,g,hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd hp hsq hx hr
  intro hc
  have ht' : orderOf (MulAut.conj g t) = 2 := (MulEquiv.orderOf_eq _ _).trans ht
  apply hno _ ht'
  rw [hg]
  exact (hc.pow_right k).map (MulAut.conj g)

private theorem janko_centralizer_two (B : Subgroup Janko1.Model)
    (hcard : Nat.card B = 60) (hcenter : center B = ⊥) :
    IsPGroup 2 (centralizer (B : Set Janko1.Model)) := by
  let C := centralizer (B : Set Janko1.Model)
  have hd : Disjoint B C := by
    apply disjoint_def.mpr
    intro g hg hc
    have hz : (⟨g,hg⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro b
      apply Subtype.ext
      exact mem_centralizer_iff.mp hc b b.property
    have hz1 : (⟨g,hg⟩ : B) = 1 := mem_bot.mp (hcenter ▸ hz)
    exact congrArg (fun z : B => (z : Janko1.Model)) hz1
  have hprod : Nat.card (B ⊔ C : Subgroup Janko1.Model) = 60 * Nat.card C := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint B C (Subgroup.centralizer_le_normalizer _) hd,hcard]
  have hcdiv : Nat.card C ∣ 2926 := by
    have hh := (B ⊔ C).card_subgroup_dvd_card
    rw [hprod,Janko1.card_model] at hh
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 60) hh
  have hnot {p : ℕ} (hp : p.Prime)
      (hsq : ¬ p^2 ∣ Nat.card Janko1.Model) (r : Janko1.Model) (hr : orderOf r = p)
      (hno : ∀ t : Janko1.Model, orderOf t = 2 → ¬ Commute t r) :
      ¬ p ∣ Nat.card C := by
    intro hpd
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) p hpd
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 (by rw [hcard]; decide)
    exact no_commuting_involution_of_representative hp hsq r hr hno x t
      ((Subgroup.orderOf_coe x).trans hx) ((Subgroup.orderOf_coe t).trans ht)
      (mem_centralizer_iff.mp x.property t t.property)
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hpd := (Nat.mem_primeFactors.mp hp).2.1
  have hdiv := hpd.trans hcdiv
  have he : p = 2 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
    change p ∣ 2 * 7 * 11 * 19 at hdiv
    simpa only [hprime.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hprime (by decide : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hprime (by decide : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hprime (by decide : Nat.Prime 19),or_assoc] using hdiv
  rcases he with rfl | rfl | rfl | rfl
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩
  · exact (hnot (by decide) (by norm_num [Janko1.card_model]) _ Janko1.orderOf_ab
      Janko1.LocalStructure.LargePrimes.no_involution_commutes_seven hpd).elim
  · exact (hnot (by decide) (by norm_num [Janko1.card_model]) _ Janko1.OrderCertificate.orderOf_eleven
      Janko1.LocalStructure.LargePrimes.no_involution_commutes_eleven hpd).elim
  · exact (hnot (by decide) (by norm_num [Janko1.card_model]) _ Janko1.orderOf_abab_sq
      Janko1.LocalStructure.LargePrimes.no_involution_commutes_nineteen hpd).elim

private theorem janko_fixer_two (B : Subgroup Janko1.Model)
    (hcard : Nat.card B = 60) (hcenter : center B = ⊥) :
    IsPGroup 2 (fixingSubgroup (MulAut Janko1.Model) (B : Set Janko1.Model)) := by
  let C := centralizer (B : Set Janko1.Model)
  let H := fixingSubgroup (MulAut Janko1.Model) (B : Set Janko1.Model)
  let a : C →* H := ((MulAut.conj : Janko1.Model →* MulAut Janko1.Model).comp C.subtype).codRestrict H (by
    intro g y
    change (g : Janko1.Model) * (y : Janko1.Model) * (g : Janko1.Model)⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.mp g.property y y.property).symm)
  apply (janko_centralizer_two B hcard hcenter).of_surjective a
  intro b
  obtain ⟨g,hg⟩ := Janko1.OuterCertificate.aut_inner b
  have hgC : g ∈ C := by
    rw [mem_centralizer_iff]
    intro y hy
    have hh := b.property (⟨y,hy⟩ : B)
    change (b : MulAut Janko1.Model) y = y at hh
    rw [←hg,MulAut.conj_apply,mul_inv_eq_iff_eq_mul] at hh
    exact hh.symm
  exact ⟨⟨g,hgC⟩,Subtype.ext hg⟩

private theorem psl2_four_card_center {B : Type*} [Group B] [Group.IsPerfect B]
    (hm : ClassicalGroup.IsPSL B 2 4) : Nat.card B = 60 ∧ center B = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  have hcard : Nat.card B = 60 := by
    rw [Nat.card_congr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
    norm_num
  have hfour : 4 ≤ Nat.card F := hF.ge
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup B := e.isSimpleGroup
  refine ⟨hcard,?_⟩
  rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht)).elim

private theorem marked_janko_fixer_two {H : Type*} [Group H]
    (e : H ≃* Janko1.Model) (B : Subgroup H) [Group.IsPerfect B]
    (hm : ClassicalGroup.IsPSL B 2 4) :
    IsPGroup 2 (fixingSubgroup (MulAut H) (B : Set H)) := by
  let Bm := B.map e.toMonoidHom
  let d := e.subgroupMap B
  let : Group.IsPerfect Bm := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  have hm' : ClassicalGroup.IsPSL Bm 2 4 := by
    obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
    exact ⟨F,hF,hfin,hcard,⟨d.symm.trans a⟩⟩
  obtain ⟨hcard,hcenter⟩ := psl2_four_card_center hm'
  let I := fixingSubgroup (MulAut H) (B : Set H)
  let J := fixingSubgroup (MulAut Janko1.Model) (Bm : Set Janko1.Model)
  let a : I →* J := ((MulAut.congr e).toMonoidHom.comp I.subtype).codRestrict J (by
    intro a y
    obtain ⟨b,hb,hby⟩ := y.property
    change e ((a : MulAut H) (e.symm (y : Janko1.Model))) = y
    rw [←hby]
    change e ((a : MulAut H) (e.symm (e b))) = e b
    rw [e.symm_apply_apply]
    exact congrArg e (a.property ⟨b,hb⟩))
  apply (janko_fixer_two Bm hcard hcenter).of_injective a
  intro x y hxy
  apply Subtype.ext
  apply (MulAut.congr e).injective
  exact congrArg Subtype.val hxy

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}
    {A : OddSupplement T} (E : JankoConfiguration S f A)
namespace JankoConfiguration

/-- The pointwise fixer of the original residual image is a two-group. -/
theorem residualImageFixer_isTwoGroup : IsPGroup 2 E.residualImageFixer := by
  obtain ⟨e⟩ := E.model
  let : Group.IsPerfect (f.Li E.index) := localResidual_perfect _
  let : Group.IsPerfect E.residualImage := Group.IsPerfect.range E.residualProjection
  exact marked_janko_fixer_two e E.residualImage E.residualImage_isPSL2Four

/-- The actual odd section centralizer acts trivially on K/O₂(K). -/
theorem oddSectionCentralizer_trivial_component_action :
    E.oddSectionCentralizer ≤ E.componentSectionCentralizer :=
  E.oddSectionCentralizer_le_componentSectionCentralizer E.residualImageFixer_isTwoGroup

/-- The exceptional component normalizes the literal displacement subgroup. -/
theorem displacement_normalized_by_component :
    E.component ≤ normalizer (E.displacement : Set G) :=
  E.component_normalizes_displacement_of_fixer E.residualImageFixer_isTwoGroup

/-- The SL₃ terminal reduction, with component normalization discharged. -/
theorem false_of_displacement_normalized_by_L
    (hne : E.oddSectionCentralizer ≠ ⊥)
    (hLQ : L ≤ normalizer (E.displacement : Set G)) : False :=
  E.false_of_common_normal_of_fixer E.residualImageFixer_isTwoGroup hne hLQ

/-- The Sp₄ terminal reduction, with component normalization discharged. -/
theorem false_of_small_moved_displacement
    (hsmall : Nat.card E.displacement ≤ 2 ^ 16)
    (hmoves : ¬ f.Li E.index ≤ centralizer (E.displacement : Set G)) : False :=
  E.false_of_small_displacement_of_fixer E.residualImageFixer_isTwoGroup hsmall hmoves

end JankoConfiguration
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
