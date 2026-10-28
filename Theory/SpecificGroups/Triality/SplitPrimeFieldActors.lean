module
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.GroupAction.PrimeCoefficientRepresentative
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.FieldTheory.PrimeOrderFixedUnits
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Split-prime field actors on the genuine triality carrier

An order-p coefficient automorphism has a fixed unit of order p in the
actual base field whenever p divides q-1. Two independent coroot directions
then give a fixed elementary subgroup of order p² in the original elementary
central quotient. Its faithful inner image and an outer coefficient actor
force rank three in the same automorphism overgroup. Inner--coefficient
coverage retains the representative in that overgroup, so a rank-two bound
excludes outer actors at every split prime.

All positive binary degrees, including q = 2, are retained. No arbitrary
outer-action label or substitute carrier is used. The nonsplit prime tori
are separate from this split-torus statement.

Source: Aschbacher--Smith A.3.18, printed pp.51--53, and 4.3.12(2), p.617;
GLS3 §§2.3--2.6 for the imported coroot words and coefficient coverage.
-/

public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace Triality.Standard.SplitPrimeFieldActors
open OuterOdd OuterOdd.Coverage ConcreteBruhat ConcreteBruhat.TorusCoordinates Parabolics

private def fixedFieldAction (P : Parameters) :
    CoefficientAut P →* (fixedField P ≃+* fixedField P) where
  toFun := coefficientFixedField P
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

private theorem exists_fixed_unit (P : Parameters) {p : ℕ} [Fact p.Prime]
    (σ : CoefficientAut P) (hσ : σ^p=1) (hd : p ∣ P.q-1) :
    ∃ u : (fixedField P)ˣ, orderOf u=p ∧ σ u.val.val=u.val.val := by
  let τ := fixedFieldAction P σ
  have ht : τ^p=1 := by rw [←map_pow,hσ,map_one]
  have hd' : p ∣ Nat.card (fixedField P)-1 := by rwa [card_fixedField]
  have hfix : p ∣ Nat.card (FixedBy.subfield (fixedField P) τ)ˣ := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one ht) with hh | hh
    · have he : τ=1 := orderOf_eq_one_iff.mp hh
      have htop : FixedBy.subfield (fixedField P) τ = ⊤ := by ext x; simp [he]
      rw [htop,Nat.card_units,Nat.card_congr (Subfield.topEquiv : (⊤ : Subfield (fixedField P)) ≃+* fixedField P).toEquiv]
      exact hd'
    · exact FiniteField.prime_dvd_fixed_units τ hh hd'
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' p hfix
  let j := Units.map (FixedBy.subfield (fixedField P) τ).subtype.toMonoidHom
  have hj : Function.Injective j := by
    intro x y hh
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hh
  refine ⟨j u,(orderOf_injective j hj u).trans hu,?_⟩
  exact congrArg Subtype.val u.val.property

private theorem coefficient_torusWord_fixed (P : Parameters) (σ : CoefficientAut P)
    (i : Fin 4) (u : (ExtensionField P)ˣ) (hu : σ u.val=u.val) :
    coefficientSplit P σ (torusWord P i u)=torusWord P i u := by
  simp only [torusWord,weylWord,map_mul,positiveRoot,negativeRoot,
    coefficientSplit_positive,coefficientSplit_negative,map_neg,map_inv₀,map_one,hu]

private theorem coefficient_product_fixed (P : Parameters) (σ : CoefficientAut P)
    (a : Coordinates P) (ha : ∀ i, σ (a i).val=(a i).val) :
    coefficientSplit P σ (product P a)=product P a := by
  dsimp only [product]
  simp only [map_mul]
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (coefficient_torusWord_fixed P σ 0 (a 0) (ha 0))
        (coefficient_torusWord_fixed P σ 2 (a 2) (ha 2)))
      (coefficient_torusWord_fixed P σ 3 (a 3) (ha 3)))
    (coefficient_torusWord_fixed P σ 1 (a 1) (ha 1))

private theorem coefficient_orbit_fixed (P : Parameters) (hp : P.prime=2)
    (σ : CoefficientAut P) (u v : (fixedField P)ˣ)
    (hu : σ u.val.val=u.val.val) (hv : σ v.val.val=v.val.val) :
    coefficientAction P σ (toCarrier P (orbitElementary P hp (fixedUnit P u,v))) =
      toCarrier P (orbitElementary P hp (fixedUnit P u,v)) := by
  have hc : ∀ i, σ ((expand P (fixedUnit P u,v)) i).val =
      ((expand P (fixedUnit P u,v)) i).val := by
    intro i
    fin_cases i <;> simp only [expand,frobenius_fixedUnit]
    all_goals first | exact hu | exact hv
  have he := coefficient_product_fixed P σ (expand P (fixedUnit P u,v)) hc
  have hword := inclusion_orbitElementary P hp (fixedUnit P u,v)
  have hh := (congrArg (coefficientSplit P σ) hword).trans (he.trans hword.symm)
  exact congrArg (toCarrier P) (Subtype.ext (Subtype.ext hh))

/-- The two split coroot directions give a fixed elementary p-square in the
actual elementary central quotient. -/
theorem exists_fixed_elementary (P : Parameters) (hp : P.prime=2)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ P.q-1)
    (σ : CoefficientAut P) (hσ : σ^p=1) :
    ∃ E : Subgroup (Carrier P), IsElementaryAbelian p E ∧ Nat.card E=p^2 ∧
      E ≤ (coefficientAction P σ).fixedSubgroup := by
  obtain ⟨u,hu,hufix⟩ := exists_fixed_unit P σ hσ hd
  let C := zpowers u
  let : IsElementaryAbelian p C := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hu ▸ pow_orderOf_eq_one u)
  let : IsElementaryAbelian p (C × C) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p C) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p C) x.2) }
  let j : C × C →* OrbitParameters P :=
    ((fixedUnit P).comp C.subtype).prodMap C.subtype
  let f : C × C →* Carrier P := (torus P).subtype.comp ((torusMulEquiv P hp).toMonoidHom.comp j)
  have hj : Function.Injective j := by
    intro x y hh
    apply Prod.ext
    · apply Subtype.ext
      apply Units.ext
      apply Subtype.ext
      exact congrArg Units.val (congrArg Prod.fst hh)
    · exact Subtype.ext (congrArg Prod.snd hh)
  have hf : Function.Injective f := (torus P).subtype_injective.comp
    ((torusMulEquiv P hp).injective.comp hj)
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfix (v : C) : σ v.val.val.val=v.val.val.val := by
    obtain ⟨z,hz⟩ := v.property
    have hh : u.val.val^z=v.val.val.val := by
      apply (map_zpow₀ (fixedField P).subtype u.val z).symm.trans
      simpa only [Units.val_zpow_eq_zpow_val,Subfield.subtype_apply] using
        congrArg (fun a : (fixedField P)ˣ => a.val.val) hz
    rw [←hh,map_zpow₀,hufix]
  refine ⟨f.range,inferInstance,?_,?_⟩
  · rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_prod,Nat.card_zpowers,hu,pow_two]
  · rintro _ ⟨x,rfl⟩
    exact (MulAut.mem_fixedSubgroup _ _).mpr
      (coefficient_orbit_fixed P hp σ x.1.val x.2.val (hfix x.1) (hfix x.2))

/-- A field representative retained in a full-inner overgroup forces rank
three at every split prime. -/
theorem field_actor_rank_three (f : ℕ) (hf : 0<f) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ 2^f-1) (A : Subgroup (MulAut (BinaryCarrier f hf)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier f hf) ≤ A)
    (σ : CoefficientAut (binaryParameters f hf)) (hσ : orderOf σ=p)
    (haA : coefficientAction _ σ∈A) : 3 ≤ primeRank p A := by
  let P := binaryParameters f hf
  let a := coefficientAction P σ
  have hout : a ∉ MulAut.innerSubgroup (Carrier P) := by
    intro hh
    have he := (EvenField.NormalForm.coefficientAction_mem_inner_iff f hf σ).mp hh
    have := (Fact.out : p.Prime).one_lt
    rw [he,orderOf_one] at hσ
    omega
  have ha : orderOf a=p := orderOf_eq_prime
    (by rw [←map_pow,show σ^p=1 from hσ ▸ pow_orderOf_eq_one σ,map_one])
    (fun hh => hout (hh ▸ (MulAut.innerSubgroup _).one_mem))
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary P rfl hd σ (hσ ▸ pow_orderOf_eq_one σ)
  let := hE
  let j : Carrier P →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hj : Function.Injective j := fun _ _ hh =>
    MulAut.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot f hf) (congrArg Subtype.val hh)
  let B := E.map j
  let : IsElementaryAbelian p B := IsElementaryAbelian.map j
  let x : A := ⟨a,haA⟩
  have hx : orderOf x=p := (orderOf_injective A.subtype A.subtype_injective x).symm.trans ha
  have hxB : x∉B := by
    rintro ⟨g,_,hg⟩
    exact hout ⟨g,congrArg Subtype.val hg⟩
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * a y * g⁻¹ = a (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B=p^2 := by rw [card_map_of_injective hj,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Every split prime has rank at least two in the actual triality carrier. -/
theorem split_prime_rank (P : Parameters) (hp : P.prime=2)
    {p : ℕ} [Fact p.Prime] (hd : p ∣ P.q-1) : 2 ≤ primeRank p (Carrier P) := by
  obtain ⟨E,hE,hcard,_⟩ := exists_fixed_elementary P hp hd 1 (one_pow p)
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hcard

/-- Full inner--coefficient coverage retains the field representative in the
original automorphism overgroup, so its split-prime rank bound excludes every
outer actor of that prime order. -/
theorem prime_actor_inner_of_split (f : ℕ) (hf : 0<f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    {p : ℕ} [Fact p.Prime] (hd : p ∣ 2^f-1)
    (A : Subgroup (MulAut (BinaryCarrier f hf)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier f hf) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut (BinaryCarrier f hf))
    (haA : a∈A) (ha : orderOf a=p) : a ∈ MulAut.innerSubgroup (BinaryCarrier f hf) := by
  by_contra hout
  let φ := coefficientAction (binaryParameters f hf)
  have hfaithful : Function.Injective ((QuotientGroup.mk'
      (MulAut.innerSubgroup (BinaryCarrier f hf))).comp φ) := by
    apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    exact (EvenField.NormalForm.coefficientAction_mem_inner_iff f hf σ).mp
      ((QuotientGroup.eq_one_iff _).mp hσ)
  obtain ⟨g,σ,he,hσ,hσA,_,_⟩ := MulAut.exists_prime_coefficient_in_overgroup φ hfaithful
    (Coverage.binary_inner_coefficient f hf) A hinner a haA ha hout
  have hh := field_actor_rank_three f hf hd A hinner σ hσ hσA
  omega

end Triality.Standard.SplitPrimeFieldActors
