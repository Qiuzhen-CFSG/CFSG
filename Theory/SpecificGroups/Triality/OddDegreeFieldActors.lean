module
public import Theory.SpecificGroups.Triality.BinarySevenPlane
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.Diagram
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Mathlib.Data.Nat.GCD.Basic
public import Theory.SpecificGroups.Triality.SplitPrimeFieldActors

/-!
# The remaining odd-degree field actors on genuine binary triality

When an odd source degree is coprime to the triality base degree, the actual
carrier order forces every common torus prime to be seven. A coefficient
automorphism whose order divides seven fixes a copy of GF(8). If the base
degree is prime to three, entrywise embedding, with reversal of the pinned
D4 cycle when necessary, embeds the genuine fixed group at q = 2 in its
coefficient fixed points. Its checked seven-plane therefore supplies a fixed
elementary subgroup of order 49 on the original elementary central quotient.

A coefficient actor of order seven and the faithful inner image of that plane
force rank three in the same automorphism overgroup. Inner--coefficient
coverage retains the actor in that overgroup. This closes the nonsplit row
without assuming a label for the outer action or replacing the carrier.

Sources: Aschbacher--Smith A.3.18, pp.51--53, and 4.3.12(2), p.617;
GLS3 §§2.3--2.6 for coefficient and diagram conventions. The imported genuine
binary seven-plane retains its explicit ATLAS p.89 root-word construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.OddDegreeFieldActors

private theorem prime_seven_of_exponents {n f p : ℕ} (hp : p.Prime) (hn : Odd n) (hc : Nat.Coprime n f)
    (hnp : p ∣ 2^n-1) (hfp : p ∣ 2^(12*f)-1) : p=7 := by
  have hd := Nat.dvd_gcd hnp hfp
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hd
  have hgf : Nat.Coprime (Nat.gcd n (12*f)) f := hc.of_dvd_left (Nat.gcd_dvd_left _ _)
  have hg12 : Nat.gcd n (12*f) ∣ 12 := hgf.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
  have hg4 : Nat.Coprime (Nat.gcd n (12*f)) 4 :=
    ((Nat.coprime_two_right.mpr hn).pow_right 2).of_dvd_left (Nat.gcd_dvd_left _ _)
  have hg3 : Nat.gcd n (12*f) ∣ 3 := hg4.dvd_of_dvd_mul_left hg12
  have hp7 : p ∣ 7 := hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hg3)
  exact ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hp7).resolve_left hp.ne_one

open OuterOdd EvenField ConcreteBruhat.FixedDescent
open Theory.AlgebraicGroup.StandardRootSystem
local instance matrixIndexDecidableEq :
    DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2+2)) := instDecidableEqSum
local notation "P₀" => binaryParameters 1 Nat.zero_lt_one

private theorem exists_fixed_embedding_aux {K F₀ : Type*} [Field K] [Finite K] [CharP K 2]
    [Algebra (ZMod 2) K] [Field F₀] [Algebra (ZMod 2) F₀]
    (f : ℕ) (hK : Module.finrank (ZMod 2) K=3*f)
    (hF₀ : Module.finrank (ZMod 2) F₀=3)
    (σ : K ≃+* K) (hσ : σ^7=1) :
    ∃ j : F₀ →+* K,
      ∀ t, σ (j t)=j t := by
  let H := zpowers σ
  let F := FixedPoints.subfield H K
  let : Finite H := Finite.of_injective
    (fun a : H => (a.val : K → K)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  have hd : Module.finrank F K=1 ∨ Module.finrank F K=7 := by
    rw [FixedPoints.finrank_eq_card,Fintype.card_eq_nat_card,Nat.card_zpowers]
    exact (Nat.dvd_prime (by decide : Nat.Prime 7)).mp (orderOf_dvd_of_pow_eq_one hσ)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Module (ZMod 2) F := Algebra.toModule
  have ht := Module.finrank_mul_finrank (ZMod 2) F K
  rw [hK] at ht
  have hdiv : Module.finrank (ZMod 2) F₀ ∣ Module.finrank (ZMod 2) F := by
    rw [hF₀]
    rcases hd with hd | hd <;> rw [hd] at ht <;> omega
  obtain ⟨j⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdiv
  refine ⟨F.subtype.comp j.toRingHom,?_⟩
  intro t
  exact (j t).property ⟨σ,mem_zpowers σ⟩

private theorem exists_fixed_embedding (f : ℕ) (hf : 0<f)
    (σ : CoefficientAut (binaryParameters f hf)) (hσ : σ^7=1) :
    ∃ j : ExtensionField P₀ →+* ExtensionField (binaryParameters f hf),
      ∀ t, σ (j t)=j t :=
  exists_fixed_embedding_aux (K := GaloisField 2 (3*f)) (F₀ := GaloisField 2 (3*1))
    f (GaloisField.finrank 2 (n := 3*f) (by omega))
    (GaloisField.finrank 2 (n := 3*1) (by decide)) σ hσ

private def splitMap {f : ℕ} {hf : 0<f}
    (j : ExtensionField P₀ →+* ExtensionField (binaryParameters f hf)) :
    SplitGroup P₀ →* SplitGroup (binaryParameters f hf) :=
  RootPairing.SimpleGeckGroup.map j

private theorem splitMap_injective {f : ℕ} {hf : 0<f}
    (j : ExtensionField P₀ →+* ExtensionField (binaryParameters f hf)) :
    Function.Injective (splitMap j) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  ext i k
  apply j.injective
  exact congrArg (fun z : SplitGroup (binaryParameters f hf) => z.val.val i k) h

private theorem small_frobenius_mod (f : ℕ) :
    coefficientFrobenius 1 Nat.zero_lt_one f = coefficientFrobenius 1 Nat.zero_lt_one (f%3) := by
  change iterateFrobeniusEquiv _ 2 f = iterateFrobeniusEquiv _ 2 (f%3)
  simp only [iterateFrobeniusEquiv_eq_pow]
  have horder := orderOf_primeFrobenius 1 Nat.zero_lt_one
  simpa only [horder,Nat.mul_one] using
    (pow_mod_orderOf (frobeniusEquiv (GaloisField 2 (3*1)) 2) f).symm

private theorem splitMap_graphField {f : ℕ} {hf : 0<f}
    (j : ExtensionField P₀ →+* ExtensionField (binaryParameters f hf))
    (x : SplitGroup P₀) :
    graphFieldAutomorphism (binaryParameters f hf) (splitMap j x) =
      splitMap j (diagramAutomorphism P₀ (splitFrobenius 1 Nat.zero_lt_one (f%3) x)) := by
  have hF : fieldAutomorphism (binaryParameters f hf) (splitMap j x) =
      splitMap j (splitFrobenius 1 Nat.zero_lt_one f x) := by
    apply Subtype.ext
    apply Units.ext
    ext i k
    exact (map_pow j (x.val.val i k) (2^f)).symm
  have hd : diagramAutomorphism (binaryParameters f hf) (splitMap j
      (splitFrobenius 1 Nat.zero_lt_one f x)) =
      splitMap j (diagramAutomorphism P₀ (splitFrobenius 1 Nat.zero_lt_one f x)) :=
    (RootPairing.SimpleGeckGroup.diagramEquiv_map _ _ _ j _)
  have he := ((diagram_field_commute (binaryParameters f hf) (splitMap j x)).symm.trans
    (congrArg (diagramAutomorphism (binaryParameters f hf)) hF)).trans hd
  have hm : splitFrobenius 1 Nat.zero_lt_one f = splitFrobenius 1 Nat.zero_lt_one (f%3) :=
    congrArg (splitCoefficientAction P₀) (small_frobenius_mod f)
  exact he.trans (congrArg (fun a : MulAut (SplitGroup P₀) => splitMap j (diagramAutomorphism P₀ (a x))) hm)

private theorem reverse_fixed (x : fixedSubgroup P₀) :
    diagramAutomorphism P₀ (splitFrobenius 1 Nat.zero_lt_one 2 (reverseDiagram P₀ x)) =
      reverseDiagram P₀ x := by
  have hh : inverseGraphHalf 1 Nat.zero_lt_one 2 x = x := by
    change diagramAutomorphism P₀ (diagramAutomorphism P₀
      (splitFrobenius 1 Nat.zero_lt_one 2 x)) = x
    have hF : splitFrobenius 1 Nat.zero_lt_one 2 = fieldAutomorphism P₀ * fieldAutomorphism P₀ := by
      apply MulEquiv.ext
      intro g
      apply Subtype.ext
      apply Units.ext
      ext i k
      change g.val.val i k ^ 4 = (g.val.val i k ^ 2)^2
      ring
    rw [hF]
    change diagramAutomorphism P₀ (diagramAutomorphism P₀
      (fieldAutomorphism P₀ (fieldAutomorphism P₀ x))) = x
    have hx : diagramAutomorphism P₀ (fieldAutomorphism P₀ x) = x :=
      (diagram_field_commute P₀ x).trans x.property
    calc
      _ = diagramAutomorphism P₀ (fieldAutomorphism P₀
          (diagramAutomorphism P₀ (fieldAutomorphism P₀ x))) :=
        congrArg (diagramAutomorphism P₀) (diagram_field_commute P₀ (fieldAutomorphism P₀ x))
      _ = diagramAutomorphism P₀ (fieldAutomorphism P₀ x) :=
        congrArg (fun z => diagramAutomorphism P₀ (fieldAutomorphism P₀ z)) hx
      _ = x := hx
  exact (reverseDiagram_half 1 Nat.zero_lt_one 2 x).symm.trans (congrArg (reverseDiagram P₀) hh)

private theorem exists_fixed_injection (f : ℕ) (hf : 0<f) (hf3 : ¬3∣f)
    (σ : CoefficientAut (binaryParameters f hf)) (hσ : σ^7=1) :
    ∃ k : fixedSubgroup P₀ →* fixedSubgroup (binaryParameters f hf),
      Function.Injective k ∧ ∀ x, coefficientSplit _ σ (k x).val=(k x).val := by
  let j := Classical.choose (exists_fixed_embedding f hf σ hσ)
  have hj := Classical.choose_spec (exists_fixed_embedding f hf σ hσ)
  have hs (x : SplitGroup P₀) : coefficientSplit _ σ (splitMap j x)=splitMap j x := by
    apply Subtype.ext
    apply Units.ext
    ext i t
    exact hj (x.val.val i t)
  have hh : ∃ k : SplitGroup P₀ →* SplitGroup (binaryParameters f hf),
      Function.Injective k ∧
      (∀ x : fixedSubgroup P₀, k x ∈ fixedSubgroup (binaryParameters f hf)) ∧
      ∀ x, coefficientSplit _ σ (k x)=k x := by
    have hmod : f%3=1 ∨ f%3=2 := by omega
    rcases hmod with h1 | h2
    · refine ⟨splitMap j,splitMap_injective j,?_,hs⟩
      intro x
      change graphFieldAutomorphism _ (splitMap j x)=splitMap j x
      have hx : diagramAutomorphism P₀ (fieldAutomorphism P₀ x)=x :=
        (diagram_field_commute P₀ x).trans x.property
      have he : splitFrobenius 1 Nat.zero_lt_one (f%3) x = fieldAutomorphism P₀ x :=
        congrArg (fun m => splitFrobenius 1 Nat.zero_lt_one m x) h1
      exact (splitMap_graphField j x).trans
        (congrArg (splitMap j) ((congrArg (diagramAutomorphism P₀) he).trans hx))
    · refine ⟨(splitMap j).comp (reverseDiagram P₀).toMonoidHom,
        (splitMap_injective j).comp (reverseDiagram P₀).injective,?_,fun x => hs _⟩
      intro x
      change graphFieldAutomorphism _ (splitMap j (reverseDiagram P₀ x)) =
        splitMap j (reverseDiagram P₀ x)
      have he := congrArg (fun m => splitFrobenius 1 Nat.zero_lt_one m (reverseDiagram P₀ x)) h2
      exact (splitMap_graphField j (reverseDiagram P₀ x)).trans
        (congrArg (splitMap j) ((congrArg (diagramAutomorphism P₀) he).trans (reverse_fixed x)))
  obtain ⟨k,hk,hm,hfix⟩ := hh
  let l := (k.comp (fixedSubgroup P₀).subtype).codRestrict
    (fixedSubgroup (binaryParameters f hf)) hm
  exact ⟨l,fun x y h => Subtype.ext (hk (congrArg Subtype.val h)),
    fun x => hfix x⟩

/-- A literal coefficient action of order dividing seven fixes an elementary
seven-square in the original carrier, including the binary endpoint. -/
theorem exists_fixed_seven_plane (f : ℕ) (hf : 0<f) (hf3 : ¬3∣f)
    (σ : CoefficientAut (binaryParameters f hf)) (hσ : σ^7=1) :
    ∃ E : Subgroup (BinaryCarrier f hf), IsElementaryAbelian 7 E ∧
      Nat.card E=7^2 ∧ E ≤ (coefficientAction _ σ).fixedSubgroup := by
  obtain ⟨k,hk,hfix⟩ := exists_fixed_injection f hf hf3 σ hσ
  let P := binaryParameters f hf
  let j₀ := k.comp BinarySevenPlane.fixedData.embedding
  let j₁ := j₀.codRestrict (elementarySubgroup P)
    (fun x => (elementarySubgroup_eq_top P rfl).ge (mem_top (j₀ x)))
  let j := (toCarrier P).comp j₁
  have hj₁ : Function.Injective j₁ := fun x y hh =>
    (hk.comp BinarySevenPlane.fixedData.embedding_injective) (congrArg Subtype.val hh)
  have hj : Function.Injective j := (ElementaryCentralKernel.toCarrier_injective P rfl).comp hj₁
  let : IsElementaryAbelian 7 (Multiplicative QuaternionSevenPlane.Plane) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      ext <;> simp [show (7 : ZMod 7)=0 from rfl]) }
  let : IsElementaryAbelian 7 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  refine ⟨j.range,inferInstance,?_,?_⟩
  · rw [←Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
    change Nat.card (ZMod 7 × ZMod 7)=7^2
    simp
  · rintro _ ⟨x,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hh : coefficientElementary P σ (j₁ x)=j₁ x :=
      Subtype.ext (Subtype.ext (hfix (BinarySevenPlane.fixedData.embedding x)))
    exact congrArg (toCarrier P) hh

/-- The fixed plane and an outer coefficient actor force seven-rank three
inside the specified automorphism overgroup. -/
theorem field_actor_rank_three (f : ℕ) (hf : 0<f)
    (hf3 : ¬3∣f) (A : Subgroup (MulAut (BinaryCarrier f hf)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier f hf) ≤ A)
    (σ : CoefficientAut (binaryParameters f hf)) (hσ : orderOf σ=7)
    (haA : coefficientAction _ σ∈A) : 3 ≤ primeRank 7 A := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P := binaryParameters f hf
  let a := coefficientAction P σ
  have hout : a ∉ MulAut.innerSubgroup (Carrier P) := by
    intro hh
    have he := (EvenField.NormalForm.coefficientAction_mem_inner_iff f hf σ).mp hh
    have := (Fact.out : Nat.Prime 7).one_lt
    rw [he,orderOf_one] at hσ
    omega
  have ha : orderOf a=7 := orderOf_eq_prime
    (by rw [←map_pow,show σ^7=1 from hσ ▸ pow_orderOf_eq_one σ,map_one])
    (fun hh => hout (hh ▸ (MulAut.innerSubgroup _).one_mem))
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_seven_plane f hf hf3 σ (hσ ▸ pow_orderOf_eq_one σ)
  let := hE
  let j : Carrier P →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hj : Function.Injective j := fun _ _ hh =>
    MulAut.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot f hf) (congrArg Subtype.val hh)
  let B := E.map j
  let : IsElementaryAbelian 7 B := IsElementaryAbelian.map j
  let x : A := ⟨a,haA⟩
  have hx : orderOf x=7 := (orderOf_injective A.subtype A.subtype_injective x).symm.trans ha
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
  have hcB : Nat.card B=7^2 := by rw [card_map_of_injective hj,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB


/-- At base degree prime to three, a rank-two overgroup containing all inner
automorphisms has no outer actor of order seven. -/
theorem seven_actor_inner (f : ℕ) (hf : 0<f)
    [IsSimpleGroup (BinaryCarrier f hf)] [Group.IsPerfect (BinaryCarrier f hf)]
    (hf3 : ¬3∣f)
    (A : Subgroup (MulAut (BinaryCarrier f hf)))
    (hinner : MulAut.innerSubgroup (BinaryCarrier f hf) ≤ A)
    (hrank : primeRank 7 A ≤ 2) (a : MulAut (BinaryCarrier f hf))
    (haA : a∈A) (ha : orderOf a=7) : a ∈ MulAut.innerSubgroup (BinaryCarrier f hf) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
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
  have hh := field_actor_rank_three f hf hf3 A hinner σ hσ hσA
  omega

private theorem prime_divisor_twelve (f : ℕ) (hf : 0<f) {p : ℕ}
    (hp : p.Prime) (hp2 : p≠2)
    (hd : p ∣ Nat.card (BinaryCarrier f hf)) : p ∣ 2^(12*f)-1 := by
  let : Fact p.Prime := ⟨hp⟩
  let q := 2^f
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
  have hq3 : 1 ≤ q^3 := Nat.one_le_pow _ _ hq
  have hq12 : 1 ≤ q^12 := Nat.one_le_pow _ _ hq
  have htwo : (2 : ZMod p)≠0 := by
    intro hh
    have h := (ZMod.natCast_eq_zero_iff 2 p).mp hh
    exact hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp.ne_one)
  have hqne : (q : ZMod p)≠0 := by simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using pow_ne_zero f htwo
  rw [ConcreteBruhat.FixedCellCount.card_carrier,ConcreteBruhat.FixedCellCount.card_borel] at hd
  change p ∣ q^12*((q^3-1)*(q-1))*((q^3+1)*(q+1)*(q^8+q^4+1)) at hd
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast [Nat.cast_sub hq,Nat.cast_sub hq3] at hz
  have hpw : (q : ZMod p)^12=1 := by
    rcases mul_eq_zero.mp hz with hh | hh
    · rcases mul_eq_zero.mp hh with hh | hh
      · exact (pow_ne_zero 12 hqne hh).elim
      · rcases mul_eq_zero.mp hh with hh | hh
        · have h3 := sub_eq_zero.mp hh
          calc
            _ = ((q : ZMod p)^3)^4 := by ring
            _ = 1 := by rw [h3,one_pow]
        · rw [sub_eq_zero.mp hh,one_pow]
    · rcases mul_eq_zero.mp hh with hh | hh
      · rcases mul_eq_zero.mp hh with hh | hh
        · have h3 := add_eq_zero_iff_eq_neg.mp hh
          calc
            _ = ((q : ZMod p)^3)^4 := by ring
            _ = 1 := by rw [h3]; norm_num
        · rw [add_eq_zero_iff_eq_neg.mp hh]; norm_num
      · linear_combination ((q : ZMod p)^4-1)*hh
  have hd' : p ∣ q^12-1 := (ZMod.natCast_eq_zero_iff _ p).mp (by
    push_cast [Nat.cast_sub hq12]
    exact sub_eq_zero.mpr hpw)
  simpa only [q,←pow_mul,Nat.mul_comm f 12] using hd'
/-- The actual carrier order and coprime odd source degree leave only seven
as a common prime. No rank or field-action hypothesis is assumed. -/
theorem prime_eq_seven {n f p : ℕ} (hf : 0<f) (hp : p.Prime) (hp2 : p≠2)
    (hn : Odd n) (hc : Nat.Coprime n f) (hd : p∣2^n-1)
    (hcard : p∣Nat.card (BinaryCarrier f hf)) : p=7 :=
  prime_seven_of_exponents hp hn hc hd (prime_divisor_twelve f hf hp hp2 hcard)

end Triality.Standard.OddDegreeFieldActors
