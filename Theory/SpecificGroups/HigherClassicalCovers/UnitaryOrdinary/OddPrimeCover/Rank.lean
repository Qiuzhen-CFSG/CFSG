module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
public import Theory.GroupTheory.CentralElementaryRankFour
public import Theory.ElementaryAbelian.Quotient

/-!
# Ordinary defining rank in central covers of PSU₄

The highest, middle and long positive roots form an actual elementary subgroup
of order p⁴: its two trace-zero coordinates each have order p, and its field
coordinate has order p². Matrix entries prove injectivity, and the scalar
projection remains injective because its kernel has order dividing four.

A finite central extension of this elementary subgroup has p-rank at least
three. Passing to its full preimage proves the ordinary-rank conclusion for
every central cover, including the exceptional prime three and all center sizes.
This is an ordinary-rank statement; no local-rank conclusion is inferred.

Source: Aschbacher–Smith I.2.1, printed p.409, the PSU₄(3) branch.
-/

open Matrix Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
open OddFourClosure.DefiningPrime

universe u
variable {F : Type u} [Field F] (J : HermitianForm 4 F)

private def radical : Multiplicative (traceZero J × F × traceZero J) →* HyperbolicSU J where
  toFun x := (matrixRootLifts J).word 0 x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2
  map_one' := (matrixRootLifts J).word_zero
  map_mul' x y := by
    rw [PositiveRootLifts.word_mul]
    have hs : skew J 0 x.toAdd.2.1=0 := Subtype.ext (by simp [skew])
    have hn : normMul J 0 x.toAdd.2.2=0 := Subtype.ext (by simp [normMul])
    simp only [hs,hn,add_zero,neg_zero,zero_mul]
    rfl

private theorem radical_injective : Function.Injective (radical J) := by
  intro x y h
  have hm := congrArg (fun g : HyperbolicSU J => g.val.val) h
  change ((matrixRootLifts J).word 0 x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2).val.val =
    ((matrixRootLifts J).word 0 y.toAdd.1 y.toAdd.2.1 y.toAdd.2.2).val.val at hm
  rw [word_matrix,word_matrix] at hm
  change x.toAdd=y.toAdd
  apply Prod.ext
  · apply Subtype.ext
    simpa using congrArg (fun M => M 0 2) hm
  · apply Prod.ext
    · simpa using congrArg (fun M => M 0 3) hm
    · exact Subtype.ext (congrArg (fun M => M 1 3) hm)

public theorem exists_elementary_four_embedding [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p) :
    ∃ (V : Type u) (_ : Group V) (_ : Finite V) (_ : IsElementaryAbelian p V),
      Nat.card V=p^4 ∧ ∃ v : V →* ProjectiveSpecialUnitaryMatrixGroup J,
        Function.Injective v := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f:=2)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let V := Multiplicative (traceZero J × F × traceZero J)
  let : IsElementaryAbelian p V := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      change p • x.toAdd=0
      ext <;> simp [nsmul_eq_mul] }
  have hV : Nat.card V=p^4 := by
    change Nat.card (traceZero J × F × traceZero J)=p^4
    rw [Nat.card_prod,Nat.card_prod,card_traceZero J hp hcard hconj,hcard]
    ring
  refine ⟨V,inferInstance,inferInstance,inferInstance,hV,?_⟩
  obtain ⟨e⟩ := exists_hyperbolic_special_equiv J hp hcard hconj
  let g : HyperbolicSU J →* ProjectiveSpecialUnitaryMatrixGroup J :=
    (project J).comp e.toMonoidHom
  have hkg : Nat.card g.ker=Nat.gcd 4 (p+1) := by
    rw [Nat.card_congr (Theory.GroupTheory.Covering.kerMulEquivOfSquare g
      (project J) e (MulEquiv.refl _) (fun _ => rfl)).toEquiv]
    exact card_project_kernel J hconj hcard
  have hcop : Nat.Coprime p (Nat.card g.ker) := by
    rw [hkg]
    apply (hp.coprime_iff_not_dvd).mpr
    intro hh
    have hd4 : p ∣ 2^2 := hh.trans (Nat.gcd_dvd_left 4 (p+1))
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd4))
  let u : V →* positive J := (radical J).codRestrict (positive J) (fun x =>
    (mem_positive_iff J _).mpr ⟨0,x.toAdd.1,x.toAdd.2.1,x.toAdd.2.2,rfl⟩)
  have hu : Function.Injective u := fun x y hh => radical_injective J (congrArg Subtype.val hh)
  have hg : Function.Injective (g.comp (positive J).subtype) :=
    injective_comp_subtype_of_coprime_ker g hcop (positive J)
      (positiveSylow J hp hcard hconj).isPGroup'
  exact ⟨(g.comp (positive J).subtype).comp u,hg.comp hu⟩

public theorem three_le_primeRank_of_central_cover [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (f : E →* ProjectiveSpecialUnitaryMatrixGroup J)
    (hf : Function.Surjective f) (hc : f.ker ≤ center E) :
    3 ≤ primeRank p E := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨V,hG,hfin,hA,hV,v,hv⟩ := exists_elementary_four_embedding J hp hp2 hcard hconj
  let := hG
  let := hfin
  let := hA
  let P := v.range.comap f
  let q : P →* v.range := f.subgroupComap v.range
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have hqc : q.ker ≤ center P := by
    intro x hx
    have hh : (x:E) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hh) y))
  let : IsElementaryAbelian p v.range :=
    IsElementaryAbelian.of_surjective v.rangeRestrict v.rangeRestrict_surjective
  let : Finite v.range := Finite.of_surjective v.rangeRestrict v.rangeRestrict_surjective
  have hvc : p^4 ≤ Nat.card v.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hv).toEquiv,hV]
  have hr := CentralExtension.three_le_primeRank_of_elementary_quotient q hq hqc hp2 hvc
  exact hr.trans (primeRank_subgroup_le p P)

public theorem three_le_primeRank_of_quotient_equiv [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (e : E ⧸ center E ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    3 ≤ primeRank p E := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  apply three_le_primeRank_of_central_cover J hp hp2 hcard hconj f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
