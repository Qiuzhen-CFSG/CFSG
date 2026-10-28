module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Hyperplanes
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.SpecificGroups.AlternatingSix.M10.SolvableResidual

/-!
# The literal M₁₀ obstructions in J.2.7(5--6)

The quotient in this file is the actual quotient by the cubic kernel.  The
order-45 argument is made before identifying the odd core with a five-core:
only the hypothetical odd complement is transported into the centralizer of
`z`.  Odd subgroups of the actual M₁₀ lie in its specified inner A₆, where the
small-index calculation excludes orders 15 and 45.

The solvable residual calculation uses the same quotient and the actual
inner-A₆ residual.  Its kernel has order dividing the literal cubic kernel,
so its Sylow five-subgroups have order five.

Source: Aschbacher--Smith, J.2.7(5--6), printed pp.435--436 (PDF pp.446--447).
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d)

private instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem factorization_360_five : Nat.factorization 360 5 = 1 := by
  have hzero : padicValNat 5 72 = 0 := by norm_num
  rw [Nat.factorization_def 360 Nat.prime_five,
    show (360 : Nat) = 5 ^ 1 * 72 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]

private theorem factorization_1080_five : Nat.factorization 1080 5 = 1 := by
  have hzero : padicValNat 5 216 = 0 := by norm_num
  rw [Nat.factorization_def 1080 Nat.prime_five,
    show (1080 : Nat) = 5 ^ 1 * 216 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]

private theorem card_source_eq_card_range_mul_card_ker
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

private theorem odd_subgroup_le_inner
    (Q : Subgroup AlternatingSix.M10.extension)
    (hodd : Odd (Nat.card Q)) :
    Q ≤ AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension := by
  intro x hx
  let q := QuotientGroup.mk'
    (AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension)
  have htwo : (q x : AlternatingSix.M10.extension ⧸
      AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := q x)
    change q x ^ (AlternatingSix.ShadowLocal.inner.subgroupOf
      AlternatingSix.M10.extension).index = 1 at h
    rwa [AlternatingSix.M10.innerInExtension_index] at h
  have hoddpow : (q x) ^ Nat.card Q = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : Q))
    change q ((⟨x, hx⟩ : Q) : AlternatingSix.M10.extension) ^ Nat.card Q = 1
    rw [← map_pow]
    exact congrArg (fun y : Q => q (y : AlternatingSix.M10.extension)) h
  have hq : q x = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have hdiv : orderOf (q x) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one htwo
    have hdivodd : orderOf (q x) ∣ Nat.card Q :=
      orderOf_dvd_of_pow_eq_one hoddpow
    have hc : (Nat.card Q).Coprime 2 :=
      (Nat.coprime_two_left.mpr ⟨k, hk⟩).symm
    have hgcd : orderOf (q x) ∣ Nat.gcd 2 (Nat.card Q) :=
      Nat.dvd_gcd hdiv hdivodd
    have hone : orderOf (q x) ∣ 1 := by
      rw [hc.symm.gcd_eq_one] at hgcd
      exact hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  exact (QuotientGroup.eq_one_iff x).mp hq

private theorem no_inner_subgroup_card
    (Q : Subgroup AlternatingSix.M10.extension)
    (hodd : Odd (Nat.card Q))
    (hcard : Nat.card Q = 15 ∨ Nat.card Q = 45) : False := by
  have hle := odd_subgroup_le_inner Q hodd
  let I := AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension
  let H := (Q.subgroupOf I).map
      AlternatingSix.M10.innerInExtensionEquiv.toMonoidHom
  have hHcard : Nat.card H = Nat.card Q := by
    rw [Subgroup.card_map_of_injective
      AlternatingSix.M10.innerInExtensionEquiv.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hproper : H ≠ ⊤ := by
    intro htop
    have hQtop : Nat.card Q = 360 := by
      rw [← hHcard, htop, card_top, hA6]
    rcases hcard with h15 | h45 <;> omega
  have hidx : H.index ≤ 63 := by
    have hc := H.card_mul_index
    rcases hcard with h15 | h45
    · rw [hHcard, h15, hA6] at hc
      omega
    · rw [hHcard, h45, hA6] at hc
      omega
  have hsmall := AlternatingSix.SmallIndex.index_divisible_by_five_or_six_or_thirtySix
    H hproper hidx
  rcases hcard with h15 | h45
  · have hc := H.card_mul_index
    rw [hHcard, h15, hA6] at hc
    rcases hsmall with h | h | h <;> omega
  · have hc := H.card_mul_index
    rw [hHcard, h45, hA6] at hc
    rcases hsmall with h | h | h <;> omega

/-- No subgroup of the actual centralizer `G_B` has order 45.

The proof passes through the literal cubic quotient.  The possible kernel
orders are one and three, giving quotient orders 45 and 15 respectively;
oddness forces the quotient subgroup into the actual inner A₆ of M₁₀.
-/
theorem no_subgroup_order45
    (hB : Nat.card c.B = 3)
    (e : c.CubicQuotient ≃* AlternatingSix.M10.extension) :
    ∀ P : Subgroup G, P ≤ c.GB → Nat.card P ≠ 45 := by
  intro P hP h45
  let P' := P.subgroupOf c.GB
  let f : c.GB →* c.CubicQuotient := c.cubicQuotientMap
  let r := f.subgroupMap P'
  have hrange : Nat.card r.range = Nat.card (P'.map f) := by
    have ht : r.range = ⊤ := MonoidHom.range_eq_top.mpr
      (MonoidHom.subgroupMap_surjective f P')
    simp only [ht, Subgroup.card_top]
  have hcardP' : Nat.card P' = Nat.card r.range * Nat.card r.ker := by
    simpa only [hrange] using card_source_eq_card_range_mul_card_ker r
  have hPcard : Nat.card P' = 45 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv]
    exact h45
  have hker_le : r.ker.map P'.subtype ≤ c.cubicKernel := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    have hxker : f (P'.subtype x) = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [← c.cubicQuotientMap_ker]
    exact MonoidHom.mem_ker.mpr hxker
  have hker_div : Nat.card r.ker ∣ 3 := by
    let kf : r.ker →* c.cubicKernel :=
      (P'.subtype.comp r.ker.subtype).codRestrict c.cubicKernel (fun x =>
        hker_le (Subgroup.mem_map_of_mem (f := P'.subtype)
          (K := r.ker) x.property))
    have hkf : Function.Injective kf := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : c.cubicKernel => (z : G)) hxy)))
    have hd := Subgroup.card_dvd_of_injective kf hkf
    rw [c.cubicKernel_card hB] at hd
    exact hd
  have hker : Nat.card r.ker = 1 ∨ Nat.card r.ker = 3 :=
    (Nat.dvd_prime (by decide)).mp hker_div
  have hrange_card : Nat.card r.range = 45 ∨ Nat.card r.range = 15 := by
    rcases hker with h1 | h3
    · left
      have hc := hcardP'
      rw [h1] at hc
      omega
    · right
      have hc := hcardP'
      rw [h3] at hc
      omega
  let Q := (r.range.map (P'.map f).subtype).map e.toMonoidHom
  have hQcard : Nat.card Q = 45 ∨ Nat.card Q = 15 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective (P'.map f).subtype_injective]
    exact hrange_card
  have hQodd : Odd (Nat.card Q) := by
    rcases hQcard with h | h <;> rw [h] <;> decide
  rcases hQcard with h45 | h15
  · exact no_inner_subgroup_card Q hQodd (Or.inr h45)
  · exact no_inner_subgroup_card Q hQodd (Or.inl h15)

/-- In the hypothetical order-45 branch, the z-class conjugator sends the
odd core into the literal centralizer `G_B`. -/
theorem order45_conjugate_le_GB
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (_v : FiveInverterData c B5)
    (_h45 : Nat.card (fiveOddPart B5) = 45)
    (hconj : ∃ g : G, (fiveOddPart B5).map
      (MulAut.conj g).toMonoidHom ≤ c.GB) :
    ∃ g : G, (fiveOddPart B5).map (MulAut.conj g).toMonoidHom ≤ c.GB := by
  exact hconj

/-- The order-45 branch is impossible for the literal odd complement. -/
theorem fiveOddPart_card_ne_45
    (hB : Nat.card c.B = 3)
    (e : c.CubicQuotient ≃* AlternatingSix.M10.extension)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (v : FiveInverterData c B5)
    (hconj : ∃ g : G, (fiveOddPart B5).map
      (MulAut.conj g).toMonoidHom ≤ c.GB) :
    Nat.card (fiveOddPart B5) ≠ 45 := by
  intro h45
  obtain ⟨g, hle⟩ := c.order45_conjugate_le_GB B5 v h45 hconj
  have himage : Nat.card ((fiveOddPart B5).map
      (MulAut.conj g).toMonoidHom) = 45 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h45]
  exact c.no_subgroup_order45 hB e _ hle himage

private theorem residual_source_card
    (hB : Nat.card c.B = 3)
    (e : c.CubicQuotient ≃* AlternatingSix.M10.extension) :
    Nat.card (solvableResidual c.GB) = 360 ∨ Nat.card (solvableResidual c.GB) = 1080 := by
  let S := solvableResidual c.GB
  let q : S →* AlternatingSix.M10.extension :=
    e.toMonoidHom.comp (c.cubicQuotientMap.comp S.subtype)
  have hqrange : q.range = AlternatingSix.ShadowLocal.inner.subgroupOf
      AlternatingSix.M10.extension := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx
      have hy' : c.cubicQuotientMap (S.subtype y) ∈
          (solvableResidual c.CubicQuotient : Subgroup c.CubicQuotient) := by
        rw [← map_solvableResidual_eq c.cubicQuotientMap
          c.cubicQuotientMap_surjective]
        exact Subgroup.mem_map_of_mem _ y.property
      have hxres : x ∈ solvableResidual AlternatingSix.M10.extension := by
        rw [← map_solvableResidual_eq e.toMonoidHom e.surjective,
          ← hy]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hy'
      rw [← AlternatingSix.M10.residual_eq_inner]
      exact hxres
    · intro x hx
      have hxres : x ∈ solvableResidual AlternatingSix.M10.extension := by
        rw [AlternatingSix.M10.residual_eq_inner]
        exact hx
      rw [← map_solvableResidual_eq e.toMonoidHom e.surjective] at hxres
      obtain ⟨z, hz, hzmap⟩ := Subgroup.mem_map.mp hxres
      rw [← map_solvableResidual_eq c.cubicQuotientMap
          c.cubicQuotientMap_surjective] at hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      let sy : S := ⟨y, hy⟩
      refine ⟨sy, ?_⟩
      change e.toMonoidHom (c.cubicQuotientMap y) = x
      rw [hyz, hzmap]
  have hqcard : Nat.card q.range = 360 := by
    rw [hqrange, Nat.card_congr AlternatingSix.M10.innerInExtensionEquiv.toEquiv,
      AlternatingSix.ShadowLocal.card_A6]
  have hker_le : q.ker.map S.subtype ≤ c.cubicKernel := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    have hxker : q x = 1 := MonoidHom.mem_ker.mp hx
    rw [← c.cubicQuotientMap_ker]
    exact MonoidHom.mem_ker.mpr (by
      exact e.injective (by simpa [q] using hxker))
  have hker_div : Nat.card q.ker ∣ 3 := by
    let kf : q.ker →* c.cubicKernel :=
      (S.subtype.comp q.ker.subtype).codRestrict c.cubicKernel (fun x =>
        hker_le (Subgroup.mem_map_of_mem (f := S.subtype) (K := q.ker) x.property))
    have hkf : Function.Injective kf := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : c.cubicKernel => (z : G)) hxy)))
    have hd := Subgroup.card_dvd_of_injective kf hkf
    rw [c.cubicKernel_card hB] at hd
    exact hd
  have hker : Nat.card q.ker = 1 ∨ Nat.card q.ker = 3 :=
    (Nat.dvd_prime (by decide)).mp hker_div
  have hsourcecard := card_source_eq_card_range_mul_card_ker q
  rcases hker with h1 | h3
  · left
    rw [hqcard, h1] at hsourcecard
    simpa only [S] using hsourcecard
  · right
    rw [hqcard, h3] at hsourcecard
    simpa only [S] using hsourcecard

/-- Every Sylow five-subgroup of the actual solvable residual `L_B` has
order five.  The quotient map is the literal cubic quotient, and its image
is the actual inner A₆ residual of M₁₀. -/
theorem residual_sylow_five_card
    (hB : Nat.card c.B = 3)
    (e : c.CubicQuotient ≃* AlternatingSix.M10.extension) :
    ∀ S : Sylow 5 c.LB, Nat.card S = 5 := by
  intro S
  have hsource := c.residual_source_card hB e
  have hLBcard : Nat.card c.LB = Nat.card (solvableResidual c.GB) := by
    rw [card_map_of_injective c.GB.subtype_injective]
  have hfac : (Nat.card c.LB).factorization 5 = 1 := by
    rw [hLBcard]
    rcases hsource with h | h
    · rw [h, factorization_360_five]
    · rw [h, factorization_1080_five]
  rw [Sylow.card_eq_multiplicity, hfac]
  decide

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
