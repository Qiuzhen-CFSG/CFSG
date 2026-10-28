module
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Components
public import Theory.Representation.BinaryOffender.Defs
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.Rank

/-!
# The cubic centralizer in the offender-generated outer A₆ configuration

The original commuting factors form a normal A₆ × C₃ subgroup with cyclic
quotient. Images of the elementary two-subgroups generating the offender
group have square one in this quotient, so its order divides two. The
specified outer action on the cubic factor makes its centralizer proper;
therefore that centralizer is exactly the factor product. The established
two-rank of A₆ and the odd order of C₃ give two-rank at most two.

The generation input is the literal `offenderSubgroup σ = ⊤` equation;
no extra extension order or module splitting is assumed. This is the group
bound used in the outer alternative of Aschbacher–Smith B.5.13, printed p.110.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.OuterSixThreeShape
variable {D : Type*} [Group D] [Finite D] (c : OuterSixThreeShape D)
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable (σ : Representation (ZMod 2) D W)

omit [Finite D] in
private theorem cyclic_quotient_card_dvd_two
    (hgen : offenderSubgroup σ = ⊤) (N : Subgroup D) [N.Normal]
    [IsCyclic (D ⧸ N)] : Nat.card (D ⧸ N) ∣ 2 := by
  let : CommGroup (D ⧸ N) := IsCyclic.commGroup
  let q := QuotientGroup.mk' N
  let f : D →* D ⧸ N := (powMonoidHom 2).comp q
  have hf : f.ker = ⊤ := by
    apply top_unique
    rw [← hgen]
    unfold offenderSubgroup generatedBy
    refine iSup_le fun A => iSup_le fun hA => ?_
    let : IsElementaryAbelian 2 A := hA.1.1.2
    intro a ha
    change q a ^ 2 = 1
    rw [← map_pow]
    have hs : a ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a,ha⟩)
    rw [hs,map_one]
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N x
  exact (show a ∈ f.ker from hf.symm ▸ mem_top a)

omit [Finite D] in
/-- Offender generation bounds the original cyclic factor quotient by two. -/
theorem factors_index_dvd_two (hgen : offenderSubgroup σ = ⊤) :
    (c.first ⊔ c.second).index ∣ 2 := by
  let := c.first_normal
  let := c.second_normal
  let N := c.first ⊔ c.second
  let q := QuotientGroup.mk' N
  have hz : (zpowers c.element).map q = ⊤ := by
    have he := congrArg (map q) c.generates
    change map q (N ⊔ zpowers c.element) = map q ⊤ at he
    simpa only [Subgroup.map_sup,q,QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using he
  let f := q.comp (zpowers c.element).subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    simpa only [f,MonoidHom.range_comp,range_subtype] using hz
  let : IsCyclic (D ⧸ N) := isCyclic_of_surjective f hf
  exact cyclic_quotient_card_dvd_two σ hgen N

omit [Finite D] in
/-- The cubic centralizer is exactly the original A₆ × C₃ subgroup. -/
theorem second_centralizer_eq_factors (hgen : offenderSubgroup σ = ⊤) :
    centralizer (c.second : Set D) = c.first ⊔ c.second := by
  let : IsCyclic c.second := c.secondEquiv.isCyclic.mpr inferInstance
  have hNC : c.first ⊔ c.second ≤ centralizer (c.second : Set D) :=
    sup_le (fun a ha => mem_centralizer_iff.mpr fun b hb =>
      (c.first_second_commute ⟨a,ha⟩ ⟨b,hb⟩).symm) (le_centralizer c.second)
  have hproper : centralizer (c.second : Set D) ≠ ⊤ := by
    intro hc
    obtain ⟨α,hα,houter⟩ := c.secondOuter
    have ht : c.element ∈ centralizer (c.second : Set D) := hc.symm ▸ mem_top _
    apply houter
    refine ⟨1,?_⟩
    ext a
    simp only [map_one, MulAut.one_apply]
    rw [hα]
    have hh := ht (a : D) a.property
    rw [← hh,mul_inv_cancel_right]
  have hni := c.factors_index_dvd_two σ hgen
  have hcindex : (centralizer (c.second : Set D)).index = 2 := by
    exact (Nat.dvd_prime Nat.prime_two).mp ((index_dvd_of_le hNC).trans hni)
      |>.resolve_left (fun he => hproper (index_eq_one.mp he))
  have hnindex : (c.first ⊔ c.second).index = 2 := by
    exact (Nat.dvd_prime Nat.prime_two).mp hni
      |>.resolve_left (fun he => hproper (top_unique ((index_eq_one.mp he) ▸ hNC)))
  have hrel := relIndex_mul_index hNC
  rw [hcindex,hnindex] at hrel
  have hh : (c.first ⊔ c.second).relIndex (centralizer (c.second : Set D)) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hh) hNC

private theorem second_twoRank_eq_zero : primeRank 2 c.second = 0 := by
  have hp : IsPGroup 3 c.second := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    simp)
  apply Nat.eq_zero_of_le_zero
  apply (_root_.primeRank_le_iff 2 0).mpr
  intro A hA _
  have hd := hA.disjoint_of_coprime (hp.to_subgroup (⊤ : Subgroup c.second))
    (by decide : Nat.Coprime 2 3)
  have ha : A = ⊥ := by simpa using hd
  subst A
  simp [Group.rank_eq_zero]

/-- The actual factor product has two-rank exactly two. -/
theorem factors_twoRank_eq_two : primeRank 2 (c.first ⊔ c.second : Subgroup D) = 2 := by
  rw [← primeRank_equiv 2 c.product,primeRank_prod_eq_add,
    primeRank_equiv 2 c.firstEquiv,c.second_twoRank_eq_zero,add_zero]
  exact (GLS3.Chapter5.PRank.alternating_hasPRank_two 6).primeRank_eq Nat.prime_two

/-- The cubic centralizer has two-rank at most two under offender generation. -/
theorem second_centralizer_twoRank_le (hgen : offenderSubgroup σ = ⊤) :
    primeRank 2 (centralizer (c.second : Set D)) ≤ 2 := by
  rw [c.second_centralizer_eq_factors σ hgen,c.factors_twoRank_eq_two]

end CFSG.Quasithin.ChapterB.OuterSixThreeShape
