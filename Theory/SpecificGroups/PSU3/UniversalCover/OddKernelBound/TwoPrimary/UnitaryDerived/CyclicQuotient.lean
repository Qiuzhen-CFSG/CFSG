module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.TwoPrimary.LocalTransfer

/-!
# Central two-kernels over a cyclic quotient

Suppose a finite group B maps to a cyclic group and its kernel L has odd
abelianization. If every finite central two-extension of L has trivial
derived kernel, the same holds for B, without assuming either group perfect.

For a central two-extension f : D → B, put M = f⁻¹(L) and let n be the odd
order of L/L′. Inside M, the subgroup H defined by xⁿ ∈ M′ is the kernel of
the n-th power map on M/M′. Its displayed description makes H normal in D.
Surjectivity onto L′ and invertibility of odd powers on the two-kernel give
M = ker(f) H. Thus D/H is a central extension of a cyclic group and is
abelian. Now D′ lies in H, while H meets ker(f) trivially by the local
calculation and oddness of n.

The application in `UnitaryDerived` takes the literal determinant on GU₂.
This is the cyclic-quotient step in the local calculation supporting the
PSU₃ multiplier exclusions quoted in Aschbacher--Smith I.1.3--4 and GLS3 §6.1.
-/

open Subgroup
namespace PerfectCentralCovering
universe u v w

/-- Derived-kernel vanishing passes from the kernel of a cyclic quotient to the
whole group when that kernel has odd abelianization. -/
public theorem twoKernelDerivedTrivial_of_cyclic_quotient {B : Type v} {C : Type w}
    [Group B] [Finite B] [Group C] [IsCyclic C]
    (d : B →* C) (ho : Odd (Nat.card (Abelianization d.ker)))
    (hl : TwoKernelDerivedTrivial.{u, v} d.ker) :
    TwoKernelDerivedTrivial.{u, v} B := by
  intro D _ _ f hf hc hk
  let M := d.ker.comap f
  let q : M →* d.ker := f.subgroupComap d.ker
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  have hqk {x : M} (hx : x ∈ q.ker) : (x : D) ∈ f.ker :=
    congrArg Subtype.val hx
  have hqc : q.ker ≤ center M := fun x hx =>
    mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc (hqk hx)) y)
  let k : q.ker →* f.ker := (M.subtype.comp q.ker.subtype).codRestrict f.ker
    (fun x => hqk x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : D)) h
  have hkp : IsPGroup 2 q.ker := hk.of_injective k hki
  have hdis := hl q hq hqc hkp
  let n := Nat.card (Abelianization d.ker)
  let a : M →* Abelianization M := (powMonoidHom n).comp Abelianization.of
  let H : Subgroup D := a.ker.map M.subtype
  have hmem (x : D) : x ∈ H ↔ x ∈ M ∧ x ^ n ∈ ⁅M, M⁆ := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rw [← map_subtype_commutator]
      refine ⟨y ^ n, ?_, rfl⟩
      rw [← Abelianization.ker_of]
      change Abelianization.of (y ^ n) = 1
      rw [map_pow]
      exact hy
    · rintro ⟨hx, hxn⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [← map_subtype_commutator] at hxn
      obtain ⟨y, hy, he⟩ := hxn
      have hey : y = (⟨x, hx⟩ : M) ^ n := Subtype.ext he
      change Abelianization.of (⟨x, hx⟩ : M) ^ n = 1
      rw [← map_pow, ← hey]
      exact (show y ∈ Abelianization.of.ker by rwa [Abelianization.ker_of])
  let : H.Normal := ⟨fun x hx g => by
    obtain ⟨hm, hn⟩ := (hmem x).mp hx
    apply (hmem _).mpr
    refine ⟨(inferInstance : M.Normal).conj_mem x hm g, ?_⟩
    rw [conj_pow]
    exact (inferInstance : (⁅M, M⁆).Normal).conj_mem _ hn g⟩
  have hHM : H ≤ M := fun x hx => ((hmem x).mp hx).1
  have hfactor (x : M) : ∃ z : q.ker, a z = a x := by
    have hp : q (x ^ n) ∈ _root_.commutator d.ker := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_pow, map_pow]
      exact pow_card_eq_one' (x := Abelianization.of (q x))
    have hmap : (_root_.commutator M).map q = _root_.commutator d.ker := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq]
      rfl
    obtain ⟨t, ht, he⟩ := hmap ▸ hp
    let z : q.ker := ⟨x ^ n * t⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]⟩
    let y := (hkp.powEquiv (Nat.coprime_two_left.mpr ho)).symm z
    have hy : y ^ n = z := (hkp.powEquiv (Nat.coprime_two_left.mpr ho)).apply_symm_apply z
    refine ⟨y, ?_⟩
    change Abelianization.of (y : M) ^ n = Abelianization.of x ^ n
    rw [← map_pow]
    have hey : (y : M) ^ n = x ^ n * t⁻¹ := congrArg Subtype.val hy
    rw [hey, map_mul, map_inv]
    have ht1 : Abelianization.of t = 1 := by
      change t ∈ Abelianization.of.ker
      rwa [Abelianization.ker_of]
    rw [ht1, inv_one, mul_one, map_pow]
  let π := QuotientGroup.mk' H
  let δ : D ⧸ H →* C := QuotientGroup.lift H (d.comp f) (fun x hx => hHM hx)
  have hδ : δ.ker ≤ center (D ⧸ H) := by
    intro x
    induction x using QuotientGroup.induction_on with | H x =>
      intro hx
      have hxm : x ∈ M := hx
      obtain ⟨z, hz⟩ := hfactor ⟨x, hxm⟩
      have hsame : π ((z : M) : D) = π x := by
        apply eq_of_div_eq_one
        rw [← map_div]
        change ((z : M) : D) / x ∈ π.ker
        rw [QuotientGroup.ker_mk']
        refine ⟨(z : M) / ⟨x, hxm⟩, ?_, rfl⟩
        change a ((z : M) / ⟨x, hxm⟩) = 1
        rw [map_div, hz]
        exact div_self' _
      change π x ∈ center (D ⧸ H)
      rw [← hsame]
      exact Subgroup.mem_center_iff.mpr fun y => by
        induction y using QuotientGroup.induction_on with | H y =>
          exact congrArg π (mem_center_iff.mp (hc (hqk z.property)) y)
  let : IsMulCommutative (D ⧸ H) :=
    δ.isMulCommutative_of_isCyclic_of_ker_le_center hδ
  have hder : _root_.commutator D ≤ H := by
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  apply (f.ker ⊓ _root_.commutator D).eq_bot_iff_forall.mpr
  intro x hx
  have hxH := (hmem x).mp (hder hx.2)
  have hxM : x ∈ M := hxH.1
  have hxn : (⟨x, hxM⟩ : M) ^ n ∈ _root_.commutator M := by
    rw [← map_subtype_commutator] at hxH
    obtain ⟨y, hy, he⟩ := hxH.2
    exact (show y = (⟨x, hxM⟩ : M) ^ n from Subtype.ext he) ▸ hy
  have hxq : (⟨x, hxM⟩ : M) ∈ q.ker := Subtype.ext hx.1
  have hxpow : (⟨x, hxM⟩ : M) ^ n = 1 := by
    apply mem_bot.mp
    rw [← hdis]
    exact ⟨pow_mem hxq n, hxn⟩
  have hxpow' : (⟨x, hx.1⟩ : f.ker) ^ n = 1 :=
    Subtype.ext (congrArg (fun z : M => (z : D)) hxpow)
  have he : (⟨x, hx.1⟩ : f.ker) = 1 := by
    apply (hk.powEquiv (Nat.coprime_two_left.mpr ho)).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hxpow'
  exact congrArg Subtype.val he
end PerfectCentralCovering
