module

public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Index


/-!
# Images of prime-set residuals in finite groups

The quotient by the intersection of normal subgroups with π-group quotient
embeds into the finite product of those quotients. It is therefore a π-group.
Consequently surjections preserve π-residuals. The final transport theorem
uses the literal subtype maps and needs no ambient normality of a subgroup.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.18, printed p.931. Here O^{2,3} is the residual for {2,3}-group quotients,
as in the prime-set convention of A.1.26, rather than a prime-set core.
-/

@[expose] public section

open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

instance piResidual_normal (π : Set Nat.Primes) : (piResidual π G).Normal where
  conj_mem x hx g := by
    apply mem_sInf.mpr
    rintro N ⟨hN, hpi⟩
    exact hN.conj_mem x (mem_sInf.mp hx N ⟨hN, hpi⟩) g

private theorem piGroup_dependent_product {ι : Type*} [Finite ι]
    {K : ι → Type*} [∀ i, Group (K i)] [∀ i, Finite (K i)]
    (π : Set Nat.Primes) (h : ∀ i, IsPiGroup π (K i)) :
    IsPiGroup π (∀ i, K i) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [IsPiGroup_iff]
  intro p hp
  rw [Nat.card_pi] at hp
  obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp p.property) _).mp hp
  exact (IsPiGroup_iff _ _).mp (h i) p hi

theorem isPiGroup_quotient_piResidual (π : Set Nat.Primes) :
    IsPiGroup π (G ⧸ piResidual π G) := by
  classical
  let _ : Finite (Subgroup G) :=
    Finite.of_injective (fun N : Subgroup G => (N : Set G)) SetLike.coe_injective
  let S := {N : Subgroup G // ∃ hN : N.Normal,
    @IsPiGroup π (G ⧸ N) (@QuotientGroup.Quotient.group G _ N hN)}
  let _ (N : S) : N.val.Normal := N.property.choose
  let q : G →* ((N : S) → G ⧸ N.val) :=
    MonoidHom.pi fun N => QuotientGroup.mk' N.val
  have hp : IsPiGroup π ((N : S) → G ⧸ N.val) :=
    piGroup_dependent_product π fun N => N.property.choose_spec
  have hk : q.ker = piResidual π G := by
    ext x
    rw [MonoidHom.mem_ker, funext_iff]
    change (∀ N : S, QuotientGroup.mk' N.val x = 1) ↔ x ∈ piResidual π G
    simp only [piResidual, mem_sInf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h N hN => h ⟨N, hN⟩, fun h N => h N.val N.property⟩
  have hker : IsPiGroup π (G ⧸ q.ker) :=
    hp.of_injective (QuotientGroup.kerLift q) (QuotientGroup.kerLift_injective q)
  exact hker.of_equiv (QuotientGroup.quotientMulEquivOfEq hk).symm

theorem map_piResidual_of_surjective (π : Set Nat.Primes) (f : G →* H)
    (hf : Function.Surjective f) : (piResidual π G).map f = piResidual π H := by
  apply le_antisymm (map_piResidual_le π f)
  let N := (piResidual π G).map f
  let _ : N.Normal := Normal.map inferInstance f hf
  have hle : piResidual π G ≤ N.comap f := le_comap_map f _
  have hsurj := QuotientGroup.map_surjective_of_surjective (piResidual π G) N f
    (QuotientGroup.mk_surjective.comp hf) hle
  exact sInf_le ⟨inferInstance, (isPiGroup_quotient_piResidual π).of_surjective
    (QuotientGroup.map (piResidual π G) N f hle) hsurj⟩

theorem map_embedded_piResidual (π : Set Nat.Primes) (M : Subgroup G) (f : G →* H) :
    ((piResidual π M).map M.subtype).map f =
      (piResidual π (M.map f)).map (M.map f).subtype := by
  calc
    _ = ((piResidual π M).map (f.subgroupMap M)).map (M.map f).subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by
      rw [map_piResidual_of_surjective π (f.subgroupMap M) (f.subgroupMap_surjective M)]
end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- A π-group bound on the image of O² suffices when 2 belongs to π. -/
theorem piResidual_le_ker_of_twoResidual_image (π : Set Nat.Primes)
    (h2 : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ π)
    (f : G →* H) (D : Subgroup H) (hD : IsPiGroup π D)
    (himage : (pResidual 2 G).map f ≤ D) : piResidual π G ≤ f.ker := by
  let R := pResidual 2 f.range
  have hr : (pResidual 2 G).map f.rangeRestrict = R :=
    map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective
  have hRD : R.map f.range.subtype ≤ D := by
    rw [← hr, map_map]
    exact himage
  let i : R →* D := {
    toFun x := ⟨x.val.val, hRD (mem_map_of_mem f.range.subtype x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y he
    have hv : (x.val.val : H) = y.val.val := congrArg (fun z : D => (z : H)) he
    exact Subtype.ext (Subtype.ext hv)
  have hR : IsPiGroup π R := hD.of_injective i hi
  have hQ : IsPiGroup π (f.range ⧸ R) := by
    apply (IsPiGroup_iff _ _).mpr
    intro p hp
    obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := f.range) 2).exists_card_eq
    have hp2 : p.val = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow (hn ▸ hp))).resolve_left p.property.ne_one
    have he : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    exact he.symm ▸ h2
  have hrange := IsPiGroup.of_normal_subgroup_and_quotient R (hR.isPiSubgroup R) hQ
  exact piResidual_le_ker_of_range π f hrange
end Subgroup

