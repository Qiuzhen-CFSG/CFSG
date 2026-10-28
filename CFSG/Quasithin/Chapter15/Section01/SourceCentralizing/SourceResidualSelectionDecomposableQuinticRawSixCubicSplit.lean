module
public import Theory.GroupTheory.SymmetricThreeCentralKernel
public import Theory.GroupTheory.SylowNormalGenerationFrattini
public import Theory.GroupTheory.PResidual.PerfectCover
-- Reuse only the elementary central Sylow transfer calculation.
import all Theory.GroupTheory.SymmetricThreeCentralKernel

/-!
# Canonical parabolics through the cubic center

The three-residual of a central three-extension of S₄ maps isomorphically
onto S₄. This uses the abelian Sylow-three preimage and central transfer;
it does not assume that the full extension splits or has exponent three.
The subgroup is canonical, so normalizing the full preimage also normalizes
this complement. The intended source preimages lie in the same original L.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
namespace RawSixCubicSplit
variable {X : Type*} [Group X] [Finite X]

private theorem symmetric_four_three_perfect : IsPPerfect 3 (Equiv.Perm (Fin 4)) := by
  apply (pResidual_eq_top_iff 3 _).mp
  apply top_unique
  rw [←symmetric_involutions_generate (Fin 4), closure_le]
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  exact (Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one hx)
    (by decide : Nat.Coprime 2 3)).symm

private theorem faithful_three_perfect_cover
    (f : X →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center X) (hp : IsPGroup 3 f.ker)
    (hX : IsPPerfect 3 X) : f.ker = ⊥ := by
  let P : Sylow 3 X := Sylow.nonempty.some
  let Q := P.mapSurjective hf
  have hcard : Nat.card Q = 3 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    change 3 ^ (24 : ℕ).factorization 3 = 3
    have h24 := congrArg (fun t : ℕ →₀ ℕ => t 3)
      (Nat.factorization_mul (by decide : (8 : ℕ) ≠ 0) (by decide : (3 : ℕ) ≠ 0))
    change (24 : ℕ).factorization 3 = (8 : ℕ).factorization 3 + (3 : ℕ).factorization 3 at h24
    rw [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ (3 : ℕ) ∣ 8),
      Nat.Prime.factorization_self Nat.prime_three, zero_add] at h24
    rw [h24, pow_one]
  let : IsCyclic Q := isCyclic_of_prime_card hcard
  let B := (Q : Subgroup (Equiv.Perm (Fin 4))).comap f
  let g : B →* Q := f.subgroupComap Q
  have hgc : g.ker ≤ center B := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (hc (congrArg Subtype.val hx)) y)
  let : IsMulCommutative B := g.isMulCommutative_of_isCyclic_of_ker_le_center hgc
  have hPB : (P : Subgroup X) ≤ B := fun x hx => mem_map_of_mem f hx
  exact SymmetricThreeCentralKernel.ker_eq_bot_of_abelian_sylow f hc hp hX P
    (.of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hPB ha) (hPB hb))

/-- The canonical three-residual splits the full central three-kernel over
S₄. The map is the restriction of the given quotient map. -/
theorem residual_bijective
    (f : X →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center X) (hp : IsPGroup 3 f.ker) :
    Function.Bijective (f.comp (pResidual 3 X).subtype) := by
  let R := pResidual 3 X
  let g := f.comp R.subtype
  have hmap : R.map f = ⊤ := by
    rw [map_pResidual_of_surjective 3 f hf,
      (pResidual_eq_top_iff 3 _).mpr symmetric_four_three_perfect]
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hx,hxy⟩ := show y ∈ R.map f by rw [hmap]; trivial
    exact ⟨⟨x,hx⟩,hxy⟩
  have hgc : g.ker ≤ center R := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hx) y)
  have hgp : IsPGroup 3 g.ker := hp.comap_of_injective R.subtype R.subtype_injective
  exact ⟨(MonoidHom.ker_eq_bot_iff g).mp
      (faithful_three_perfect_cover g hg hgc hgp (isPPerfect_pResidual 3)),hg⟩

/-- Lifting the canonical complement through the original normal two-group
retains exactly that two-group as the kernel, with no Sylow assumption. -/
theorem residual_full_two_kernel (N : Subgroup X) [N.Normal]
    (hN : IsPGroup 2 N) (f : (X ⧸ N) →* Equiv.Perm (Fin 4))
    (hf : Function.Surjective f) (hc : f.ker ≤ center (X ⧸ N))
    (hp : IsPGroup 3 f.ker) :
    N ≤ pResidual 3 X ∧
      Function.Surjective ((f.comp (QuotientGroup.mk' N)).comp (pResidual 3 X).subtype) ∧
      ((f.comp (QuotientGroup.mk' N)).comp (pResidual 3 X).subtype).ker =
        N.subgroupOf (pResidual 3 X) := by
  let q := QuotientGroup.mk' N
  let R := pResidual 3 X
  let D := pResidual 3 (X ⧸ N)
  have hNR : N ≤ R := by
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    have hh := hN.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x,hx⟩ : N)
    rw [←orderOf_coe] at hh
    exact hh.symm
  have hmap : R.map q = D := map_pResidual_of_surjective 3 q (QuotientGroup.mk'_surjective N)
  let r : R →* D := (q.comp R.subtype).codRestrict D (by
    intro x
    exact hmap ▸ mem_map_of_mem q x.property)
  have hr (x : R) : (r x : X ⧸ N) = q x := rfl
  have hrs : Function.Surjective r := by
    intro y
    obtain ⟨x,hx,hxy⟩ := show (y : X ⧸ N) ∈ R.map q by rw [hmap]; exact y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hsplit := residual_bijective f hf hc hp
  refine ⟨hNR,hsplit.2.comp hrs,?_⟩
  ext x
  change f (q x) = 1 ↔ (x : X) ∈ N
  constructor
  · intro hx
    have hy : r x = 1 := hsplit.1 (by
      change f (r x) = f 1
      rw [hr,map_one]
      exact hx)
    exact (QuotientGroup.eq_one_iff (x : X)).mp (congrArg Subtype.val hy)
  · intro hx
    have hqx : q (x : X) = 1 := (QuotientGroup.eq_one_iff (x : X)).mpr hx
    rw [hqx,map_one]

end RawSixCubicSplit
end CFSG.Quasithin.Chapter15.Section01
