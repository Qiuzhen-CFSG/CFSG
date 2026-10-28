module

public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# A factor normalizer inside the normalizer of a commuting product

For a finite commuting family generating a group, restrict the specified
Sylow subgroup to each factor. Its intrinsic normalizer embeds in the
normalizer of the original Sylow subgroup. Lift that subgroup through the
surjective multiplication map. A Sylow subgroup of the product is the
product of its coordinate images, so single-coordinate normalizer elements
normalize the lifted Sylow. This does not require disjoint factors.

Source: the component-product Borel calculation in Aschbacher–Smith,
`refs/quasithin.pdf`, printed p.1144, proof of 15.3.49(k).
-/

public section

open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]

private theorem mem_pi_sylow_iff (K : ι → Type*) [∀ i, Group (K i)]
    [∀ i, Finite (K i)] (Q : Sylow p (∀ i, K i)) (x : ∀ i, K i) :
    x ∈ Q ↔ ∀ i, x i ∈ Q.map (Pi.evalMonoidHom K i) := by
  let R : Subgroup (∀ i, K i) := Subgroup.pi Set.univ
    (fun i => Q.map (Pi.evalMonoidHom K i))
  have hp : IsPGroup p R := by
    intro y
    choose n hn using fun i =>
      (Q.mapSurjective (Function.surjective_eval i)).isPGroup'
        ⟨y.val i, y.property i (Set.mem_univ i)⟩
    refine ⟨∑ i, n i, Subtype.ext (funext fun i => ?_)⟩
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have he : y.val i ^ (p ^ n i) = 1 := congrArg Subtype.val (hn i)
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one he).trans
      (pow_dvd_pow p hi))
  have hQR : (Q : Subgroup (∀ i, K i)) ≤ R := by
    intro y hy i _
    exact mem_map_of_mem _ hy
  have he := Q.is_maximal' hp hQR
  change x ∈ (Q : Subgroup (∀ i, K i)) ↔ _
  conv_lhs => rw [← he]
  simp only [R, mem_pi, Set.mem_univ, forall_const]

/-- The Sylow normalizer in a commuting factor embeds in the normalizer
of the original ambient Sylow subgroup. Central intersections are allowed. -/
theorem factor_normalizer_control
    (C : ι → Subgroup G)
    (hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hgen : iSup C = ⊤) (P : Sylow p G) (i : ι) :
    ∃ R : Sylow p (C i),
      (R : Subgroup (C i)) = (P : Subgroup G).subgroupOf (C i) ∧
      (normalizer (R : Set (C i))).map (C i).subtype ≤ normalizer (P : Set G) := by
  classical
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    exact (hcomm hij hx y hy).symm
  let f : (∀ i, C i) →* G := noncommPiCoprod hc
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (noncommPiCoprod_range.trans hgen)
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hf p P
  have hQP : Q.map f = (P : Subgroup G) := congrArg Sylow.toSubgroup hQ
  let R : Sylow p (C i) := Q.mapSurjective
    (f := Pi.evalMonoidHom (fun j => C j) i) (Function.surjective_eval i)
  have hsingle (y : C i) (hy : y ∈ R) : Pi.mulSingle i y ∈ Q := by
    apply (mem_pi_sylow_iff (fun j => C j) Q _).mpr
    intro j
    by_cases h : i = j
    · subst j
      change y ∈ Q.map (Pi.evalMonoidHom (fun j => C j) i) at hy
      simpa only [Pi.mulSingle_eq_same] using hy
    · simpa only [Pi.mulSingle_eq_of_ne (Ne.symm h), Pi.mul_apply, Pi.inv_apply, one_mul, inv_one, mul_one] using
        (Q.map (Pi.evalMonoidHom (fun j => C j) j)).one_mem
  have hRP : (R : Subgroup (C i)) ≤ (P : Subgroup G).subgroupOf (C i) := by
    intro y hy
    change y.val ∈ (P : Subgroup G)
    rw [← hQP]
    exact ⟨Pi.mulSingle i y, hsingle y hy, noncommPiCoprod_mulSingle (hcomm := hc) i y⟩
  have he := (R.is_maximal' P.isPGroup'.comap_subtype hRP).symm
  refine ⟨R, he, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hzQ : Pi.mulSingle i z ∈ normalizer (Q : Set (∀ j, C j)) := by
    change z ∈ normalizer ((Q.map (Pi.evalMonoidHom (fun j => C j) i)) : Set (C i)) at hz
    apply mem_normalizer_iff.mpr
    intro x
    change x ∈ Q ↔ Pi.mulSingle i z * x * (Pi.mulSingle i z)⁻¹ ∈ Q
    rw [mem_pi_sylow_iff (fun j => C j) Q, mem_pi_sylow_iff (fun j => C j) Q]
    constructor <;> intro hx j
    · by_cases h : i = j
      · subst j
        simpa only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] using
          (mem_normalizer_iff.mp hz (x i)).mp (hx i)
      · simpa only [Pi.mulSingle_eq_of_ne (Ne.symm h), Pi.mul_apply, Pi.inv_apply, one_mul, inv_one, mul_one] using hx j
    · by_cases h : i = j
      · subst j
        apply (mem_normalizer_iff.mp hz (x i)).mpr
        simpa only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] using hx i
      · simpa only [Pi.mulSingle_eq_of_ne (Ne.symm h), Pi.mul_apply, Pi.inv_apply, one_mul, inv_one, mul_one] using hx j
  have hm := (Q : Subgroup (∀ j, C j)).le_normalizer_map f (mem_map_of_mem f hzQ)
  rw [hQP] at hm
  change (z : G) ∈ normalizer (P : Set G)
  simpa only [f, noncommPiCoprod_mulSingle, Sylow.coe_coe] using hm

end Sylow
