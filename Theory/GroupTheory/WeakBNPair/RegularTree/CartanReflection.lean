module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Lifting a Cartan reflection through a two-kernel

In a finite local group, an odd solvable Cartan complements the normal
two-kernel in their product. Hall conjugacy corrects every lift of a
quotient Cartan normalizer by an element of that same kernel. If the
kernel centralizer of the Cartan is trivial, a quotient involution lifts
to an actual involution: its square both lies in the kernel and normalizes
the disjoint Cartan, hence centralizes it.

The correction retains the original quotient representative and lies in
the original local group. The fixed-point-free Cartan condition is explicit;
the cases with a nontrivial kernel centralizer require a different argument.
This is the corresponding lifting step of DGS, *Groups and Graphs* (1985),
(14.2), printed pp.210--211. Conjugacy to a prescribed root involution is
an additional conclusion treated by natural-module coordinates.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X Y : Type*} [Group X] [Finite X] [Group Y]

/-- Correct a lift of a quotient Cartan normalizer by an element of the
actual two-kernel. The chosen quotient representative is retained. -/
theorem exists_cartan_normalizer_lift (π : X →* Y) (K : Subgroup X)
    (hQ : IsPGroup 2 π.ker) (hK : Nat.Coprime 2 (Nat.card K))
    [Group.IsSolvable K] (g : X)
    (hg : π g ∈ normalizer (K.map π : Set Y)) :
    ∃ q ∈ π.ker, q*g ∈ normalizer (K : Set X) := by
  let Q := π.ker
  let B := Q ⊔ K
  let T := normalizer (B : Set X)
  have hn : K ≤ normalizer (Q : Set X) := le_normalizer_of_normal
  let := hQ.isNilpotent
  have hsolv : Group.IsSolvable B := Group.isSolvable_sup_of_normalizes Q K hn
  have hi : ¬ 2 ∣ (Q.subgroupOf B).index := by
    intro hd
    have hid : (Q.subgroupOf B).index ∣ Nat.card K := by
      change Q.relIndex (Q ⊔ K) ∣ Nat.card K
      rw [OddHall.relIndex_normalized_sup Q K hn]
      exact relIndex_dvd_card (H := Q) (K := K)
    exact Nat.prime_two.coprime_iff_not_dvd.mp hK (hd.trans hid)
  let P : Sylow 2 B := (hQ.comap_subtype).toSylow hi
  have hP : (P : Subgroup B).map B.subtype = Q :=
    map_subgroupOf_eq_of_le (show Q ≤ B from le_sup_left)
  have hhall : IsHallSubgroup OddHall.oddPrimes (K.subgroupOf B) :=
    OddHall.oddHall_of_normalized_sup hQ hK hn rfl
  have hprod := OddHall.normal_sylow_frattini B Q T K hsolv
    (le_trans (show Q ≤ B from le_sup_left) B.le_normalizer) le_rfl P hP
    le_sup_right hhall
  have hgT : g ∈ T := by
    have hh := (K.map π).le_normalizer_comap π hg
    change g ∈ normalizer ((Q ⊔ K : Subgroup X) : Set X)
    simpa only [Subgroup.comap_map_eq,sup_comm] using hh
  have hm : g ∈ (Q : Set X) * ((T ⊓ normalizer (K : Set X) : Subgroup X) : Set X) :=
    hprod ▸ hgT
  obtain ⟨q,hq,t,ht,he⟩ := hm
  refine ⟨q⁻¹,Q.inv_mem hq,?_⟩
  rw [←he,inv_mul_cancel_left]
  exact ht.2

omit [Finite X] in
/-- A kernel element normalizing a disjoint subgroup centralizes it. -/
theorem kernel_normalizer_centralizes (π : X →* Y) (K : Subgroup X)
    (hdis : K ⊓ π.ker=⊥) {q : X} (hq : q∈π.ker)
    (hn : q∈normalizer (K : Set X)) : q∈centralizer (K : Set X) := by
  apply mem_centralizer_iff.mpr
  intro k hk
  have hm : q*k*q⁻¹*k⁻¹∈K ⊓ π.ker := by
    constructor
    · exact K.mul_mem ((mem_normalizer_iff.mp hn k).mp hk) (K.inv_mem hk)
    · change π (q*k*q⁻¹*k⁻¹)=1
      simp only [map_mul,map_inv,show π q=1 from hq,
        one_mul,inv_one,mul_one,mul_inv_cancel]
  rw [hdis] at hm
  have he : q*k*q⁻¹=k := mul_inv_eq_one.mp hm
  have hh := congrArg (·*q) he
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm

/-- A quotient involution normalizing the image Cartan lifts to an actual
involution when the two-kernel has trivial Cartan centralizer. -/
theorem exists_cartan_reflection (π : X →* Y) (K : Subgroup X)
    (hQ : IsPGroup 2 π.ker) (hK : Nat.Coprime 2 (Nat.card K))
    [Group.IsSolvable K]
    (hcentral : π.ker ⊓ centralizer (K : Set X)=⊥)
    (g : X) (hgsq : π g * π g=1) (hgne : π g≠1)
    (hg : π g∈normalizer (K.map π : Set Y)) :
    ∃ t : X, t∈normalizer (K : Set X) ∧ t*t=1 ∧ orderOf t=2 ∧
      π t=π g ∧ t*g⁻¹∈π.ker := by
  obtain ⟨q,hq,ht⟩ := exists_cartan_normalizer_lift π K hQ hK g hg
  let t := q*g
  have himage : π t=π g := by
    change π (q*g)=π g
    rw [map_mul,show π q=1 from hq,one_mul]
  have hdis : K ⊓ π.ker=⊥ := by
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    exact (disjoint_of_coprime_natCard (by rw [hn]; exact hK.symm.pow_right n)).eq_bot
  have hsqker : t*t∈π.ker := by rw [MonoidHom.mem_ker,map_mul,himage,hgsq]
  have hsq : t*t=1 := by
    have hh : t*t∈π.ker ⊓ centralizer (K : Set X) :=
      ⟨hsqker,kernel_normalizer_centralizes π K hdis hsqker
        ((normalizer (K : Set X)).mul_mem ht ht)⟩
    rwa [hcentral] at hh
  refine ⟨t,ht,hsq,?_,himage,?_⟩
  · apply orderOf_eq_prime (show t^2=1 by simpa only [pow_two] using hsq)
    intro he
    exact hgne (himage.symm.trans (he ▸ π.map_one))
  · change q*g*g⁻¹∈π.ker
    rwa [mul_inv_cancel_right]

end Theory.GroupTheory.WeakBNPair.RegularTree
