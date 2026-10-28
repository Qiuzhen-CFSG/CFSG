module
public import Theory.GroupTheory.Hall.TwoComplementConjugacy
public import Theory.GroupTheory.InvertedOddLift
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalReflection

/-!
# Preserving an involution class while normalizing an odd cyclic Cartan

Suppose an involution inverts the image of an odd cyclic subgroup modulo a
normal two-subgroup. Its product with a conjugate involution has the full
cyclic image. Extracting the odd part gives a cyclic complement inverted by
the original involution. Conjugacy of odd complements by the two-kernel then
puts this complement onto the prescribed Cartan. Thus the correction is a
conjugation, preserving the original involution class, even when the Cartan
has nontrivial fixed points in the kernel.

The SL₂ application starts with a prescribed upper-root involution and keeps
its exact antidiagonal quotient image. This is the noncentral torus step in
DGS, *Groups and Graphs* (1985), (14.2), pp.210--211, used at the binary
commuting alpha endpoint. No natural-module or extension-splitting premise
is needed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X Y : Type*} [Group X] [Finite X] [Group Y]

/-- An involution inverting a cyclic odd quotient Cartan has a two-kernel
conjugate normalizing the prescribed Cartan itself. -/
theorem exists_cyclic_cartan_conjugate
    (π : X →* Y) (K : Subgroup X) [IsCyclic K]
    (hQ : IsPGroup 2 π.ker) (ho : Odd (Nat.card K))
    (v : X) (hv : v*v=1)
    (hinv : ∀ k∈K, π v * π k * (π v)⁻¹=(π k)⁻¹) :
    ∃ q∈π.ker, q*v*q⁻¹∈normalizer (K : Set X) := by
  obtain ⟨k,hk⟩ := K.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hkK : k∈K := hk ▸ mem_zpowers k
  have hok : Odd (orderOf (π k)) :=
    (ho.of_dvd_nat (K.orderOf_dvd_natCard hkK)).of_dvd_nat (orderOf_map_dvd π k)
  let w := k*v*k⁻¹
  have hw : w^2=1 := by
    change (MulAut.conj k v)^2=1
    rw [←map_pow,show v^2=1 from by simpa only [pow_two] using hv,map_one]
  have hprod : π (v*w)=((π k)^2)⁻¹ := by
    have hvi : (π v)⁻¹=π v := inv_eq_of_mul_eq_one_right (by rw [←map_mul,hv,map_one])
    have hh := hinv k hkK
    rw [hvi] at hh
    change π (v*(k*v*k⁻¹))=_
    rw [map_mul,map_mul,map_mul,map_inv]
    calc
      π v * (π k * π v * (π k)⁻¹) = (π v * π k * π v) * (π k)⁻¹ := by group
      _ = ((π k)^2)⁻¹ := by rw [hh,pow_two,mul_inv_rev]
  have hop : Odd (orderOf (π (v*w))) := by
    rw [hprod,orderOf_inv]
    exact hok.of_dvd_nat (orderOf_pow_dvd (x := π k) 2)
  obtain ⟨r,_,hor,hr,hir⟩ := exists_inverted_odd_of_involution_product π v w
    (by simpa only [pow_two] using hv) hw hop
  have himage : (zpowers r).map π=K.map π := by
    rw [MonoidHom.map_zpowers,hr,hprod,zpowers_inv,←hk,MonoidHom.map_zpowers]
    apply le_antisymm (zpowers_le.mpr (pow_mem (mem_zpowers _) _))
    obtain ⟨n,hn⟩ := exists_pow_eq_self_of_coprime (x := π k) hok.coprime_two_left
    apply zpowers_le.mpr
    have hh := pow_mem (mem_zpowers ((π k)^2)) n
    rwa [hn] at hh
  have hsup : π.ker ⊔ zpowers r=π.ker ⊔ K := by
    have hh := congrArg (Subgroup.comap π) himage
    simpa only [comap_map_eq,sup_comm] using hh
  let _ : Group.IsSolvable K := Group.isSolvable_of_comm (mul_comm' (M := K))
  obtain ⟨q,hq,hqK⟩ := OddHall.exists_two_conjugator_of_common_sup
    π.ker K (zpowers r) hQ ho.coprime_two_left
    (by rw [Nat.card_zpowers]; exact hor.coprime_two_left)
    le_normalizer_of_normal le_normalizer_of_normal hsup
  have hvR : v∈normalizer (zpowers r : Set X) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (v*r*v⁻¹)=zpowers r
    rw [hir,zpowers_inv]
  have hh := (zpowers r).le_normalizer_map (MulAut.conj q).toMonoidHom
    (mem_map_of_mem (MulAut.conj q).toMonoidHom hvR)
  rw [hqK] at hh
  exact ⟨q,hq,hh⟩
end Theory.GroupTheory.WeakBNPair.RegularTree

open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open NaturalCubic Matrix.SpecialLinearGroup
variable {X F : Type*} [Group X] [Finite X] [Field F] [CharP F 2]

/-- A prescribed upper-root involution has a conjugate normalizing the
odd cyclic diagonal Cartan, with the literal quotient braid retained. -/
theorem exists_diagonal_cyclic_cartan_reflection
    (π : X →* SL(2,F)) (honto : Function.Surjective π)
    (K : Subgroup X) [IsCyclic K] (hQ : IsPGroup 2 π.ker)
    (ho : Odd (Nat.card K))
    (hdiag : ∀ k∈K, ∃ b : F, ∃ hb : b≠0, π k=diag2 b hb)
    (x : X) (hx : x*x=1) (a : F) (ha : a≠0) (hπx : π x=upper a) :
    ∃ t : X, t∈normalizer (K : Set X) ∧ t*t=1 ∧
      π t=upper a*lower a⁻¹*upper a ∧ ∃ g : X, g*x*g⁻¹=t := by
  obtain ⟨g,hg⟩ := honto (lower a⁻¹)
  let v := g*x*g⁻¹
  have hv : v*v=1 := by
    calc
      _ = g*(x*x)*g⁻¹ := by dsimp [v]; group
      _ = 1 := by rw [hx,mul_one,mul_inv_cancel]
  have hπv : π v=upper a*lower a⁻¹*upper a := by
    change π (g*x*g⁻¹)=_
    rw [map_mul,map_mul,map_inv,hg,hπx,lower_conjugates_upper a ha]
  obtain ⟨q,hq,hqN⟩ := exists_cyclic_cartan_conjugate π K hQ ho v hv (by
    intro k hk
    obtain ⟨b,hb,hbk⟩ := hdiag k hk
    rw [hπv,hbk,braid_inverts_diagonal a b ha hb])
  refine ⟨q*v*q⁻¹,hqN,?_,?_,q*g,?_⟩
  · calc
      _ = q*(v*v)*q⁻¹ := by group
      _ = 1 := by rw [hv,mul_one,mul_inv_cancel]
  · rw [map_mul,map_mul,map_inv,show π q=1 from hq,one_mul,inv_one,mul_one,hπv]
  · dsimp only [v]; group
end Theory.GroupTheory.WeakBNPair.RegularTree
