module
public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Perm.Centralizer
public import Theory.GroupTheory.CentralizerSmallKernelTransport
import all Theory.SpecificGroups.SymmetricFive.OuterFourGeometry

/-!
# The dihedral structure of a transposition centralizer

The existing twelve-word model in S₅ is exactly the centralizer of (23).
Conjugacy of transpositions gives an actual dihedral isomorphism for every
such centralizer. A normal two-subgroup of D₁₂ is central: its elements and
commutators with a rotation have fourth power one, which excludes reflections.
Thus a homomorphism onto a transposition centralizer kills commutators with
the domain's two-core.

This is an intentional internal companion to OuterFourGeometry, reusing its
private twelve-word certificate through `import all` without changing its
public API. The finite checks use twelve dihedral words. A representative
probe used 8.35 seconds wall time and 1.91 GiB peak memory with default limits.
The actual Rudvalis ambient quotient consumes both conclusions in Chapter13's
OriginalOddNormalizer.RudvalisAmbientOrder.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFive
open OuterFourGeometry

private theorem local_eq_swap_centralizer :
    localGroup = centralizer ({Equiv.swap 2 3} : Set (Equiv.Perm (Fin 5))) := by
  have hle : localGroup ≤ centralizer ({Equiv.swap 2 3} : Set (Equiv.Perm (Fin 5))) := by
    have hh : ∀ d : DihedralGroup 6, localHom d * Equiv.swap 2 3 =
        Equiv.swap 2 3 * localHom d := by decide +kernel
    rintro _ ⟨d,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hh d)
  apply eq_of_le_of_card_ge hle
  rw [local_card,Equiv.Perm.nat_card_centralizer]
  rw [Equiv.Perm.isSwap_iff_cycleType.mp
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (2 : Fin 5) ≠ 3))]
  norm_num [Nat.factorial]

/-- The full transposition centralizer is an actual dihedral group of order twelve. -/
theorem transposition_centralizer_dihedral (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap) :
    Nonempty (centralizer ({t} : Set (Equiv.Perm (Fin 5))) ≃* DihedralGroup 6) := by
  obtain ⟨i,j,hij,rfl⟩ := ht
  obtain ⟨g,hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hij (by decide : (2 : Fin 5) ≠ 3))
  let a := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    (MulAut.conj g) (Equiv.swap i j)
  let b := MulEquiv.subgroupCongr
    (congrArg (fun z : Equiv.Perm (Fin 5) => centralizer ({z} : Set (Equiv.Perm (Fin 5)))) hg)
  exact ⟨(a.trans b).trans ((MulEquiv.subgroupCongr local_eq_swap_centralizer.symm).trans localEquiv)⟩

private theorem dihedral_six_twoCore_central :
    pCore 2 (DihedralGroup 6) ≤ center (DihedralGroup 6) := by
  have hpow (x : pCore 2 (DihedralGroup 6)) : x ^ 4 = 1 := by
    have hd : orderOf x ∣ 12 := (orderOf_dvd_natCard x).trans
      ((pCore 2 (DihedralGroup 6)).card_subgroup_dvd_card.trans (by
        rw [DihedralGroup.nat_card]))
    have hc := (pCore_isPGroup (p := 2) (G := DihedralGroup 6)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) x
    exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right hd)
  have htest : ∀ x y : DihedralGroup 6, x ^ 4 = 1 →
      (DihedralGroup.r 1 * x * (DihedralGroup.r 1)⁻¹ * x⁻¹) ^ 4 = 1 →
      y * x = x * y := by decide +kernel
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply htest x y (congrArg Subtype.val (hpow ⟨x,hx⟩))
  have hm : DihedralGroup.r 1 * x * (DihedralGroup.r 1)⁻¹ * x⁻¹ ∈ pCore 2 (DihedralGroup 6) :=
    (pCore 2 _).mul_mem ((inferInstance : (pCore 2 (DihedralGroup 6)).Normal).conj_mem x hx _)
      ((pCore 2 _).inv_mem hx)
  exact congrArg Subtype.val (hpow ⟨_,hm⟩)

/-- A map onto a transposition centralizer kills all commutators with the two-core. -/
theorem transposition_image_twoCore_commutator
    {B : Type*} [Group B] [Finite B] (r : B →* Equiv.Perm (Fin 5))
    (t : Equiv.Perm (Fin 5)) (ht : t.IsSwap)
    (hr : r.range = centralizer ({t} : Set (Equiv.Perm (Fin 5)))) :
    ⁅pCore 2 B,⊤⁆ ≤ r.ker := by
  obtain ⟨e⟩ := transposition_centralizer_dihedral t ht
  let d := (MulEquiv.subgroupCongr hr).trans e
  let q := d.toMonoidHom.comp r.rangeRestrict
  have hq : Function.Surjective q := d.surjective.comp r.rangeRestrict_surjective
  let : ((pCore 2 B).map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hi : (pCore 2 B).map q ≤ pCore 2 (DihedralGroup 6) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map q⟩
  apply commutator_le.mpr
  intro x hx y _
  change r (x*y*x⁻¹*y⁻¹) = 1
  have hc := mem_center_iff.mp (dihedral_six_twoCore_central (hi (mem_map_of_mem q hx))) (q y)
  have he : q (x*y*x⁻¹*y⁻¹) = 1 := by
    simp only [map_mul,map_inv]
    rw [←hc,mul_inv_cancel_right,mul_inv_cancel]
  have hq1 : r.rangeRestrict (x*y*x⁻¹*y⁻¹) = 1 := d.injective (he.trans (map_one d).symm)
  exact congrArg Subtype.val hq1

end Theory.SpecificGroups.SymmetricFive
