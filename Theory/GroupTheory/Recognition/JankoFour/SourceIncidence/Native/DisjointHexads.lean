module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.HexadOrbits
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
# Regular action on disjoint hexads

A nonidentity element of a hexad's pointwise E₁₆ fixes exactly that hexad.
If it stabilized a disjoint hexad, its six-point action would be a fixed-point-free
involution, hence odd. The actual hexad action lies in A₆, excluding this.
The sixteen-element kernel therefore acts freely on the sixteen disjoint hexads,
and evaluation is bijective. This uses no new finite enumeration.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (5.3)(2), p.600, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeHexads
open Sporadic.Mathieu SourceCycleBase

private theorem even_six_involution_fixed (p : Equiv.Perm (Fin 6))
    (hp : p^2=1) (he : Equiv.Perm.sign p = 1) : ∃ i, p i = i := by
  classical
  by_contra hn
  have hi : IsEmpty (Function.fixedPoints p) := ⟨fun x => hn ⟨x.val,x.property⟩⟩
  have hh := Equiv.Perm.sign_of_pow_two_eq_one hp
  rw [he,Fintype.card_fin,Fintype.card_eq_zero (α := Function.fixedPoints p)] at hh
  norm_num at hh

theorem kernel_disjoint_fixer (A B : Hexad) (hd : (B.val ∩ A.val).card = 0)
    (g : m22HexadPointwiseKernel A.val) (hg : (g : M22) • B.val = B.val) : g = 1 := by
  classical
  by_contra hne
  let := m22HexadPointwiseKernel_elementaryAbelian A.property
  have hg2 : g^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (m22HexadPointwiseKernel A.val)) g
  have hgo : orderOf (g : M22) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime_iff.mpr ⟨hg2,hne⟩
  obtain ⟨D,hD,hfix⟩ := m22_exists_fixed_hexad g.val hgo
  have hAD : A.val = D := Finset.eq_of_subset_of_card_le
    (fun x hx => (hfix x).mp ((mem_m22HexadPointwiseKernel A.val g.val).mp g.property x hx))
    (by rw [m22Block_card _ hD,m22Block_card _ A.property])
  let gs : MulAction.stabilizer M22 B.val := ⟨g,hg⟩
  have hp : (m22HexadAction B.property gs)^2=1 := by
    rw [←map_pow]
    have hgs : gs^2=1 := Subtype.ext (congrArg (fun v : m22HexadPointwiseKernel A.val => (v : M22)) hg2)
    rw [hgs,map_one]
  have he : Equiv.Perm.sign (m22HexadAction B.property gs) = 1 := by
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [←m22HexadAction_range B.property]
    exact ⟨gs,rfl⟩
  obtain ⟨i,hi⟩ := even_six_involution_fixed _ hp he
  let b := (m22HexadLabels B.property).symm i
  have hb : (g : M22) • b.val = b.val := by
    have hh := m22HexadAction_apply B.property gs b
    have hi' : m22HexadLabels B.property b = i := (m22HexadLabels B.property).apply_symm_apply i
    rw [hi',hi] at hh
    have hh' := (m22HexadLabels B.property).injective (hh.symm.trans hi'.symm)
    exact congrArg Subtype.val hh'
  have ha : b.val ∈ A.val := hAD ▸ (hfix b.val).mp hb
  have hmem : b.val ∈ B.val ∩ A.val := Finset.mem_inter.mpr ⟨b.property,ha⟩
  rw [Finset.card_eq_zero.mp hd] at hmem
  exact Finset.notMem_empty _ hmem

theorem kernel_disjoint_stable (A B : Hexad) (hd : (B.val ∩ A.val).card=0)
    (g : m22HexadPointwiseKernel A.val) : ((g.val • B.val) ∩ A.val).card=0 := by
  have hg : g.val • A.val = A.val := m22HexadPointwiseKernel_le A.val g.property
  calc
    _ = ((g.val • B.val) ∩ (g.val • A.val)).card := congrArg (fun C => ((g.val • B.val) ∩ C).card) hg.symm
    _ = (B.val ∩ A.val).card := inter_card_smul g.val B.val A.val
    _ = 0 := hd

/-- The literal pointwise hexad kernel acts regularly on the sixteen disjoint
hexads. This is a different action from its action on complementary points. -/
theorem kernel_disjoint_regular (A B : Hexad) (hd : (B.val ∩ A.val).card=0) :
    Function.Bijective (fun g : m22HexadPointwiseKernel A.val =>
      (⟨smulHexad g.val B,kernel_disjoint_stable A B hd g⟩ :
        {C : Hexad // (C.val ∩ A.val).card=0})) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro g k he
    have hh : g.val • B.val = k.val • B.val := congrArg (fun C => C.val.val) he
    have hfix : (k⁻¹*g).val • B.val = B.val := by
      change (k.val⁻¹ * g.val) • B.val = B.val
      rw [mul_smul]
      rw [hh,inv_smul_smul]
    have hk := kernel_disjoint_fixer A B hd (k⁻¹*g) hfix
    exact (inv_mul_eq_one.mp hk).symm
  · rw [m22HexadPointwiseKernel_card A.property,nonneighbor_card]

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeHexads
