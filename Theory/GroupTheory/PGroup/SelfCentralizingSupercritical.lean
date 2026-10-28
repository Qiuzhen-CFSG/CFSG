module
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Supercritical actions above a self-centralizing normal p-group

Let P be a normal p-subgroup of a finite group D, with C_D(P) ≤ P, and
let X be supercritical in P for odd p. The literal actions on X and on
X/Φ(X) have p-group kernels: compose conjugation on P with the existing
supercritical automorphism-detection theorem. In particular C_D(X) ≤ O_p(D).

If P = O_p(D) and Z(X) ≤ Φ(X), supercriticality makes P act trivially on
X/Φ(X), so the full kernel of this action is exactly P. This applies to
the Heisenberg supercritical branch without discarding inner automorphisms.

Source: Aschbacher–Smith, A.1.21(3), printed p.24; used in 14.7.27,
printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace IsSupercriticalPSubgroup
variable {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime]
  (P : Subgroup D) [P.Normal] (hP : IsPGroup p P)
  (hC : centralizer (P : Set D) ≤ P)
  (X : Subgroup P) (hX : IsSupercriticalPSubgroup p X) (hp : Odd p)

include hP hC hX hp

/-- The original conjugation action on X has p-group kernel. -/
theorem ambient_restriction_kernel_isPGroup :
    letI : X.Characteristic := hX.characteristic
    IsPGroup p ((MulAut.characteristic X).comp
      (MulAut.conjNormal : D →* MulAut P)).ker := by
  let : X.Characteristic := hX.characteristic
  have hk : IsPGroup p (MulAut.conjNormal : D →* MulAut P).ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact hP.to_le hC
  exact (hX.isPGroup_restriction_kernel hP hp).comap_of_ker_isPGroup
    (MulAut.conjNormal : D →* MulAut P) hk

/-- The original conjugation action on X/Φ(X) has p-group kernel. -/
theorem ambient_frattini_kernel_isPGroup :
    letI : X.Characteristic := hX.characteristic
    IsPGroup p (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
      (MulAut.conjNormal : D →* MulAut P)).ker := by
  let : X.Characteristic := hX.characteristic
  have hk : IsPGroup p (MulAut.conjNormal : D →* MulAut P).ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact hP.to_le hC
  exact (hX.isPGroup_frattini_action_kernel hP hp).comap_of_ker_isPGroup
    (MulAut.conjNormal : D →* MulAut P) hk

/-- The centralizer of the actual embedded supercritical subgroup lies in O_p(D). -/
theorem ambient_centralizer_le_pCore :
    centralizer (X.map P.subtype : Set D) ≤ pCore p D := by
  let : X.Characteristic := hX.characteristic
  let a := (MulAut.characteristic X).comp (MulAut.conjNormal : D →* MulAut P)
  have hk : a.ker = centralizer (X.map P.subtype : Set D) := by
    ext d
    constructor
    · intro hd
      rintro x ⟨y,hy,rfl⟩
      have he := congrArg (fun f : MulAut X => ((f ⟨y,hy⟩ : P) : D)) hd
      change d * (y : D) * d⁻¹ = (y : D) at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hd
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      change d * (x.val : D) * d⁻¹ = (x.val : D)
      have he : (x.val : D) * d = d * (x.val : D) :=
        hd _ (mem_map_of_mem P.subtype x.property)
      rw [←he,mul_inv_cancel_right]
  rw [←hk]
  exact le_sSup ⟨inferInstance,hX.ambient_restriction_kernel_isPGroup P hP hC X hp⟩

/-- For the full p-core and a special supercritical subgroup, the Frattini-action kernel is exactly O_p(D). -/
theorem ambient_frattini_kernel_eq_pCore
    (hcore : P = pCore p D) (hcenter : center X ≤ frattini X) :
    letI : X.Characteristic := hX.characteristic
    (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
      (MulAut.conjNormal : D →* MulAut P)).ker = pCore p D := by
  let : X.Characteristic := hX.characteristic
  let a := (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
    (MulAut.conjNormal : D →* MulAut P))
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,hX.ambient_frattini_kernel_isPGroup P hP hC X hp⟩
  · rw [←hcore]
    intro d hd
    apply MulEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini X) v
    change quotientAut (frattini X) (MulAut.characteristic X (MulAut.conjNormal d))
      (QuotientGroup.mk' (frattini X) x) = QuotientGroup.mk' (frattini X) x
    rw [quotientAut_apply_mk]
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    have hc := hX.commutator_le
      (commutator_mem_commutator (X.inv_mem x.property) (mem_top (⟨d,hd⟩ : P)))
    obtain ⟨z,hz,he⟩ := hc
    apply hcenter
    have he' : z = x⁻¹ * MulAut.characteristic X (MulAut.conjNormal d) x := by
      apply Subtype.ext
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      simp only [commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv,inv_inv] at hh
      change (z.val : D) = (x.val : D)⁻¹ * (d * (x.val : D) * d⁻¹)
      simpa only [mul_assoc,Subgroup.subtype_apply] using hh
    exact he' ▸ hz

end IsSupercriticalPSubgroup
