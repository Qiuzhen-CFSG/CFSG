module
public import Theory.GroupTheory.DihedralFiveTwist
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeOddInvolution
public import Theory.Representation.HexacodeAction.Cover
import all Theory.GroupTheory.DihedralFiveTwist

/-!
# Odd extensions of the original code tensor actors

An involution normalizing D10 fixes a reflection; the dihedral twist therefore
centralizes that same image without prescribing a new ambient reflection.
An odd hexacode automorphism inverts every element of the even group's cubic
centre. This inversion transfers through a cover with full two-core kernel
to any action killing that kernel, retaining both ambient inclusions.

These are the group calculations used on the original P/U in source
Aschbacher--Smith 8.2.8(6), printed p.719, refs/quasithin.pdf. The internal
DihedralFiveTwist import reuses its private rotation calculation. The native
hexacode models retain the ATLAS attribution and license in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Atlas.Codes Representation
namespace MathieuCode.NormalizedShadowRows.CodeExtension

theorem odd_inverts_even_center (t : HexAutomorphisms) (ht : hexSign t = -1)
    (z : HexEvenAutomorphisms) (hz : z ∈ center HexEvenAutomorphisms) :
    t * z.val * t⁻¹ = z.val⁻¹ := by
  rw [← Hexacode.even_kernel_eq_center, hexEvenCoordinate_kernel] at hz
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hz
  change (MulAut.conj t) (hexZ ^ n) = (hexZ ^ n)⁻¹
  rw [map_zpow]
  change (t * hexZ * t⁻¹) ^ n = _
  rw [hex_conjugation_odd t ht, inv_zpow]

private theorem fixed_reflection (a : MulAut (DihedralGroup 5))
    (ha : ∀ d, a (a d) = d) :
    ∃ j : ZMod 5, a (.sr j) = .sr j := by
  have hs := a.orderOf_eq (.sr 0)
  cases he : a (.sr 0) with
  | r j =>
    have hj : orderOf (DihedralGroup.r j : DihedralGroup 5) ∣ 5 := by
      apply orderOf_dvd_of_pow_eq_one
      exact (show ∀ k : ZMod 5, (DihedralGroup.r k : DihedralGroup 5)^5 = 1 by decide +kernel) j
    rw [he,DihedralGroup.orderOf_sr] at hs
    rw [hs] at hj
    norm_num at hj
  | sr j =>
    have hrot := DihedralGroup.automorphism_square_rotation a ha
    have hj (k : ZMod 5) :
        a (.sr k) = .sr j * a (.r 1) ^ k.val := by
      rw [show (DihedralGroup.sr k : DihedralGroup 5) = .sr 0 * .r 1 ^ k.val by
        simp, map_mul,map_pow,he]
    rcases hrot with hr | hr
    · have hh := ha (.sr 0)
      rw [he,hj,hr] at hh
      have hj0 : j = 0 := by
        have h2 : j + j = 0 := by simpa using hh
        exact (show ∀ k : ZMod 5, k+k = 0 → k=0 by decide +kernel) j h2
      exact ⟨0,by simpa only [hj0] using he⟩
    · refine ⟨3*j,?_⟩
      rw [hj,hr]
      have hcalc : ∀ k : ZMod 5,
          (DihedralGroup.sr k * (DihedralGroup.r 1)⁻¹ ^ (3*k).val : DihedralGroup 5) =
            .sr (3*k) := by decide +kernel
      exact hcalc j

/-- An involution normalizing the same D10 image fixes some reflection of
that image. Changing only its marking makes the existing twist applicable. -/
theorem normalizing_involution_twist {H : Type*} [Group H]
    (D : Subgroup H) (e : D ≃* DihedralGroup 5) (t : H)
    (ht : t ^ 2 = 1) (hn : t ∈ normalizer (D : Set H)) :
    ∃ (v : D) (s : H), (s = t ∨ s = t * v.val) ∧ s ^ 2 = 1 ∧
      ∀ d : D, Commute s d.val := by
  let a : MulAut (DihedralGroup 5) :=
    (e.symm.trans (D.normalizerMonoidHom ⟨t,hn⟩)).trans e
  have ha (d) : a (a d) = d := by
    change e (D.normalizerMonoidHom ⟨t,hn⟩
      (e.symm (e (D.normalizerMonoidHom ⟨t,hn⟩ (e.symm d))))) = d
    rw [e.symm_apply_apply]
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change t * (t * (e.symm d : H) * t⁻¹) * t⁻¹ = (e.symm d : H)
    have htt : t * t = 1 := by simpa only [pow_two] using ht
    calc
      _ = (t*t) * (e.symm d : H) * (t*t)⁻¹ := by group
      _ = _ := by rw [htt,inv_one,one_mul,mul_one]
  obtain ⟨j,hj⟩ := fixed_reflection a ha
  let c : MulAut (DihedralGroup 5) := MulAut.conj (.r (3*j))
  have hc : c (.sr j) = .sr 0 := by
    change DihedralGroup.r (3*j) * .sr j * (.r (3*j))⁻¹ = .sr 0
    exact (show ∀ k : ZMod 5,
      (DihedralGroup.r (3*k) * .sr k * (.r (3*k))⁻¹ : DihedralGroup 5) = .sr 0 by decide +kernel) j
  let e' := e.trans c
  have hv : e'.symm (.sr 0) = e.symm (.sr j) := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    change _ = c (e (e.symm (.sr j)))
    rw [e.apply_symm_apply,hc]
  have hfix : Commute t (e'.symm (.sr 0) : H) := by
    rw [hv]
    apply mul_inv_eq_iff_eq_mul.mp
    have hh := congrArg (fun d => (e.symm d : H)) hj
    change (e.symm (e (D.normalizerMonoidHom ⟨t,hn⟩ (e.symm (.sr j)))) : H) = _ at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  obtain ⟨s,hchoice,hs,hsD⟩ :=
    exists_involution_twist_centralizing_dihedral_five D e' t hn ht hfix
  exact ⟨e'.symm (.sr 0),s,hchoice,hs,hsD⟩
/-- Inversion of the central cubic transfers to any action killing the same
full two-core. The two ambient groups and both literal inclusions are retained. -/
theorem odd_inverts_central_quotient {G A : Type*} [Group G] [Group A]
    (R N K : Subgroup G) (hRN : R ≤ N) (hRK : R ≤ K)
    (p : R →* HexEvenAutomorphisms) (hp : Function.Surjective p)
    (hpk : p.ker = pCore 2 R)
    (f : N →* HexAutomorphisms) (hf : ∀ r, f (inclusion hRN r) = (p r).val)
    (σ : K →* A) (hσ : pCore 2 R ≤ (σ.comp (inclusion hRK)).ker)
    (t : G) (htN : t ∈ N) (htK : t ∈ K) (htR : t ∈ normalizer (R : Set G))
    (htodd : hexSign (f ⟨t,htN⟩) = -1)
    (z : R) (hz : QuotientGroup.mk' (pCore 2 R) z ∈ center (R ⧸ pCore 2 R)) :
    σ ⟨t,htK⟩ * σ (inclusion hRK z) * (σ ⟨t,htK⟩)⁻¹ =
      (σ (inclusion hRK z))⁻¹ := by
  let pq := QuotientGroup.lift (pCore 2 R) p hpk.ge
  have hpc : p z ∈ center HexEvenAutomorphisms := by
    rw [mem_center_iff]
    intro y
    obtain ⟨r,rfl⟩ := hp y
    simpa only [map_mul, pq, QuotientGroup.mk'_apply, QuotientGroup.lift_mk'] using
      congrArg pq (mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 R) r))
  let zt : R := R.normalizerMonoidHom ⟨t,htR⟩ z
  have hconjN : inclusion hRN zt = (⟨t,htN⟩ : N) * inclusion hRN z * (⟨t,htN⟩ : N)⁻¹ := by
    apply Subtype.ext
    rfl
  have hpzt : p zt = (p z)⁻¹ := by
    apply Subtype.ext
    rw [←hf,hconjN,map_mul,map_mul,map_inv,hf]
    exact odd_inverts_even_center _ htodd _ hpc
  have hm : zt * z ∈ pCore 2 R := by
    rw [←hpk]
    change p (zt*z) = 1
    rw [map_mul,hpzt,inv_mul_cancel]
  have hs := hσ hm
  change σ (inclusion hRK (zt*z)) = 1 at hs
  rw [map_mul,map_mul] at hs
  have hconjK : inclusion hRK zt = (⟨t,htK⟩ : K) * inclusion hRK z * (⟨t,htK⟩ : K)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hconjK,map_mul,map_mul,map_inv] at hs
  exact mul_eq_one_iff_eq_inv.mp hs

end MathieuCode.NormalizedShadowRows.CodeExtension
