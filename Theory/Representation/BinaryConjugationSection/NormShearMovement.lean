module
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# Shear movement after removing a cubic norm

On a second literal section, a shear recovers a vector modulo its cubic
norm. If that norm vanishes in the first section, the shear still forces
movement of the original span. Multiply the double commutator by the
norm element, then compare both coordinate maps. Only the kernel on the
original span is used; the whole ambient subgroup need not be abelian.

This extends the shear argument to tensor modules with a trivial summand.
Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, 13.8.29(4)–30, printed p.964.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W Z : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  {H A N J B U : Subgroup G}
  {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) J Z}
  (q : BinaryConjugationSection H A N ρ)
  (p : BinaryConjugationSection J B U σ)

private def conjugated {T C D : Subgroup G} {Y : Type*}
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) T Y} (d : BinaryConjugationSection T C D τ)
    (a : T) (x : C) : C :=
  ⟨a * x * (a : G)⁻¹, (mem_normalizer_iff.mp (d.normalized a.property) x).mp x.property⟩

private theorem displacement_coordinates {T C D : Subgroup G} {Y : Type*}
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) T Y} (d : BinaryConjugationSection T C D τ)
    (a : T) (x : C) :
    (d.coordinates (conjugated d a x * x⁻¹)).toAdd =
      τ a (d.coordinates x).toAdd - (d.coordinates x).toAdd := by
  rw [map_mul, map_inv]
  change (d.coordinates (conjugated d a x)).toAdd + -(d.coordinates x).toAdd = _
  rw [show (d.coordinates (conjugated d a x)).toAdd = _ from d.equivariant a x]
  exact (sub_eq_add_neg _ _).symm

/-- A shear modulo a norm that vanishes in the first section forces movement.
The kernel is controlled only on the original span. -/
theorem image_moved_of_section_shear_mod_norm
    (S : Subgroup G) (hSA : S ≤ A) (hSB : S ≤ B) (hUS : U ≤ S)
    (hkernel : S ⊓ N ≤ U) (hproper : ¬ S ≤ U)
    (a b c : H) (ha : (a : G) ∈ J) (hb : (b : G) ∈ J) (hc : (c : G) ∈ J)
    (hnorm : ∀ w, ρ c (ρ c w) + ρ c w + w = 0)
    (hfix : ∀ w ∈ p.imageSpace S, σ ⟨b,hb⟩ w = w)
    (hshear : ∀ w ∈ p.imageSpace S,
      σ ⟨b,hb⟩ (σ ⟨a,ha⟩ w) - σ ⟨a,ha⟩ w =
        w - (σ ⟨c,hc⟩ (σ ⟨c,hc⟩ w) + σ ⟨c,hc⟩ w + w)) :
    ∃ w ∈ q.imageSpace S, ρ a w ∉ q.imageSpace S := by
  classical
  by_contra h
  push Not at h
  apply hproper
  intro x hx
  let xA : A := ⟨x,hSA hx⟩
  let xB : B := ⟨x,hSB hx⟩
  have hxq : (q.coordinates xA).toAdd ∈ q.imageSpace S :=
    (q.mem_imageSpace_iff S _).mpr ⟨xA,hx,rfl⟩
  have hxp : (p.coordinates xB).toAdd ∈ p.imageSpace S :=
    (p.mem_imageSpace_iff S _).mpr ⟨xB,hx,rfl⟩
  obtain ⟨y,hy,he⟩ := (q.mem_imageSpace_iff S _).mp (h _ hxq)
  let yB : B := ⟨y,hSB hy⟩
  let axA := conjugated q a xA
  let axB := conjugated p ⟨a,ha⟩ xB
  let zA := conjugated q b axA * axA⁻¹
  let zB := conjugated p ⟨b,hb⟩ axB * axB⁻¹
  let cA := conjugated q b y * y⁻¹
  let cB := conjugated p ⟨b,hb⟩ yB * yB⁻¹
  have hcU : (cA : G) ∈ U := by
    change (cB : G) ∈ U
    apply (p.coordinates_eq_one_iff cB).mp
    apply Multiplicative.toAdd.injective
    change (p.coordinates cB).toAdd = 0
    rw [displacement_coordinates, hfix _ ((p.mem_imageSpace_iff S _).mpr ⟨yB,hy,rfl⟩), sub_self]
  have hez : (q.coordinates zA).toAdd = (q.coordinates cA).toAdd := by
    rw [displacement_coordinates, displacement_coordinates]
    rw [show (q.coordinates axA).toAdd = _ from q.equivariant a xA, he]
  let nA := conjugated q c (conjugated q c xA) * conjugated q c xA * xA
  let nB := conjugated p ⟨c,hc⟩ (conjugated p ⟨c,hc⟩ xB) *
    conjugated p ⟨c,hc⟩ xB * xB
  have eqA (d : H) (z : A) : (q.coordinates (conjugated q d z)).toAdd =
      ρ d (q.coordinates z).toAdd := q.equivariant d z
  have eqB (d : J) (z : B) : (p.coordinates (conjugated p d z)).toAdd =
      σ d (p.coordinates z).toAdd := p.equivariant d z
  have hnA : (q.coordinates nA).toAdd = 0 := by
    simp only [nA, map_mul, toAdd_mul]
    simp only [eqA]
    exact hnorm _
  have hnB : (p.coordinates nB).toAdd =
      σ ⟨c,hc⟩ (σ ⟨c,hc⟩ (p.coordinates xB).toAdd) +
        σ ⟨c,hc⟩ (p.coordinates xB).toAdd + (p.coordinates xB).toAdd := by
    simp only [nB, map_mul, toAdd_mul]
    simp only [eqB]
  have hpz : (p.coordinates zB).toAdd = (p.coordinates xB).toAdd - (p.coordinates nB).toAdd := by
    rw [displacement_coordinates]
    rw [show (p.coordinates axB).toAdd = _ from p.equivariant ⟨a,ha⟩ xB]
    rw [hnB]
    exact hshear _ hxp
  have hzU : ((zA * nA * xA⁻¹ : A) : G) ∈ U := by
    change ((zB * nB * xB⁻¹ : B) : G) ∈ U
    apply (p.coordinates_eq_one_iff _).mp
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      toAdd_one]
    rw [hpz]
    abel
  have hximage : (q.coordinates xA).toAdd ∈ q.imageSpace U := by
    have hzimage : (q.coordinates zA).toAdd ∈ q.imageSpace U := by
      rw [hez]
      exact (q.mem_imageSpace_iff U _).mpr ⟨cA,hcU,rfl⟩
    have hdiff : (q.coordinates zA).toAdd - (q.coordinates xA).toAdd ∈ q.imageSpace U := by
      have hh := (q.mem_imageSpace_iff U _).mpr ⟨zA * nA * xA⁻¹,hzU,rfl⟩
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
        hnA, add_zero] at hh
      simpa only [sub_eq_add_neg] using hh
    simpa only [sub_sub_cancel] using (q.imageSpace U).sub_mem hzimage hdiff
  obtain ⟨u,hu,heu⟩ := (q.mem_imageSpace_iff U _).mp hximage
  have hn : ((u⁻¹ * xA : A) : G) ∈ N := by
    apply (q.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, Multiplicative.toAdd.injective heu, inv_mul_cancel]
  have hs : ((u⁻¹ * xA : A) : G) ∈ S := S.mul_mem (S.inv_mem (hUS hu)) hx
  have hk := hkernel ⟨hs,hn⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using U.mul_mem hu hk

end Representation.BinaryConjugationSection
