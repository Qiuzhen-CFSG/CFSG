module

public import Theory.GroupTheory.PerfectCentralCoverExistence
/-!
# Lifting an involution through every elementary central cover

An involutory automorphism of the actual universal cover descends through
every perfect central cover when each displacement of a universal-kernel
element is a square. Such squares vanish in the elementary target kernel.
The constructed automorphism preserves the given projection and fixes its
kernel pointwise; no choice of a lift is assumed.

Source: Aschbacher–Smith I.2.2(3b), printed pp.409–410.
-/

public section
open PerfectCentralCovering Subgroup
namespace PerfectCentralCovering
universe u v
variable {G : Type u} [Group G] [Group.IsPerfect G]
  {E : Type v} [Group E] [Group.IsPerfect E]
theorem exists_involutory_lift_of_universal_square_displacements
    (β : MulAut G) (a : MulAut (UniversalGroup G))
    (ha : ∀ x, universalProjection G (a x)=β (universalProjection G x))
    (ha2 : a^2=1)
    (hsquare : ∀ z : (universalProjection G).ker,
      ∃ w : (universalProjection G).ker, (w : UniversalGroup G)^2=a z*(z : UniversalGroup G)⁻¹)
    (f : E →* G) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hexp : ∀ z ∈ f.ker,z^2=1) :
    ∃ b : MulAut E, (∀ x, f (b x)=β (f x)) ∧
      (∀ z ∈ f.ker,b z=z) ∧ b^2=1 := by
  obtain ⟨h,hh,_⟩ := universalProjection_existsUnique_lift f hf hc
  have hh' (x) : f (h x)=universalProjection G x := DFunLike.congr_fun hh x
  have hsurj : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f h
      (hh ▸ universalProjection_surjective G) hc
  have hfix (z : (universalProjection G).ker) : h (a z)=h z := by
    obtain ⟨w,hw⟩ := hsquare z
    have hwker : h w ∈ f.ker := (hh' w).trans w.property
    have hsq := hexp (h w) hwker
    have he := congrArg h hw
    rw [map_pow,map_mul,map_inv,hsq] at he
    exact mul_inv_eq_one.mp he.symm
  have hkill : h.ker ≤ (h.comp a.toMonoidHom).ker := by
    intro x hx
    have hz : x ∈ (universalProjection G).ker := by
      change universalProjection G x=1
      rw [←hh',show h x=1 from hx,map_one]
    exact (hfix ⟨x,hz⟩).trans hx
  let bHom : E →* E := h.liftOfSurjective hsurj ⟨h.comp a.toMonoidHom,hkill⟩
  have hb (x) : bHom (h x)=h (a x) :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have haa (x) : a (a x)=x := by
    exact congrArg (fun t : MulAut (UniversalGroup G) => t x) ha2
  have hbb (x) : bHom (bHom x)=x := by
    obtain ⟨y,rfl⟩ := hsurj x
    rw [hb,hb,haa]
  let b : MulAut E := { bHom with invFun := bHom, left_inv := hbb, right_inv := hbb }
  refine ⟨b,?_,?_,?_⟩
  · intro x
    obtain ⟨y,rfl⟩ := hsurj x
    change f (bHom (h y))=β (f (h y))
    rw [hb,hh',hh',ha]
  · intro z hz
    obtain ⟨y,rfl⟩ := hsurj z
    have hy : y ∈ (universalProjection G).ker := (hh' y).symm.trans hz
    change bHom (h y)=h y
    exact (hb y).trans (hfix ⟨y,hy⟩)
  · apply MulEquiv.ext
    intro x
    exact hbb x
end PerfectCentralCovering
