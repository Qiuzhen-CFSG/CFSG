module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.CoreProduct
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer.Pointwise

/-!
# The centralizer of the original Ru plane

Under the faithful natural coordinates, a member of the original plane
normalizer centralizes the plane exactly when its quotient fixes every
vector of the binary plane. The pointwise-fixer theorem puts that image
in the stabilizer two-core. The original quotient has two-group kernel,
so lifting the two-core gives the literal subgroup R₂.

For F ≤ G₂ and V₂ ≤ A = F ∩ R₂, the same equality gives C_F(A) ≤ A.
The second source endpoint uses this with its original F₂ and A when
establishing characteristic two.

Source: Aschbacher–Smith, J.4.5, printed p.442, using the original
natural-module setup of J.4 and J.4.4(2).
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)
open BinaryLinearThree

private theorem quotient_kernel_pGroup : IsPGroup 2 p.quotient.ker := by
  have he : p.quotient.ker = p.parabolicMap.ker := by
    ext b
    change p.quotient b = 1 ↔ p.parabolicMap b = 1
    rw [show p.parabolicMap b = (p.quotient b : Group) by
      rw [p.quotient_apply,p.parabolicMap_apply]]
    exact Subtype.val_injective.eq_iff.symm
  rw [he,p.parabolicMap_kernel]
  exact (isPGroup_pCoreIn 2 d.L).comap_subtype

/-- The centralizer in the actual second parabolic is its original two-core. -/
theorem Plane.parabolic_inf_centralizer :
    p.parabolic ⊓ centralizer (p.group : Set G) = p.R₂ := by
  apply le_antisymm
  · intro a ha
    let b : p.parabolic := ⟨a,ha.1⟩
    have hf : ∀ v : Vector, v ∈ p.naturalSpace → W (p.quotient b : Group) v = v := by
      intro v hv
      obtain ⟨x,hx⟩ := d.ru1.natural.onto (Multiplicative.ofAdd v)
      have hxp : (x:G) ∈ p.group := (p.mem_naturalSpace x).mp (by simpa [hx] using hv)
      let l : d.L := ⟨a,((p.mem_parabolic _).mp ha.1).1⟩
      let y : d.V := ⟨(l:G) * (x:G) * (l:G)⁻¹,
        (mem_normalizer_iff.mp (d.ru1.natural.normalized l.property) x).mp x.property⟩
      have hy : y = x := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (ha.2 (x:G) hxp).symm
      have he := d.ru1.natural.equivariant l x
      change (d.ru1.natural.coordinates y).toAdd = W (d.ru1.quotientMap l)
        (d.ru1.natural.coordinates x).toAdd at he
      rw [hy,hx] at he
      rw [p.quotient_apply]
      exact he.symm
    have hm := (NaturalPlaneStabilizer.mem_core_iff_fixes p.naturalSpace
      p.finrank_naturalSpace (p.quotient b : Group)).mpr hf
    have hm' : p.quotient b ∈ pCore 2 (NaturalPlaneStabilizer.stabilizer p.naturalSpace) := by
      obtain ⟨c,hc,he⟩ := hm
      exact (Subtype.ext he : c = p.quotient b) ▸ hc
    have hb : b ∈ pCore 2 p.parabolic := by
      rw [← p.quotient.comap_pCore_of_ker_isPGroup p.quotient_surjective
        (quotient_kernel_pGroup p)]
      exact hm'
    rw [p.R₂_eq]
    exact mem_map_of_mem p.parabolic.subtype hb
  · exact le_inf (p.R₂_eq ▸ pCoreIn_le 2 p.parabolic) p.R₂_centralizes

/-- The source F₂ application: containing the original plane forces the
centralizer of A into the actual intersection A = F ∩ R₂. -/
theorem Plane.centralizer_le_of_plane_le {F A : Subgroup G}
    (hFP : F ≤ p.parabolic) (hVA : p.group ≤ A) (hFA : F ⊓ p.R₂ = A) :
    F ⊓ centralizer (A : Set G) ≤ A := by
  exact (le_inf inf_le_left
    ((inf_le_inf hFP (centralizer_le hVA)).trans_eq p.parabolic_inf_centralizer)).trans_eq hFA

end CFSG.Quasithin.ChapterJ.RuSubgroup
