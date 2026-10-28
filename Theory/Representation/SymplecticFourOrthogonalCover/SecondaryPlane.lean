module
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement

/-!
# A secondary plane in every binary symplectic cover

For every two-subgroup of the genuine symplectic component, choose a containing
Sylow and transport its standard isotropic flag. The full preimage of its plane
has displacement in the full preimage of its fixed line. Fixed-point lifting
through the universal cover makes that displacement fixed by the original
actor, without choosing a complement to the central kernel.

The result uses the original projection over every finite characteristic-two
field. Its graph consumer places this fixed displacement in the literal edge
omega-center before applying maximality of the secondary seed.

Source: MS93 (3.6), printed p.871, and Aschbacher--Smith I.2.3, printed p.413.
-/

public section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem movedPlane_self_orthogonal (g : L (K := F)) :
    (form F).orthogonal (SylowFlag.movedPlane g) = SylowFlag.movedPlane g := by
  have hs : (form F).orthogonal (plane F) = plane F := by
    ext v
    change (∀ u ∈ plane F, form F u v = 0) ↔ v ∈ plane F
    constructor
    · intro h i
      have he := h (Theory.SpecificGroups.SymplecticFour.e i) (e_mem_plane i)
      fin_cases i <;> simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using he
    · intro hv u hu
      exact plane_isotropic u v hu hv
  have hplane : SylowFlag.movedPlane g = (plane F).map (symplecticDerivedNatural 2 g) := by
    rw [SylowFlag.movedPlane,SylowFlag.secondPlane_eq_plane]
  rw [hplane]
  ext v
  constructor
  · intro hv
    have hi : symplecticDerivedNatural 2 g⁻¹ v ∈ (form F).orthogonal (plane F) := by
      intro u hu
      have he := hv (symplecticDerivedNatural 2 g u) ⟨u,hu,rfl⟩
      have hf := preserves_form g.val u (symplecticDerivedNatural 2 g⁻¹ v)
      change form F (symplecticDerivedNatural 2 g u)
        (symplecticDerivedNatural 2 g (symplecticDerivedNatural 2 g⁻¹ v)) = _ at hf
      rw [(symplecticDerivedNatural 2).self_inv_apply] at hf
      exact hf.symm.trans he
    rw [hs] at hi
    exact ⟨_,hi,(symplecticDerivedNatural 2).self_inv_apply g v⟩
  · rintro ⟨w,hw,rfl⟩ _ ⟨u,hu,rfl⟩
    exact (preserves_form g.val u w).trans (plane_isotropic u w hu hw)

omit [Algebra (ZMod 2) F] in
private theorem movedPlane_displacement (g : L (K := F))
    (b : SylowFlag.movedSylow g) (v : Vector F) (hv : v ∈ SylowFlag.movedPlane g) :
    symplecticDerivedNatural 2 b.val v-v ∈ SylowFlag.movedLine g := by
  obtain ⟨c,hc,he⟩ := b.property
  obtain ⟨u,hu,rfl⟩ := hv
  change (MulAut.conj g) c = b.val at he
  rw [←he,SylowFlag.Transport.conjugate_action,←map_sub]
  exact ⟨_,(SylowFlag.fixedModulo_firstLine u).mpr hu ⟨c,hc⟩,rfl⟩

/-- Every two-subgroup of the symplectic component admits a self-orthogonal
plane whose entire cover preimage has displacement fixed by that subgroup.
The original natural projection and all of its kernel are retained. -/
theorem exists_plane_with_fixed_cover_displacement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Subgroup (L (K := F))) (hA : IsPGroup 2 A) :
    ∃ P : Submodule F (Vector F), (form F).orthogonal P = P ∧
      ∀ b ∈ A, ∀ w : W, p w ∈ P →
        σ b w-w ∈ fixed (σ.comp A.subtype) := by
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  obtain ⟨g,hg⟩ := SylowFlag.exists_marking S
  refine ⟨SylowFlag.movedPlane g,movedPlane_self_orthogonal g,?_⟩
  intro b hb w hw
  have hbS : b ∈ SylowFlag.movedSylow g := hg ▸ hS hb
  have hdisp := movedPlane_displacement g ⟨b,hbS⟩ (p w) hw
  have hfixed : p (σ b w-w) ∈
      fixed ((binaryNatural (K := F)).comp (SylowFlag.movedSylow g).subtype) := by
    rw [map_sub,p.isIntertwining]
    intro a
    exact (show symplecticDerivedNatural 2 b (p w)-p w ∈
      fixed ((symplecticDerivedNatural 2).comp (SylowFlag.movedSylow g).subtype) from
      (SylowFlag.movedLine_fixed g).symm ▸ hdisp) a
  intro a
  exact cover_fixed_of_projection_fixed p hp a.val (σ b w-w)
    (hfixed ⟨a.val,hg ▸ hS a.property⟩)

end Representation.SymplecticFourOrthogonalCover
