module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.FixedGeneration
public import Theory.ElementaryAbelian.Injective

/-!
# Transport of four-subgroup fixed-space generation

An injective marking of the acting group identifies elementary subgroups of
order four in an original subgroup with those in its image. An equivariant
linear equivalence therefore carries the sum of their fixed spaces onto the
corresponding sum for the image subgroup.

This transports the native H.15.4(4) generation calculation to marked actions
without assuming surjectivity of the actor marking. Source: Aschbacher--Smith,
H.15.4(4), printed p.400, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows
open M22Quintet
variable {G H V W : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- The four-subgroup fixed span respects injective actor markings. -/
theorem fourFixedSpan_map_equivariant
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
    (f : G →* H) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (A : Subgroup G) :
    (fourFixedSpan ρ A).map E.toLinearMap = fourFixedSpan σ (A.map f) := by
  simp only [fourFixedSpan,Submodule.map_iSup,
    fixedSpace_map_equivariant ρ σ f E hE]
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hB => iSup_le fun hc => ?_
    let := hB
    exact le_iSup_of_le (B.map f) (le_iSup_of_le (map_mono hBA)
      (le_iSup_of_le (IsElementaryAbelian.map f)
        (le_iSup_of_le ((card_map_of_injective hf).trans hc) le_rfl)))
  · refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hB => iSup_le fun hc => ?_
    let C := B.comap f
    have hCB : C.map f = B := map_comap_eq_self (hBA.trans (map_le_range _ _))
    have hCA : C ≤ A := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hBA hx
      exact hf he ▸ hy
    let := hB
    have hC : IsElementaryAbelian 2 C := IsElementaryAbelian.comap_of_injective f hf B
    have hcard : Nat.card C = 4 := by
      rw [←card_map_of_injective (K := C) hf,hCB,hc]
    exact le_iSup_of_le C (le_iSup_of_le hCA (le_iSup_of_le hC
      (le_iSup_of_le hcard (by rw [hCB]))))

end MathieuCode.NormalizedShadowRows
