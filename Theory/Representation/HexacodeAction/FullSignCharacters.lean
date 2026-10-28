module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeConjugation
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The intrinsic sign of every six-letter quotient

Every surjective sign character of the full hexacode actor kills its central
cubic and descends to S6. Uniqueness of the symmetric-group sign identifies
it with the intrinsic hexacode sign. Thus any surjective six-letter marking
preserves parity, including an exceptional marking.

Source application: the even and odd transverse lifts in
Aschbacher--Smith12.7.19, printed p.846.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode

/-- Every nontrivial sign character is the intrinsic hexacode sign. -/
theorem eq_hexSign_of_surjective (f : HexAutomorphisms →* ℤˣ)
    (hf : Function.Surjective f) : f=hexSign := by
  have hz : f hexZ=1 := by
    have h3 : f hexZ^3=1 := by rw [←map_pow,hexZ_cube,map_one]
    rcases Int.units_eq_one_or (f hexZ) with h | h
    · exact h
    · rw [h] at h3
      norm_num at h3
  have hk : hexCoordinateSixHom.ker ≤ f.ker := by
    rw [hexCoordinateSix_kernel]
    exact zpowers_le.mpr hz
  let χ := hexCoordinateSixHom.liftOfSurjective hexCoordinateSix_surjective ⟨f,hk⟩
  have he (g : HexAutomorphisms) : χ (hexCoordinateSixHom g)=f g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hχ : Function.Surjective χ := by
    intro y
    obtain ⟨g,rfl⟩ := hf y
    exact ⟨hexCoordinateSixHom g,he g⟩
  have hs : χ=Equiv.Perm.sign := Equiv.Perm.eq_sign_of_surjective_hom hχ
  ext g
  rw [←he,hs]
  rfl

/-- Any surjective six-letter marking of the full actor has the same parity. -/
theorem six_quotient_sign (f : HexAutomorphisms →* Equiv.Perm (Fin 6))
    (hf : Function.Surjective f) (g : HexAutomorphisms) :
    Equiv.Perm.sign (f g)=hexSign g := by
  have hs : Function.Surjective (Equiv.Perm.sign.comp f) := by
    intro y
    obtain ⟨p,hp⟩ := Equiv.Perm.sign_surjective (Fin 6) y
    obtain ⟨x,hx⟩ := hf p
    refine ⟨x,?_⟩
    change Equiv.Perm.sign (f x)=y
    rw [hx]
    exact hp
  exact DFunLike.congr_fun (eq_hexSign_of_surjective (Equiv.Perm.sign.comp f) hs) g

end Representation.Hexacode
