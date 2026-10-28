module
public import Theory.Representation.G2.RestrictedModules.NaturalHighestWeight
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.Representation.BinaryOffender.Defs
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Borel fixed vectors in the natural G₂ module

The trace-zero octonion quotient has six nonzero split-torus weights.
Two torus elements, formed from a nonidentity field unit, therefore annihilate
all six coordinates of a Borel-fixed vector when the field has more than two
elements. Scalar restriction gives the same statement on the binary module.

The terminal component sieve uses this calculation after genuine B.4.2 natural
recognition. Source: Aschbacher--Smith 14.6.20, printed p.1037, and B.4.2(4).
Octonion coordinates retain the ATLAS attribution of the imported modules;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BorelFixed
open Restricted.NaturalCoordinates
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual marked Borel fixes only zero on the natural octonion quotient. -/
theorem fixed_eq_zero (hF : 2 < Nat.card F) (v : Natural.Space F)
    (hv : ∀ b ∈ borel (K := F), Natural.action F b v = v) : v = 0 := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨t, ht⟩ := exists_ne (1 : Fˣ)
  have ht' : (t : F) ≠ 1 := fun he => ht (Units.ext he)
  let w := equiv F v
  have hfix (l m : Fˣ) : Restricted.NaturalCoordinates.action F (torus l m) w = w := by
    change equiv F (Natural.action F (torus l m) ((equiv F).symm (equiv F v))) = equiv F v
    rw [LinearEquiv.symm_apply_apply]
    exact congrArg (equiv F) (hv _ (mem_sup_right ⟨(l,m),rfl⟩))
  have hh : ∀ c : F, c ≠ 1 → ∀ x : F, c * x = x → x = 0 := by
    intro c hc x hx
    exact (mul_eq_zero.mp (show (c - 1) * x = 0 by rw [sub_mul,one_mul,hx,sub_self])).resolve_left
      (sub_ne_zero.mpr hc)
  have hti : ((t⁻¹ : Fˣ) : F) ≠ 1 := by
    intro he
    apply ht
    apply inv_eq_one.mp
    exact Units.ext he
  have h0 : w 0 = 0 := hh _ ht' _ (by simpa [action_torus] using congrFun (hfix t 1) 0)
  have h1 : w 1 = 0 := hh _ ht' _ (by simpa [action_torus] using congrFun (hfix 1 t) 1)
  have h2 : w 2 = 0 := hh _ ht' _ (by simpa [action_torus] using congrFun (hfix t 1) 2)
  have h3 : w 3 = 0 := hh _ hti _ (by simpa [action_torus] using congrFun (hfix t 1) 3)
  have h4 : w 4 = 0 := hh _ hti _ (by simpa [action_torus] using congrFun (hfix 1 t) 4)
  have h5 : w 5 = 0 := hh _ hti _ (by simpa [action_torus] using congrFun (hfix t 1) 5)
  apply (equiv F).injective
  rw [map_zero]
  change w = 0
  ext i
  fin_cases i <;> assumption

/-- Forgetting the extension-field scalars preserves Borel fixed-space vanishing. -/
theorem fixedSpace_eq_bot [Algebra (ZMod 2) F] (hF : 2 < Nat.card F) :
    fixedSpace ((Natural.action F).restrictScalars (k := ZMod 2)) (borel (K := F)) = ⊥ := by
  apply bot_unique
  intro v hv
  exact fixed_eq_zero hF v (fun b hb => hv ⟨b,hb⟩)

end Atlas.G2.Natural.BorelFixed
