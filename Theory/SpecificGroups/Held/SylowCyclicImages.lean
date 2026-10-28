module
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.FrattiniCoordinates
import all Theory.SpecificGroups.Held.SylowAutomorphismSolvability.FrattiniCoordinates

/-!
# Cyclic images of the actual Held Sylow subgroup

In the certified polycyclic sequence, nine generators square to one.
The last generator squares to the product of two conjugate involutions.
In any cyclic image those two involutions have equal images, so the last
image also squares to one. The checked generating theorem and Sylow
conjugacy give the assertion for every full Sylow subgroup of Held.

The Chapter6 common-container argument uses this to bound the outer image
of a hypothetical faithful Sylow action on Sp₄(4). The actual order-four
outer group cannot be its image. No new permutation computation is needed.
Source: the ATLAS HeG1-p2058B0 and HeG1-max3W1 words and their certified
relations in the imported modules, with original attribution retained;
Aschbacher–Smith A.3.12 and5.2.2, printed pp.47–48,648–649.
-/

public noncomputable section
open Subgroup
namespace Held

attribute [local irreducible] Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.pcGenerator

/-- Every cyclic image of a full Sylow two-subgroup has exponent dividing two. -/
theorem sylow_cyclic_image_square (S : Sylow 2 Held.He)
    {C : Type*} [Group C] [IsCyclic C] (f : S →* C) (x : S) : f x ^ 2 = 1 := by
  let : CommGroup C := IsCyclic.commGroup
  open Held.LocalPairs.SylowGeometry.Calculations in
  obtain ⟨P,hP⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  let e := (S.equiv P).trans (MulEquiv.subgroupCongr hP)
  let g := f.comp e.symm.toMonoidHom
  open Held.SylowAutomorphismSolvability.FrattiniCoordinates
    Held.LocalPairs.SylowGeometry.Calculations.TwoGroup in
  have hgen : ∀ i, g (pcElement i) ^ 2 = 1 := by
    have he : g (pcElement 1) = g (pcElement 2) := by
      have hh := pcGenerator_conjugate (9 : Fin 10) (1 : Fin 10) (by decide)
      have hv : pcElement 9 * pcElement 1 * (pcElement 9)⁻¹ = pcElement 2 :=
        Subtype.ext (by simpa only [pcElement,coe_mul,coe_inv,conjugateWord,pcProduct,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hh)
      have hg := congrArg g hv
      rw [map_mul,map_mul,map_inv,mul_comm (g (pcElement 9)) (g (pcElement 1)),
        mul_assoc,mul_inv_cancel,mul_one] at hg
      exact hg
    have hs (i : Fin 10) : pcElement i ^ 2 = ((sqWord i).map pcElement).prod :=
      Subtype.ext (by simpa only [pcElement,coe_pow,val_list_prod,List.map_map,Function.comp_def] using square_actual i)
    intro i
    rw [←map_pow,hs,map_list_prod]
    by_cases hi : i = 9
    · subst i
      simp only [sqWord,↓reduceIte,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
      rw [←he,←pow_two,←map_pow,hs]
      simp [sqWord]
    · simp [sqWord,hi]
  open Held.SylowAutomorphismSolvability.FrattiniCoordinates in
  have htop : (powMonoidHom 2 |>.comp g).ker = ⊤ := by
    apply top_unique
    rw [←generators_top]
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact hgen i
  have hh := (show e x ∈ (powMonoidHom 2 |>.comp g).ker from htop ▸ mem_top _)
  simpa [g] using hh

end Held
