module
public import Theory.Representation.PSL3Two.NaturalDualMarking

/-!
# The natural fixed line in a binary point parabolic

Every Sylow two-subgroup of a surjective point-parabolic action fixes only
zero and the distinguished natural point. The normal four-group is contained
in the Sylow image; its two elementary matrices force the other coordinates
to vanish. This works with an arbitrary kernel in the original acting group.

Source application: Aschbacher--Smith, 14.6.24 and the seed decomposition
on printed p.1042. The natural and dual actions retain the same marking.
-/

public section
open Subgroup Representation
open BinaryLinear.OuterCyclic
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace Matrix.PSL3Two.NaturalDualMarking
variable {J : Type*} [Group J] [Finite J]

/-- The full natural binary linear group has no nonzero fixed vector. -/
theorem natural_common_fixed_eq_zero (v : Space)
    (hv : ∀ g : BinaryLinear.GL Space, g v = v) : v = 0 := by
  have hcalc : ∀ w : Space,
      slEquivLinear 3 (Bruhat.upper 1) w = w →
      slEquivLinear 3 (Bruhat.upper 2) w = w →
      slEquivLinear 3 (Bruhat.perm 2) w = w → w = 0 := by
    decide +kernel
  exact hcalc v (hv _) (hv _) (hv _)

theorem natural_sylow_fixed_zero_or_point (f : J →* SL)
    (hf : f.range = pointParabolicSL) (S : Sylow 2 J) (v : Space)
    (hv : ∀ s : J, s ∈ (S : Subgroup J) → slEquivLinear 3 (f s) v = v) :
    v = 0 ∨ v = ![1,0,0] := by
  let g : J →* pointParabolicSL := f.codRestrict pointParabolicSL (fun x => by
    rw [← hf]; exact ⟨x,rfl⟩)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y,hy⟩ := (show (x : SL) ∈ f.range by rw [hf]; exact x.property)
    exact ⟨y,Subtype.ext hy⟩
  let S' := S.mapSurjective hg
  have hcore : pointV ≤ (S : Subgroup J).map f := by
    rw [← MarkedProduct.pointParabolic_core]
    have he := map_mono (f := pointParabolicSL.subtype)
      (pCore_isPGroup.le_sylow_of_normal S')
    change (pCore 2 pointParabolicSL).map pointParabolicSL.subtype ≤ _
    simpa only [S',Sylow.coe_mapSurjective,Subgroup.map_map,
      show pointParabolicSL.subtype.comp g = f from rfl] using he
  have hfix (a : SL) (ha : a ∈ pointV) : slEquivLinear 3 a v = v := by
    obtain ⟨s,hs,rfl⟩ := hcore ha
    exact hv s hs
  have hcalc : ∀ w : Space,
      slEquivLinear 3 (Bruhat.upper 1) w = w →
      slEquivLinear 3 (Bruhat.upper 2) w = w → w = 0 ∨ w = ![1,0,0] := by
    decide +kernel
  exact hcalc v (hfix (Bruhat.upper 1) (by decide)) (hfix (Bruhat.upper 2) (by decide))

end Matrix.PSL3Two.NaturalDualMarking
