module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Bray.Checks
public import Theory.GroupAction.PackedPermutation.Checkpoints
/-!
# Actual centralizing Bray words

The checked tables return each fifth power to the identity and identify both
Bray action tables. Generic checkpoint soundness transports these calculations
to the original ATLAS carrier, so the elementary Bray identity yields actual
centralizing elements. No abstract replacement group is introduced.
-/
public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Bray
open Theory.GroupAction.PackedPermutation Networks
private theorem ramp_fields (i : Fin 524288) : get 19 (ramp 19 524288) i = i.val :=
  get_ramp (by decide) (by decide) i.isLt

theorem permK0_five : permK0^5=1 :=
  fifth_power_of_checkpoints 19 524288 netK0 netK0_valid
    (ramp 19 524288) tableK0p1 tableK0p2 tableK0p3 tableK0p4 ramp_fields
    runK0p1 runK0p2 runK0p3 runK0p4 runK0p5

theorem k0_five : k0^5=1 := (k0_intertwines.pow 5).eq_one permK0_five

theorem h0_centralizes : Commute a h0 := h0_commute k0_five

theorem tableH0_get (x : Fin 524288) :
    get 19 tableH0 x = ((permG0*permK0^2) x).val :=
  product_square_of_named_checkpoints 19 524288 netG0 netK0 netG0_valid netK0_valid
    permG0 permK0 rfl rfl
    (ramp 19 524288) tableG0 tableGK0 tableH0 ramp_fields runG0 runGK0 runH0 x

theorem h0_table (x : Fin 306936) :
    (inclusion h0 x).val = get 19 tableH0 x := by
  have H := congrArg (fun y : Fin 524288 => y.val)
    ((g0_intertwines.mul (k0_intertwines.pow 2)) x)
  calc
    (inclusion h0 x).val = ((permG0*permK0^2) (Fin.castLE (by decide) x)).val := H
    _ = get 19 tableH0 x := (tableH0_get (Fin.castLE (by decide) x)).symm

theorem permK1_five : permK1^5=1 :=
  fifth_power_of_checkpoints 19 524288 netK1 netK1_valid
    (ramp 19 524288) tableK1p1 tableK1p2 tableK1p3 tableK1p4 ramp_fields
    runK1p1 runK1p2 runK1p3 runK1p4 runK1p5

theorem k1_five : k1^5=1 := (k1_intertwines.pow 5).eq_one permK1_five

theorem h1_centralizes : Commute a h1 := h1_commute k1_five

theorem tableH1_get (x : Fin 524288) :
    get 19 tableH1 x = ((permG1*permK1^2) x).val :=
  product_square_of_named_checkpoints 19 524288 netG1 netK1 netG1_valid netK1_valid
    permG1 permK1 rfl rfl
    (ramp 19 524288) tableG1 tableGK1 tableH1 ramp_fields runG1 runGK1 runH1 x

theorem h1_table (x : Fin 306936) :
    (inclusion h1 x).val = get 19 tableH1 x := by
  have H := congrArg (fun y : Fin 524288 => y.val)
    ((g1_intertwines.mul (k1_intertwines.pow 2)) x)
  calc
    (inclusion h1 x).val = ((permG1*permK1^2) (Fin.castLE (by decide) x)).val := H
    _ = get 19 tableH1 x := (tableH1_get (Fin.castLE (by decide) x)).symm
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Bray
