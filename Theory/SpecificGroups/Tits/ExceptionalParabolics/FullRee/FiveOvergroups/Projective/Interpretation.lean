module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Data

/-! Actual projective generators and representatives interpreting the raw transfer witnesses. Inversion and identity use their original SL₂ lifts. -/

@[expose] public section
open Theory.GroupTheory
namespace Tits.Max4Projective
open Tits.MinimumIndexCandidates.OrderCertificate.Max4

theorem raw_sl_inv (x : Raw) (hx : x.det=1) (hi : x.inv.det=1) :
    x.inv.sl hi = (x.sl hx)⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change !![x.d,-x.b;-x.c,x.a]=(!![x.a,x.b;x.c,x.d]:Matrix (Fin 2) (Fin 2) F).adjugate
  exact (Matrix.adjugate_fin_two_of _ _ _ _).symm

def target0Gen (i:Fin 4) : PSL := pi ((raw0Gen i).sl (raw0Gen_det i))
def target1Gen (i:Fin 4) : PSL := pi ((raw1Gen i).sl (raw1Gen_det i))
def target2Gen (i:Fin 2) : PSL := pi ((raw2Gen i).sl (raw2Gen_det i))
def target3Gen (i:Fin 0) : PSL := Fin.elim0 i

theorem target0Inv (i:Fin 4) : target0Gen (L0Inv i)=(target0Gen i)⁻¹ := by
  have he : ∀i,raw0Gen (L0Inv i)=(raw0Gen i).inv := by decide +kernel
  have hi : ((raw0Gen i).inv).det=1 := by rw [← he];exact raw0Gen_det _
  have hh : (raw0Gen (L0Inv i)).sl (raw0Gen_det _) =
      ((raw0Gen i).inv).sl hi := by
    apply Subtype.ext
    exact congrArg Raw.matrix (he i)
  dsimp [target0Gen]
  rw [hh,raw_sl_inv,map_inv]
theorem target1Inv (i:Fin 4) : target1Gen (L1Inv i)=(target1Gen i)⁻¹ := by
  have he : ∀i,raw1Gen (L1Inv i)=(raw1Gen i).inv := by decide +kernel
  have hi : ((raw1Gen i).inv).det=1 := by rw [← he];exact raw1Gen_det _
  have hh : (raw1Gen (L1Inv i)).sl (raw1Gen_det _) =
      ((raw1Gen i).inv).sl hi := by
    apply Subtype.ext
    exact congrArg Raw.matrix (he i)
  dsimp [target1Gen]
  rw [hh,raw_sl_inv,map_inv]
theorem target2Inv (i:Fin 2) : target2Gen (L2Inv i)=(target2Gen i)⁻¹ := by
  have he : ∀i,raw2Gen (L2Inv i)=(raw2Gen i).inv := by decide +kernel
  have hi : ((raw2Gen i).inv).det=1 := by rw [← he];exact raw2Gen_det _
  have hh : (raw2Gen (L2Inv i)).sl (raw2Gen_det _) =
      ((raw2Gen i).inv).sl hi := by
    apply Subtype.ext
    exact congrArg Raw.matrix (he i)
  dsimp [target2Gen]
  rw [hh,raw_sl_inv,map_inv]
theorem target3Inv (i:Fin 0) : target3Gen (L3Inv i)=(target3Gen i)⁻¹ := Fin.elim0 i

def target0Rep (r:Fin 300) : PSL := pi ((raw0Rep r).sl (raw0Rep_det r))
def target1Rep (r:Fin 13) : PSL := pi ((raw1Rep r).sl (raw1Rep_det r))
def target2Rep (r:Fin 2) : PSL := pi ((raw2Rep r).sl (raw2Rep_det r))
theorem target0Rep_initial : target0Rep 0=1 := by
  have he : (raw0Rep 0).sl (raw0Rep_det 0)=1 := by apply Subtype.ext;decide +kernel
  exact (congrArg pi he).trans (map_one pi)
theorem target1Rep_initial : target1Rep 0=1 := by
  have he : (raw1Rep 0).sl (raw1Rep_det 0)=1 := by apply Subtype.ext;decide +kernel
  exact (congrArg pi he).trans (map_one pi)
theorem target2Rep_initial : target2Rep 0=1 := by
  have he : (raw2Rep 0).sl (raw2Rep_det 0)=1 := by apply Subtype.ext;decide +kernel
  exact (congrArg pi he).trans (map_one pi)
end Tits.Max4Projective
