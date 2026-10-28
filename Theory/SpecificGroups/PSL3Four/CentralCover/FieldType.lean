module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.SpecificGroups.PSL3Four.OuterPlane.FieldOccurrence
public import Theory.SpecificGroups.PSL3Four.CentralCover.AutomorphismLifting
public import Theory.GroupTheory.PerfectCentralCoverFixedResidual
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
import all Theory.SpecificGroups.PSL3Four.OuterPlane.FieldOccurrence
import all Theory.SpecificGroups.PSL3.ExtensionBorel

/-! An automorphism preserving an actual elementary sixteen in PSL₃(4)
preserves its parabolic type and is semilinear. In a central four-cover,
an involution preserving a full elementary sixty-four and moving the center
therefore descends to a conjugate of Frobenius. -/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.LinearThree.OuterExtensions

private theorem map_aut_mul (Q : Subgroup PSL) (a b : MulAut PSL) :
    Q.map (a*b).toMonoidHom = (Q.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

/-- Stabilizing any actual elementary sixteen preserves one parabolic type. -/
theorem stabilizes_elementary_sixteen_linearField
    (Q : Subgroup PSL) [IsElementaryAbelian 2 Q] (hQ : Nat.card Q=16)
    (a : MulAut PSL) (ha : Q.map a.toMonoidHom=Q) :
    a∈Matrix.PSL3.ExtensionBorel.linearField F := by
  obtain ⟨S,hQS⟩ := (IsElementaryAbelian.isPGroup 2 Q).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL S
    (unipotentSylow F (n := 2) (by decide) (by simpa using card_F))
  let c := MulAut.conj g
  have hS : (S:Subgroup PSL).map c.toMonoidHom=unipotent F :=
    congrArg Sylow.toSubgroup hg
  let Q' := Q.map c.toMonoidHom
  have hQ'U : Q'≤unipotent F := hS ▸ map_mono hQS
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.map _
  have hQ' : Nat.card Q'=16 := (card_map_of_injective c.injective).trans hQ
  obtain ⟨b,hb⟩ := FullPlaneNormalizer.elementary_plane Q' hQ'U hQ'
  let a' := c*a*c⁻¹
  have hac : Q'.map a'.toMonoidHom=Q' := by
    change (Q.map c.toMonoidHom).map (c*a*c⁻¹).toMonoidHom=Q.map c.toMonoidHom
    rw [map_aut_mul,map_aut_mul]
    have hi : (Q.map c.toMonoidHom).map (c⁻¹).toMonoidHom=Q := by
      rw [←map_aut_mul,inv_mul_cancel]
      exact Subgroup.map_id Q
    rw [hi,ha]
  have hp : (parabolic F b).map a'.toMonoidHom=parabolic F b := by
    rw [←normalizer_rootPlane,map_normalizer_eq_of_bijective (f := a'.toMonoidHom) _ a'.bijective,←hb,hac]
  have hlin : a'∈Matrix.PSL3.ExtensionBorel.linearField F :=
    (mapsParabolicType_self_iff_mem_linearField F (n:=2) (by decide)
      (by simpa using card_F) a' b).mp ⟨1,hp.trans (by rw [map_one]; exact (Subgroup.map_id _).symm)⟩
  have hc : c∈Matrix.PSL3.ExtensionBorel.linearField F :=
    (show Matrix.PSL3.OuterSolvable.innerDiagonal F≤Matrix.PSL3.ExtensionBorel.linearField F from le_sup_left)
      (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F ⟨g,rfl⟩)
  have he : a=c⁻¹*a'*c := by dsimp only [a']; group
  rw [he]
  exact (Matrix.PSL3.ExtensionBorel.linearField F).mul_mem
    ((Matrix.PSL3.ExtensionBorel.linearField F).mul_mem
      ((Matrix.PSL3.ExtensionBorel.linearField F).inv_mem hc) hlin) hc

/-- An automorphism of cube one is inner-diagonal, since the remaining
field-graph quotient has order dividing four. -/
theorem cube_one_mem_innerDiagonal (a : MulAut PSL) (ha : a^3=1) :
    a∈PSL3.OuterSolvable.innerDiagonal F := by
  let : (PSL3.OuterSolvable.innerDiagonal F).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (m:=2)
      (by decide) (by simpa using card_F)]
    exact PSL3.OuterSolvable.standard_le_normalizer_innerDiagonal (F:=F)
  let q := QuotientGroup.mk' (PSL3.OuterSolvable.innerDiagonal F)
  have h3 : orderOf (q a)∣3 := orderOf_dvd_of_pow_eq_one
    (by rw [←map_pow,ha,map_one])
  have h4 : orderOf (q a)∣4 := (orderOf_dvd_natCard (q a)).trans
    OuterThreeStructure.diagonal_index_dvd_four
  have ho : orderOf (q a)=1 := Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 4) h3 h4
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp ho)

/-- Moving the covering center excludes inner descent. Together with the
preserved elementary sixty-four, this forces the field involution class. -/
theorem FourCover.involution_stabilizes_sixtyfour_is_field
    {E : Type*} [Group E] [Finite E] (c : FourCover E)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hZQ : center E≤Q) (hQ : Nat.card Q=64)
    (a : MulAut E) (ha : a^2=1) (hQa : Q.map a.toMonoidHom=Q)
    (hmove : ∃ z : center E, a z≠z) :
    IsConj (c.toCover.autMap c.ker_eq_center a) pslFrobenius := by
  let f := c.toMonoidHom
  let β := c.toCover.autMap c.ker_eq_center a
  let Q' := Q.map f
  let := c.center_isKleinFour
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.map _
  have hQ' : Nat.card Q'=16 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map Q f
    rw [inf_eq_right.mpr (c.ker_eq_center ▸ hZQ),c.ker_eq_center,
      IsKleinFour.card_four,hQ] at hh
    change 4*Nat.card Q'=64 at hh
    omega
  have hβ : Q'.map β.toMonoidHom=Q' := by
    calc
      _ = (Q.map a.toMonoidHom).map f := by
        rw [Subgroup.map_map,Subgroup.map_map]
        congr 1
        ext x
        exact c.toCover.autMap_apply c.ker_eq_center a x
      _ = Q' := by rw [hQa]
  have hlin := stabilizes_elementary_sixteen_linearField Q' hQ' β hβ
  have houter : β∉MulAut.innerSubgroup PSL := by
    intro hi
    obtain ⟨y,hy⟩ := hi
    obtain ⟨x,hx⟩ := (c.toCover.autMap_inner_iff c.ker_eq_center a).mp ⟨y,hy.symm⟩
    obtain ⟨z,hz⟩ := hmove
    apply hz
    rw [hx]
    change x*(z:E)*x⁻¹=(z:E)
    rw [mem_center_iff.mp z.property x,mul_inv_cancel_right]
  obtain ⟨d,hd⟩ := OuterPlane.FieldOccurrence.linearField_outer_involution_conjugate β
    (by exact hlin) (by change (c.toCover.autMap c.ker_eq_center a)^2=1; rw [←map_pow,ha,map_one]) houter
  exact isConj_iff.mpr ⟨d,hd⟩

end Matrix.PSL3Four
