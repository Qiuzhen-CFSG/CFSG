module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Data

/-! The explicit field-twisted projective matrix lies in the actual mixed
outer subgroup PGL₂*(F25). Its square and both conjugation equations are
proved from the checked matrix data, retaining the native max4 words.
Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

@[expose] public section
open Subgroup Matrix
noncomputable section
namespace Tits.Max4Outer.Mixed
open Max4Projective GorensteinWalter

def iota : PSL →* PGammaL2 F :=
  SemidirectProduct.inl.comp Matrix.ProjectiveSpecialLinearGroup.toPGL

def delta : PGammaL2 F := ⟨ProjGenLinGroup.mk M,sigma⟩

def z : PGL2 F ⧸ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
  QuotientGroup.mk (ProjGenLinGroup.mk M)

theorem z_ne : z≠1 := by
  intro hz
  have hm := (QuotientGroup.eq_one_iff (ProjGenLinGroup.mk M)).mp hz
  have hd := (pgl2_mk_mem_psl2_range_iff_det_isSquare M).mp hm
  exact matrix_det_not_square hd

def plus : Subgroup (PGammaL2 F) := pgl2TwistedSubgroup F z sigma
abbrev Plus := ↥plus

theorem psl_le_plus : pGammaL2PSLRange F≤plus := pgl2Twisted_psl_le z sigma

theorem delta_mem : delta∈plus := by
  change pGammaL2OuterProduct F delta∈zpowers (z,sigma)
  change (z,sigma)∈zpowers (z,sigma)
  exact mem_zpowers _

theorem delta_not_psl : delta∉pGammaL2PSLRange F := by
  rintro ⟨x,hx⟩
  have h := congrArg (fun a : PGammaL2 F => a.right) hx
  exact sigma_ne h.symm

def outside : Plus := ⟨delta,delta_mem⟩
def pslCore : Subgroup Plus := (pGammaL2PSLRange F).subgroupOf plus

instance pslCore_normal : pslCore.Normal := by
  dsimp [pslCore,plus]
  exact pgl2Twisted_psl_normal z sigma

theorem pslCore_index : pslCore.index=2 := pgl2Twisted_psl_relIndex z sigma z_ne sigma_order

theorem outside_not_core : outside∉pslCore := delta_not_psl

def pslCoreEquiv : PSL ≃* pslCore :=
  (pGammaL2PSLRangeEquiv F).trans (subgroupOfEquivOfLe psl_le_plus).symm

theorem pslCoreEquiv_coe (x : PSL) : ((pslCoreEquiv x : pslCore) : Plus).val=iota x := rfl

private theorem pgl_eq_of_neg (x y : GeneralLinearGroup (Fin 2) F)
    (h : x.val = -y.val) : ProjGenLinGroup.mk x=ProjGenLinGroup.mk y := by
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨-1,?_⟩
  apply Units.ext
  change x.val * Matrix.diagonal (fun _=> (-1 : F))=y.val
  rw [← Matrix.smul_eq_mul_diagonal,h]
  simp

theorem delta_action (i : Fin 2) : delta*iota (pi (slGen i))=
    iota (pi (slWord (actionWord i)))*delta := by
  apply SemidirectProduct.ext
  · change ProjGenLinGroup.mk M * pgl2FieldAut F sigma
      (ProjGenLinGroup.mk (SpecialLinearGroup.toGL (slGen i))) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL (slWord (actionWord i)))*
      pgl2FieldAut F 1 (ProjGenLinGroup.mk M)
    rw [map_one]
    change ProjGenLinGroup.mk M * pgl2RingEquiv sigma
      (QuotientGroup.mk' (center _) (SpecialLinearGroup.toGL (slGen i))) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL (slWord (actionWord i)))*ProjGenLinGroup.mk M
    rw [pgl2RingEquiv_mk]
    change ProjGenLinGroup.mk M * ProjGenLinGroup.mk
      (GeneralLinearGroup.map sigma.toRingHom (SpecialLinearGroup.toGL (slGen i))) = _
    rw [← map_mul,← map_mul]
    by_cases hi : i=0
    · apply pgl_eq_of_neg
      exact (action_matrix i).trans (if_pos hi)
    · apply congrArg ProjGenLinGroup.mk
      apply Units.ext
      exact (action_matrix i).trans (if_neg hi)
  · change sigma*1=1*sigma
    simp

def squareScalar : Fˣ := Units.mk0 (⟨1,3⟩ : F) (by decide +kernel)

theorem delta_square : delta^2=iota (pi (slWord inverseSquareWord)) := by
  rw [pow_two]
  apply SemidirectProduct.ext
  · change ProjGenLinGroup.mk M*pgl2FieldAut F sigma (ProjGenLinGroup.mk M)=
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL (slWord inverseSquareWord))
    change ProjGenLinGroup.mk M*pgl2RingEquiv sigma (QuotientGroup.mk' (center _) M)=_
    rw [pgl2RingEquiv_mk]
    change ProjGenLinGroup.mk M*ProjGenLinGroup.mk (GeneralLinearGroup.map sigma.toRingHom M)=_
    rw [← map_mul]
    symm
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨squareScalar,?_⟩
    apply Units.ext
    change (slWord inverseSquareWord).val*Matrix.diagonal (fun _=>(⟨1,3⟩ : F))=
      matrix*matrix.map sigma
    rw [← Matrix.smul_eq_mul_diagonal,square_matrix]
  · change sigma*sigma=1
    exact sigma_square

end Tits.Max4Outer.Mixed
