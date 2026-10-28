module
public import Stellmacher.SectionTen.TenOneLargeTerminalCoreFixed
public import Stellmacher.SectionTen.TenOneLargeGeneratedTerminalIntersection
public import Stellmacher.SectionTen.TenOneLargeTerminalIrreducible

/-!
# A noncentral fixed terminal factor prevents full quotient action

In the actual large Section Ten branch, let D lie in the terminal
stabilizer and let F be a D-fixed subgroup of the terminal module not
contained in its center. The terminal residual core cannot equal the
join of its D-commutator and the terminal module.

The three-subgroups lemma makes [U,D] centralize F: [F,U] lies in the
terminal center, which D centralizes, and D already centralizes F. The
terminal module is elementary abelian, so the asserted join would make
all of U centralize F. The proved equality C_V(U)=Z contradicts F≰Z.
No odd-order or source-(18) quotient assumption is required here.

This is the transfer needed after (18) in Stellmacher (10.1), printed
p.64. The stated join is exactly what coprime fixed-point decomposition
provides when the quotient has no fixed point; the stronger printed
identity [U,D]=U is not required.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_terminal_factor_not_full
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (D F : Subgroup G)
    (hDP : D≤GAt ctx.Γ ctx.criticalPath.a')
    (hFV : F≤VAt ctx.Γ ctx.criticalPath.a')
    (hFD : F≤Subgroup.centralizer (D:Set G))
    (hnot : ¬F≤ZAt ctx.Γ ctx.criticalPath.a') :
    twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ≠
      ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'),D⁆ ⊔ VAt ctx.Γ ctx.criticalPath.a' := by
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hUQ : U≤Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVU : ⁅V,U⁆≤Z := (Subgroup.commutator_mono le_rfl hUQ).trans_eq
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
      ctx.criticalPath.a' ⟨alignment,halign⟩).2.1
  have hZD : ⁅Z,D⁆=⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mp (hDP.trans (nine_next_center_centralizes_stabilizer
      ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' ⟨alignment,halign⟩)))
  have hFDzero : ⁅F,D⁆=⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFD
  have htriple : ⁅⁅U,D⁆,F⁆=⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate
    (by rw [Subgroup.commutator_comm D F,hFDzero,Subgroup.commutator_bot_left])
    (by
      apply bot_unique
      exact (Subgroup.commutator_mono ((Subgroup.commutator_mono hFV le_rfl).trans hVU)
        le_rfl).trans hZD.le)
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  have hVcomm : IsElementaryAbelian 2 V := by
    change IsElementaryAbelian 2 (v ctx.Γ ctx.criticalPath.a')
    rw [←halign,v_act]
    exact IsElementaryAbelian.map (MulAut.conj alignment⁻¹).toMonoidHom
  let _ := hVcomm
  have hVF : V≤Subgroup.centralizer (F:Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact congrArg Subtype.val (mul_comm (⟨f,hFV hf⟩:V) ⟨v,hv⟩)
  intro hfull
  have hUF : U≤Subgroup.centralizer (F:Set G) := hfull.le.trans
    (sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp htriple) hVF)
  apply hnot
  exact (le_inf hFV (Subgroup.le_centralizer_iff.mp hUF)).trans
    (ten_one_large_terminal_core_fixed_line ctx middle hpath hno).le

end Stellmacher.SectionTen
