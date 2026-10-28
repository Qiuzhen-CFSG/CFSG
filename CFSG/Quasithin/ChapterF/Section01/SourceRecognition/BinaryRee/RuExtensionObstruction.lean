module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuMiddleCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuMovingPoint
public import Theory.SpecificGroups.ReeTwo.InvertingExtensionFirstCore
public import Theory.SpecificGroups.ReeTwo.FixingNonstandardFirstCore
public import Theory.SpecificGroups.ReeTwo.FixingModelSplitTwo

/-!
# The actual second endpoint excludes the bad first-core extensions

Conjugacy inside F₁ transports every order-4096 candidate to the unchanged
middle. Its intrinsic second core is the original A, whose automorphisms
move the original central point. This contradicts the marked fixed-point
certificates for every inverting, nonsplit, and nonstandard fixing extension.
Consequently the original generated extension is split and has a standard
fixing action. The source central marking and literal ambient subgroup
inclusions are retained throughout.

Source: Aschbacher–Smith J.4.5 and the verified Shinoda action census used
in the binary Ree branch of F.1.12.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- No order-4096 subgroup in the actual first endpoint can have a fixed
original point under every automorphism of its intrinsic second core. -/
theorem SourceChoice.not_intrinsic_point_fixed (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (S:Subgroup G) (hSF:S≤p.F₁ B5) (hS:Nat.card S=4096)
    (z:S) (hzgen:zpowers (z:G)=d.toTypeRuSetup.Z)
    (hz:z∈ReeTwo.InvertingExtension.firstCore S) :
    ¬∀α:MulAut (ReeTwo.InvertingExtension.firstCore S),α ⟨z,hz⟩=⟨z,hz⟩ := by
  intro hfix
  obtain ⟨h,hh⟩:=s.conjugate_to_T_F B5 hi S hSF hS
  let M:=p.T_F B5
  let e:S≃*M:=((MulAut.conj (h:G)).subgroupMap S).trans (MulEquiv.subgroupCongr hh)
  let I:=ReeTwo.InvertingExtension.firstCore M
  let eI:ReeTwo.InvertingExtension.firstCore S≃*I:=
    Subgroup.centralizerUpperCentralSeriesEquiv e 2
  have hIA:I.map M.subtype=p.A B5:=s.T_F_intrinsic_A B5 hi
  let eA:I≃*p.A B5:=(I.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hIA)
  let E:=eI.trans eA
  let zI:ReeTwo.InvertingExtension.firstCore S:=⟨z,hz⟩
  have hzZ:(z:G)∈d.toTypeRuSetup.Z:=hzgen ▸ mem_zpowers (z:G)
  have hval:(E zI:G)=(z:G):=by
    change (h:G)*(z:G)*(h:G)⁻¹=(z:G)
    apply mul_inv_eq_iff_eq_mul.mpr
    exact ((p.F₁_le_H B5 h.property) z hzZ).symm
  have hmark:zpowers (E zI:G)=d.toTypeRuSetup.Z:=by rw [hval];exact hzgen
  obtain ⟨α,hα⟩:=s.exists_A_moving_point B5 hi (E zI) hmark
  have hf:=hfix (E.trans (α.trans E.symm))
  change E.symm (α (E zI))=zI at hf
  have he:=congrArg E hf
  exact hα (by simpa only [E.apply_symm_apply] using he)

/-- The actual second endpoint excludes every inverting, nonsplit, or
nonstandard cyclic-four extension of the marked core. -/
theorem SourceChoice.firstCore_extension_standard (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (S:Subgroup G) (hSF:S≤p.F₁ B5) (hS:Nat.card S=4096)
    (j:ReeTwo.Core→*S) (g:S) (β:MulAut ReeTwo.Core)
    (hzgen:zpowers (j (ReeTwo.Core.root 9):G)=d.toTypeRuSetup.Z)
    (hgen:j.range⊔zpowers g=⊤)
    (hsq:β*ReeTwo.Core.c*β⁻¹=ReeTwo.Core.c^2)
    (hconj:∀q,g*j q*g⁻¹=j (β q))
    (hfour:g^4=1 ∨ g^4=j (ReeTwo.Core.root 9)) :
    g^4=1 ∧ β (ReeTwo.Core.root 2)=ReeTwo.Core.root 2 ∧
      ∃i:Fin 20,ReeTwo.Core.FixingActionCensus.IsStandard i ∧
        β=ReeTwo.Core.FixingActionCensus.representative i := by
  have hb4:=ReeTwo.Core.squaring_action_four β hsq
  have hfix:β (ReeTwo.Core.root 2)=ReeTwo.Core.root 2:=by
    rcases ReeTwo.Core.squaring_action_root_two β hsq with h | h
    · exact h
    · obtain ⟨hz,hall⟩:=ReeTwo.InvertingExtension.root_nine_firstCore_obstruction
        hS j g β hgen hb4 hsq h hconj hfour
      exact (s.not_intrinsic_point_fixed B5 hi S hSF hS (j (ReeTwo.Core.root 9)) hzgen hz hall).elim
  have hg4:g^4=1:=by
    rcases hfour with h | h
    · exact h
    · obtain ⟨hz,hall⟩:=ReeTwo.FixingExtension.root_nine_firstCore_obstruction
        hS j g β hgen hb4 hsq hfix hconj h
      exact (s.not_intrinsic_point_fixed B5 hi S hSF hS (j (ReeTwo.Core.root 9)) hzgen hz hall).elim
  obtain ⟨i,hiβ⟩:=ReeTwo.Core.FixingActionCensus.exhaustive_of_conj_c_root_two β hsq hfix
  refine ⟨hg4,hfix,i,?_,hiβ⟩
  by_contra hbad
  have hconj':∀q,g*j q*g⁻¹=j (ReeTwo.Core.FixingActionCensus.representative i q):=by
    rw [←hiβ]
    exact hconj
  obtain ⟨hz,hall⟩:=ReeTwo.FixingExtension.nonstandard_firstCore_obstruction_of_two_certificate
    ReeTwo.FixingModel.two_false_fixed hS j g i hbad hgen hconj' hg4
  exact s.not_intrinsic_point_fixed B5 hi S hSF hS (j (ReeTwo.Core.root 9)) hzgen hz hall

end CFSG.Quasithin.ChapterJ.RuSubgroup
