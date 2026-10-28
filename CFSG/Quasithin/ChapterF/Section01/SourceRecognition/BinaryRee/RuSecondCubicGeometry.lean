module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicCensus
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer

/-!
# Exact cubic geometry on the original second core

The source-selected X generator acts on the unchanged A with centralizer of
order 48 in Aut(A), exactly eight fixed elements, and no nontrivial fixed
central element. The proof uses the constructed native cubic marking and
retains the literal original conjugation homomorphism.

Source: Aschbacher–Smith J.4.4–5, supplying the binary Ree F.1.12 extension
calculation. No endpoint isomorphism or extension-classification premise is used.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

@[expose] def secondCoreSourceAction (B5:Sylow 5 d.toTypeRuSetup.H) :
    p.parabolic→*MulAut (p.A B5) :=
  (p.A B5).normalizerMonoidHom.comp (inclusion (p.A_normalized B5))

/-- Exact cubic centralizer and fixed-point geometry on the original A. -/
theorem SourceChoice.exists_A_cubic_automorphism_geometry (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(X:Sylow 3 p.parabolic) (x:X),
      Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)) ∧
      orderOf x=3 ∧
      Nat.card {α:MulAut (p.A B5) // Commute α (secondCoreSourceAction B5 (x:p.parabolic))}=48 ∧
      Nat.card {a:p.A B5 // secondCoreSourceAction B5 (x:p.parabolic) a=a}=8 ∧
      ∀a:p.A B5,a∈center (p.A B5)→secondCoreSourceAction B5 (x:p.parabolic) a=a→a=1 := by
  obtain ⟨X,e,x,hm,hx,hact⟩:=s.exists_A_native_cubic_marking B5 hi
  let δ:=secondCoreSourceAction B5 (x:p.parabolic)
  let ec:=MulAut.congr e
  have he (a:p.A B5) : e (δ a)=ReeTwo.SylowModel.CubicAction.cubic (e a) := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change ((x:p.parabolic):G)*(a:G)*((x:p.parabolic):G)⁻¹=_
    rw [hact,e.symm_apply_apply]
  have hγ:ec δ=ReeTwo.SylowModel.CubicAction.cubic := by
    apply MulEquiv.ext
    intro b
    change e (δ (e.symm b))=_
    rw [he,e.apply_symm_apply]
  have hC:Nat.card {α:MulAut (p.A B5) // Commute α δ}=48 := by
    let eqv : {α:MulAut (p.A B5) // Commute α δ}≃
        {α:MulAut ReeTwo.SylowModel.firstParabolicCore // Commute α (ec δ)} :=
      Equiv.subtypeEquiv ec.toEquiv (fun _=>(commute_map_iff ec.injective).symm)
    rw [Nat.card_congr eqv,hγ]
    exact ReeTwo.SylowModel.CubicAction.cubic_centralizer_card
  have hF:Nat.card {a:p.A B5 // δ a=a}=8 := by
    let eqv : {a:p.A B5 // δ a=a}≃
        {a:ReeTwo.SylowModel.firstParabolicCore // ReeTwo.SylowModel.CubicAction.cubic a=a} :=
      Equiv.subtypeEquiv e.toEquiv (fun a=>by
        change δ a=a ↔ ReeTwo.SylowModel.CubicAction.cubic (e a)=e a
        rw [←he a]
        exact e.injective.eq_iff.symm)
    exact (Nat.card_congr eqv).trans ReeTwo.SylowModel.CollectedBitVectors.cubic_fixed_card
  refine ⟨X,x,hm,hx,hC,hF,?_⟩
  intro a ha hf
  apply e.injective
  rw [map_one]
  apply ReeTwo.SylowModel.CollectedBitVectors.cubic_fixed_eq_one_of_commute
  · rw [←he,hf]
  · have hc:Commute a (e.symm (ReeTwo.SylowModel.CubicAction.orbit 0)) :=
      (mem_center_iff.mp ha _).symm
    have hh:=hc.map e.toMonoidHom
    change Commute (e a) (e (e.symm (ReeTwo.SylowModel.CubicAction.orbit 0))) at hh
    simpa only [e.apply_symm_apply] using hh

end CFSG.Quasithin.ChapterJ.RuSubgroup
