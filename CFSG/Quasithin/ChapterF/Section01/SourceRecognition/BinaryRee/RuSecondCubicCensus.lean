module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondNativeCubic
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCensus

/-!
# The cubic centralizer bound on the original second core

Transport the native bound through the actual A coordinates and the original
X conjugation. The existence theorem selects X and its generator using the
preceding source construction; no automorphism-census hypothesis is required.

Source: the binary Ree branch of Aschbacher–Smith F.1.12 applied in J.4.5.
This is an input to the remaining extension classification.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.secondCoreAction_centralizer_card_le (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hmodel:Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)))
    (e:p.A B5≃*ReeTwo.SylowModel.firstParabolicCore) (x:X) (hx:orderOf x=3) :
    Nat.card {α:MulAut (p.A B5) //
      Commute α ((p.A B5).normalizerMonoidHom (inclusion (p.A_normalized B5) (x:p.parabolic)))}≤48 := by
  let ec:=MulAut.congr e
  let a:MulAut (p.A B5):=(p.A B5).normalizerMonoidHom
    (inclusion (p.A_normalized B5) (x:p.parabolic))
  let eqv : {α:MulAut (p.A B5) // Commute α a}≃
      {α:MulAut ReeTwo.SylowModel.firstParabolicCore // Commute α (ec a)} :=
    Equiv.subtypeEquiv ec.toEquiv (fun _=>(commute_map_iff ec.injective).symm)
  rw [Nat.card_congr eqv]
  exact ReeTwo.SylowModel.CubicAction.cubic_centralizer_card_le
    (secondCoreAction B5 e (x:p.parabolic))
    (s.secondCoreAction_order_three B5 hi X hmodel e x hx)

theorem SourceChoice.exists_A_cubic_centralizer_bound (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(X:Sylow 3 p.parabolic) (x:X),
      Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)) ∧
      orderOf x=3 ∧ Nat.card {α:MulAut (p.A B5) //
        Commute α ((p.A B5).normalizerMonoidHom (inclusion (p.A_normalized B5) (x:p.parabolic)))}≤48 := by
  obtain ⟨X,e,x,hm,hx,_⟩:=s.exists_A_native_cubic_marking B5 hi
  exact ⟨X,x,hm,hx,s.secondCoreAction_centralizer_card_le B5 hi X hm e x hx⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
