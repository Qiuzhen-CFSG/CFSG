module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.Component
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterFirst
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterSecond
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut
/-!
# Literal local groups and common Sylow for F.6.18(13)

The marked outer Mathieu amalgam transports the original quaternion kernel,
normal C₄² subgroups and quotient maps to the source vertices. The ambient
Sylow condition then fixes its order at 128. After the independent component
catalogue identifies the central quotient as M₁₂, the center-free and ambient
extension results give every clause of the actual Aut(M₁₂) source row.

Source: Aschbacher–Smith, F.6.18(13), printed p.310. The central-quotient
premise is retained for its separate catalogue producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
private theorem transport_outer_extension {D M A B : Type*}
    [Group D] [Group M] [Group A] [Group B]
    (e : M ≃* D) (N : Subgroup M) [N.Normal]
    (jN : N ≃* A) (jQ : (M ⧸ N) ≃* B) :
    ∃ N' : Subgroup D, ∃ _ : N'.Normal,
      Nonempty (N' ≃* A) ∧ Nonempty ((D ⧸ N') ≃* B) := by
  let N' := N.map e.toMonoidHom
  let : N'.Normal := (inferInstance : N.Normal).map e.toMonoidHom e.surjective
  exact ⟨N', inferInstance, ⟨(e.subgroupMap N).symm.trans jN⟩,
    ⟨(QuotientGroup.congr N N' e rfl).symm.trans jQ⟩⟩
variable {G : Type*} [Group G] {G₁ G₂ : Subgroup G}
theorem outer_marked_extensions
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    (∃ N : Subgroup G₁, ∃ _ : N.Normal,
      Nonempty (QuaternionCentralProductData N) ∧
      Nonempty ((G₁ ⧸ N) ≃* DihedralGroup 6)) ∧
    (∃ N : Subgroup G₂, ∃ _ : N.Normal,
      Nonempty (N ≃* InnerSquare.C4Square) ∧
      ∃ K : Subgroup (G₂ ⧸ N), ∃ _ : K.Normal,
        Nonempty (K ≃* OuterSquare.C3 × InnerSquare.E4) ∧
        Nonempty (((G₂ ⧸ N) ⧸ K) ≃* OuterSquare.C2)) ∧
    (∃ N : Subgroup (G₁ ⊓ G₂ : Subgroup G), ∃ _ : N.Normal,
      Nonempty (N ≃* InnerSquare.C4Square) ∧
      Nonempty (((G₁ ⊓ G₂ : Subgroup G) ⧸ N) ≃* DihedralGroup 4)) ∧
    Nat.card (G₁ ⊓ G₂ : Subgroup G) = 128 := by
  obtain ⟨j⟩ := hM
  let e := ((j.trans GreenBook.AutMathieuTwelve.ambientIso.symm).trans
    GreenBook.AutMathieuTwelve.concreteIso).symm
  refine ⟨?_, ?_, transport_outer_extension e.middle OuterSquare.sylowRadical
    OuterSquare.sylowRadicalEquiv OuterSquare.sylowQuotientEquiv, ?_⟩
  · let N := OuterFirst.quaternionKernel.map e.left.toMonoidHom
    let : N.Normal := (inferInstance : OuterFirst.quaternionKernel.Normal).map
      e.left.toMonoidHom e.left.surjective
    exact ⟨N, inferInstance,
      ⟨OuterFirst.quaternionKernelData.map (e.left.subgroupMap _)⟩,
      ⟨(QuotientGroup.congr _ N e.left rfl).symm.trans OuterFirst.firstQuotientEquiv⟩⟩
  · let N := OuterSquare.localRadical.map e.right.toMonoidHom
    let : N.Normal := (inferInstance : OuterSquare.localRadical.Normal).map
      e.right.toMonoidHom e.right.surjective
    refine ⟨N, inferInstance,
      ⟨(e.right.subgroupMap _).symm.trans OuterSquare.localRadicalEquiv⟩, ?_⟩
    exact transport_outer_extension (QuotientGroup.congr _ N e.right rfl)
      OuterSquare.quotientTwelve OuterSquare.quotientTwelveEquiv OuterSquare.secondOuterQuotientEquiv
  · rw [Nat.card_congr e.middle.symm.toEquiv, SecondCoordinates.card_overlap innerModel]

universe u
variable {D H : Type u} [Group D] [Finite D] [Group H] [Finite H]
    {D₁ D₂ : Subgroup D}
theorem source_thirteen_of_mathieu_quotient
    (e : D ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple D₁ D₂)
    (hFstar : pResidual 2 D = generalizedFitting D)
    (hq : IsQuasisimple (pResidual 2 D))
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups D₁ (D₁ ⊓ D₂) D₂ inf_le_left inf_le_right))
    (j : ((pResidual 2 D) ⧸ center (pResidual 2 D)) ≃* M12) :
    ∃ S : Sylow 2 D, D₁ ⊓ D₂ = (S : Subgroup D) ∧
      Nonempty (D ≃* MulAut M12) ∧ Nonempty (generalizedFitting D ≃* M12) ∧
      IsQuasisimple (generalizedFitting D) ∧
      (∃ N : Subgroup S, ∃ _ : N.Normal,
        Nonempty (N ≃* InnerSquare.C4Square) ∧ Nonempty ((S ⧸ N) ≃* DihedralGroup 4)) ∧
      (∃ N : Subgroup D₁, ∃ _ : N.Normal,
        Nonempty (QuaternionCentralProductData N) ∧
        Nonempty ((D₁ ⧸ N) ≃* DihedralGroup 6)) ∧
      (∃ N : Subgroup D₂, ∃ _ : N.Normal,
        Nonempty (N ≃* InnerSquare.C4Square) ∧
        ∃ K : Subgroup (D₂ ⧸ N), ∃ _ : K.Normal,
          Nonempty (K ≃* OuterSquare.C3 × InnerSquare.E4) ∧
            Nonempty (((D₂ ⧸ N) ⧸ K) ≃* OuterSquare.C2)) := by
  obtain ⟨hleft, hright, hmiddle, hcard⟩ := outer_marked_extensions hM
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hs128 : Nat.card S = 128 := by
    rw [← Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv]
    exact hcard
  obtain ⟨hcomponent, hambient⟩ := ambient_aut_m12_of_sylow_one_twenty_eight e hFstar hq j S hs128
  refine ⟨S, hS, hambient, hcomponent, hFstar ▸ hq, ?_, hleft, hright⟩
  obtain ⟨N, hN, ⟨jN⟩, ⟨jQ⟩⟩ := hmiddle
  let : N.Normal := hN
  exact transport_outer_extension (MulEquiv.subgroupCongr hS) N jN jQ
end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
