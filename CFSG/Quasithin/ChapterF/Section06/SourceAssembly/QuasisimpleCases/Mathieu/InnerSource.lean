module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.Component
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerSylow
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerResidual

/-!
# The literal source vertices and common Sylow in F.6.18(12)

The marked amalgam isomorphism transports the actual quaternion core, C₄²
radical and both quotient maps. Its middle isomorphism transports the same
C₄² kernel to the original intersection, which is the ambient Sylow from
the Goldschmidt triple. Once the separate component catalogue sieve gives
the Mathieu central quotient, the center and ambient-extension arguments
supply every clause of row (12) on these original groups.

Source: Aschbacher–Smith, F.6.18(12), printed p.310. The central-quotient
premise below is explicitly retained for its independent sieve producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
open InnerSquare

private theorem transport_extension {D M A B : Type*}
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

/-- All three extension statements in row (12), on the literal source groups. -/
theorem inner_marked_extensions
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    (∃ N : Subgroup G₁, ∃ _ : N.Normal,
      Nonempty (QuaternionCentralProductData N) ∧
      Nonempty ((G₁ ⧸ N) ≃* Equiv.Perm (Fin 3))) ∧
    (∃ N : Subgroup G₂, ∃ _ : N.Normal,
      Nonempty (N ≃* C4Square) ∧ Nonempty ((G₂ ⧸ N) ≃* DihedralGroup 6)) ∧
    (∃ N : Subgroup (G₁ ⊓ G₂ : Subgroup G), ∃ _ : N.Normal,
      Nonempty (N ≃* C4Square) ∧ Nonempty (((G₁ ⊓ G₂ : Subgroup G) ⧸ N) ≃* E4)) ∧
    Nat.card (G₁ ⊓ G₂ : Subgroup G) = 64 := by
  obtain ⟨j⟩ := hM
  let e := (j.trans GreenBook.MathieuTwelve.concreteIso).symm
  refine ⟨?_, transport_extension e.right localRadical localRadicalEquiv secondQuotientEquiv,
    transport_extension e.middle sylowRadical sylowRadicalEquiv sylowQuotientEquiv, ?_⟩
  · let N := (pCore 2 firstParabolic).map e.left.toMonoidHom
    let : N.Normal := (inferInstance : (pCore 2 firstParabolic).Normal).map
      e.left.toMonoidHom e.left.surjective
    refine ⟨N, inferInstance,
      ⟨ExceptionalParabolics.firstCoreQuaternionData.map (e.left.subgroupMap _)⟩,
      ⟨(QuotientGroup.congr _ N e.left rfl).symm.trans
        Sporadic.Mathieu.M12SmallPair.firstCoreQuotient⟩⟩
  · rw [Nat.card_congr e.middle.symm.toEquiv, card_sylowCandidate]

universe u
variable {D H : Type u} [Group D] [Finite D] [Group H] [Finite H]
    {D₁ D₂ : Subgroup D}

/-- The complete row (12) data after the genuine Mathieu component branch
of the source catalogue, preserving both original local vertices. -/
theorem source_twelve_of_mathieu_quotient
    (e : D ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple D₁ D₂)
    (hFstar : pResidual 2 D = generalizedFitting D)
    (hq : IsQuasisimple (pResidual 2 D))
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups D₁ (D₁ ⊓ D₂) D₂ inf_le_left inf_le_right))
    (j : ((pResidual 2 D) ⧸ center (pResidual 2 D)) ≃* M12) :
    ∃ S : Sylow 2 D, D₁ ⊓ D₂ = (S : Subgroup D) ∧ Nonempty (D ≃* M12) ∧
      IsQuasisimple (generalizedFitting D) ∧
      (∃ N : Subgroup S, ∃ _ : N.Normal,
        Nonempty (N ≃* C4Square) ∧ Nonempty ((S ⧸ N) ≃* E4)) ∧
      (∃ N : Subgroup D₁, ∃ _ : N.Normal,
        Nonempty (QuaternionCentralProductData N) ∧
        Nonempty ((D₁ ⧸ N) ≃* Equiv.Perm (Fin 3))) ∧
      (∃ N : Subgroup D₂, ∃ _ : N.Normal,
        Nonempty (N ≃* C4Square) ∧ Nonempty ((D₂ ⧸ N) ≃* DihedralGroup 6)) := by
  obtain ⟨hleft, hright, hmiddle, hcard⟩ := inner_marked_extensions hM
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hs64 : Nat.card S = 64 := by
    rw [← Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv]
    exact hcard
  obtain ⟨_, hm⟩ := ambient_m12_of_sylow_sixty_four e hFstar hq j S hs64
  refine ⟨S, hS, hm, hFstar ▸ hq, ?_, hleft, hright⟩
  obtain ⟨N, hN, ⟨jN⟩, ⟨jQ⟩⟩ := hmiddle
  let : N.Normal := hN
  exact transport_extension (MulEquiv.subgroupCongr hS) N jN jQ

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
