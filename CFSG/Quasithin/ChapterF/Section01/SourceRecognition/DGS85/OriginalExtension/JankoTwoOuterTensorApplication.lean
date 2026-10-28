module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoOuterInvolution
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# Original outer Hall–Janko quotients in the tensor consumer

The source reduction has literal endpoints H and AT and whole Borel BT.
On a proper enlargement of a genuinely recognized reduced J₂ pair, the
new quotient calculation gives H/O₂(H) = S₅, AT/O₂(AT) = S₃ × S₃, and
BT/O₂(BT) = S₃. Every square in the same ambient Sylow T lies in O₂(AT), and T contains
an actual involution outside O₂(BT).
These are applications of the original extension theorem, with no supplied
original quotient maps or replacement Sylow subgroup.

The reduced parabolic comparison and the cubic-factor construction remain
explicit. The actual Aut(J₂) parabolic equivalences still require the
outer-involution and generator relations of DGS (15.3), pp.229–231.
Source consumer: Aschbacher–Smith 9.3.1, pp.732–733, using F.1.11–12.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Original quotient restoration in the literal mixed tensor pair. -/
theorem mixed_cubic_factor_outer_quotients_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : (T : Subgroup G) ≠ SuzukiContainment.reducedSylow
      ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) ∧
    Nonempty (((A ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    Nonempty (((B ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
    ∀ x ∈ (T : Subgroup G), x ^ 2 ∈ twoCore (A ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨hf,_,_,_,hb,hp,hq⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hfirst := JankoTwo.original_first_quotient_of_ne hf 0 e.left hne
  have hsecond := JankoTwo.original_second_quotient_of_ne hf 0 1 e.left e.right hne
  have hborel := JankoTwo.original_borel_quotient_of_ne hf 0 e.left e.middle hne
  have hsquare := JankoTwo.original_sylow_square_mem_second_core hf 0 1 e.left e.right hne
  rw [hp] at hfirst
  rw [hq] at hsecond hsquare
  rw [hb] at hborel
  exact ⟨hfirst,hsecond,hborel,hsquare⟩

/-- A genuine involution in the same ambient Sylow leaves O₂(BT) in the
proper extension. The Cartan-generator relations remain a further step. -/
theorem mixed_cubic_factor_outer_involution_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : (T : Subgroup G) ≠ SuzukiContainment.reducedSylow
      ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) :
    ∃ x ∈ (T : Subgroup G), x ^ 2 = 1 ∧
      x ∉ twoCore (B ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨hf,_,_,_,hb,_,_⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  have hx := JankoTwo.exists_original_sylow_outer_involution hf 0 1 e.left e.right hne
  change ∃ x ∈ (T : Subgroup G), x ^ 2 = 1 ∧
    x ∉ twoCore (commonBorel ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) at hx
  rwa [hb] at hx

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
