module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanKernel
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticElementaryNormalBound

/-!
# Exact order and kernel of the original elementary middle span

The genuine nine-path upper bound matches the earlier lower bound. The same
selected span therefore has order 32, its intersection with the full quintic
centralizer is the original order-16 hyperplane, and its commutator with the
full quintic core lies in the original quintic module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact span has order 32 and its full centralizer kernel is the marked hyperplane. -/
theorem source_quintic_second_kernel_span_exact
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ Nat.card W = 32 ∧
        ⁅W,U⁆ = centralInvolutions T ∧ U ⊓ centralizer (W : Set G) = R ∧
        (W ⊓ C).relIndex W = 2 ∧ 2 * Nat.card (W ⊓ C : Subgroup G) = Nat.card W ∧
        W ⊓ C = R ∧ ⁅W,H.pCoreIn 2⁆ ≤ U := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hR,hRstar,hWlower,
      hcomm,hfixed,hindex,hcardinal,hsmall⟩ :=
    source_quintic_second_kernel_span_line hG T hempty hM hu hmany hcard e H hH hi
  let R := U ⊓ (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
  let W := conjugateSpanBy R X
  let : IsElementaryAbelian 2 W := hWel
  have hWupper : Nat.card W ≤ 32 := source_quintic_elementary_normal_core_card
    hG T hempty hM hu hmany hcard e H hH hi W hWQ hXW
  exact ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hR,hRstar,
    Nat.le_antisymm hWupper hWlower,hcomm,hfixed,hindex,hcardinal,hsmall hWupper⟩

end CFSG.Quasithin.Chapter14.Section06
