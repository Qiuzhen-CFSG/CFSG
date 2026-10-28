module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticElementaryNormalBound
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanSize

/-!
# Exact span cardinality with the escaping reciprocal commutator

The original span-size producer retains the chosen conjugator and its
nonzero reciprocal commutator.  The normalized path bound supplies the upper
cardinality on that same span, so the lower bound is exact without losing the
escape witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The selected span has order 32 and retains its nonzero reciprocal branch. -/
theorem source_quintic_second_kernel_span_strong_exact
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
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Rstar ≤ W ∧ ⁅Rstar,U⁆ ≠ ⊥ ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ Nat.card W = 32 := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWlower⟩ :=
    source_quintic_second_kernel_span_size hG T hempty hM hu hmany hcard e H hH hi
  let R := U ⊓ (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
  let Rstar := U.map (MulAut.conj g).toMonoidHom ⊓ H.pCoreIn 2
  let W := conjugateSpanBy R X
  let : IsElementaryAbelian 2 W := hWel
  have hWupper : Nat.card W ≤ 32 := source_quintic_elementary_normal_core_card
    hG T hempty hM hu hmany hcard e H hH hi W hWQ hXW
  have hRstarW : Rstar ≤ W := by
    change (U.map (MulAut.conj g).toMonoidHom ⊓ H.pCoreIn 2) ≤ W
    rw [← hWUstar]
    exact inf_le_left
  exact ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hRstarW,hmove,hRcard,hRstarcard,
    Nat.le_antisymm hWupper hWlower⟩

end CFSG.Quasithin.Chapter14.Section06
