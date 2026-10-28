module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeOverlap
public import Theory.SpecificGroups.PSL3.LinearThreeBorelOrder
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual PSL₃(4) residual has no odd central cover

The original maximal subgroup has odd Hall order three, and its marked
PSL₃(4) quotient Borel already has order divisible by three. The product
formula for kernel and image therefore makes its normal core a two-group.
The normal core equals O₂(H), so the literal comparison from the residual's
two-core quotient to its star-image is an isomorphism.

The original full-module intersection bound now concerns V ∩ O₂(H), with
binary corank at most two. This does not assert H-normality or movement of
that intersection, and does not exclude the PSL₃(4) branch.

Source: Aschbacher--Smith E.2.2 and 9.2.7, printed pp.215--216,731--732;
the original long-root placement used by the overlap theorem is E.2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceOldResidual
open ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

private theorem kernel_two_of_odd_three
    (M J : Subgroup X) [J.Normal] (hJM : J ≤ M)
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card M → n ∣ 3)
    (h3 : 3 ∣ Nat.card (M.map (QuotientGroup.mk' J))) : IsPGroup 2 J := by
  let f := (QuotientGroup.mk' J).comp M.subtype
  have hk : f.ker = J.subgroupOf M := by
    ext x
    change QuotientGroup.mk' J (x : X) = 1 ↔ (x : X) ∈ J
    exact QuotientGroup.eq_one_iff (x : X)
  have hr : f.range = M.map (QuotientGroup.mk' J) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hc := f.ker.card_mul_index
  rw [index_ker, hk, hr, Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv] at hc
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp hp
  by_cases he : p = 2
  · subst p
    norm_num
  have ho : Odd p := hprime.odd_of_ne_two he
  have hd3 : p * 3 ∣ Nat.card M := hc ▸ Nat.mul_dvd_mul hd h3
  have hb := Nat.le_of_dvd (by decide : 0 < 3) (hsize (p*3) (ho.mul (by decide)) hd3)
  have hp2 := hprime.two_le
  omega

/-- The marked field-four Borel exhausts the original maximal subgroup's odd Hall order. -/
theorem linear_three_core_eq_twoCore
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card (minimalParabolicMax S hP) → n ∣ 3)
    (hm : ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 3 4) :
    minimalParabolicCore S hP = pCore 2 X := by
  let M := minimalParabolicMax S hP
  let J := minimalParabolicCore S hP
  have h3 : 3 ∣ Nat.card (M.map (QuotientGroup.mk' J)) := by
    have hmodel := source_binary_linear_three_model S hP hs K hK hgen
      (n := 2) (by decide) (by simpa using hm)
    rcases hmodel with ⟨F,hF,hfin,hchar,_,hcard,e,hB,_⟩ | ⟨F,hF,hfin,hchar,_,hcard,e,hB,_⟩
    · have hc : Nat.card (sourceImage M (M ⊓ K)) = 192 :=
        (Nat.card_congr (componentBorelEquiv (Matrix.PSL3.LinearThree.borel F) e hB).toEquiv).trans
          (Matrix.PSL3.CartanActions.BorelQuotient.card_borel_linear_three_four F hcard)
      have hd := card_dvd_of_le (map_mono (f := QuotientGroup.mk' J)
        (show M ⊓ K ≤ M from inf_le_left))
      change Nat.card (sourceImage M (M ⊓ K)) ∣ _ at hd
      rw [hc] at hd
      exact (by decide : 3 ∣ 192).trans hd
    · exact (not_symplectic_model hsize (by simpa using hcard) ⟨e,hB⟩).elim
  have hj : IsPGroup 2 J := kernel_two_of_odd_three M J M.normalCore_le hsize h3
  exact le_antisymm (le_sSup ⟨inferInstance,hj⟩) (minimalParabolicTwoCore_le_core S hP)

end CFSG.Quasithin.Chapter10.SourceOldResidual

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- In the original tensor branch, the maximal normal core is exactly O₂(H). -/
theorem old_residual_linear_three_core_eq_twoCore
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    minimalParabolicCore (T.subtype hH.1.1.2) hP = pCore 2 H := by
  apply SourceOldResidual.linear_three_core_eq_twoCore _ _ _ _ hK
    (pResidual_sup_sylow_eq_top _) (m.hstar_maximal_odd_order_dvd_three hH hlarge) hm
  intro hh
  let := hh
  exact (Nat.not_le_of_gt hlarge) generationParameter_le_one_of_solvable

/-- The original two-residual quotient itself is PSL₃(4); no odd central kernel remains. -/
theorem old_residual_linear_three_quotient
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    ClassicalGroup.IsPSL (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) 3 4 := by
  let S := T.subtype hH.1.1.2
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  let K := pResidual 2 H
  let f := DiagramHall.linearSourceComparison S hP K
  have hJ := m.old_residual_linear_three_core_eq_twoCore hH hlarge hK hm
  change sourceKernel _ = pCore 2 H at hJ
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    rintro ⟨x,k,hk,rfl⟩ hx
    have he := congrArg Subtype.val hx
    change QuotientGroup.mk' (sourceKernel (minimalParabolicMax S hP)) k = 1 at he
    have hkJ := (QuotientGroup.eq_one_iff k).mp he
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff k).mpr (hJ ▸ hkJ)
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hm
  let b := MulEquiv.ofBijective f ⟨hf,DiagramHall.linearSourceComparison_surjective S hP K⟩
  exact ⟨F,hF,hfin,hcard,⟨((cComponentTwoCoreQuotientEquiv hK).trans b).trans a⟩⟩

/-- The original V ∩ O₂(H), with its literal ambient embedding, has binary corank at most two. -/
theorem old_residual_linear_three_twoCore_overlap_corank_le_two
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    subgroupCorank D.fullModule (D.fullModule ⊓ H.pCoreIn 2) ≤ 2 := by
  have h := m.old_residual_linear_three_overlap_corank_le_two hH hlarge hK hm
  dsimp only at h
  rwa [m.old_residual_linear_three_core_eq_twoCore hH hlarge hK hm] at h

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
