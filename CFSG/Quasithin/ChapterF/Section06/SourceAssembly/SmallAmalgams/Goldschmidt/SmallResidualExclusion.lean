module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualInvolution
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualIndex
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualCubic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallAlternatingBase
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The original large amalgam has no small local residual

An A₄ residual supplies an involution outside the opposite two-core with
centralizer index at most two there. The opposite residual is therefore
C₃ or A₄. Characteristic two excludes C₃; the proved action on the two A₄
residuals bounds the original overlap by 32, contradicting its order at
least 64.

The final wrappers retain the original finite Goldschmidt triple. The
universal marked amalgam transports both endpoint residuals, their own
core quotients, and the original overlap without assuming a size bound
on the normal residual's overlap.

Source: Goldschmidt (4.1)--(4.2), *Automorphisms of trivalent graphs* (1980),
pp.392--393, specialized to the characteristic-two F.1.12/F.6.5 branch.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.residual_not_alternating_of_large_overlap
    (h : CubicTreeAction F)
    (eA : ((F false) ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3))
    (eB : ((F true) ⧸ pCore 2 (F true)) ≃* Equiv.Perm (Fin 3))
    (hC : ¬ Nonempty ((pResidual 2 (F true)) ≃* Multiplicative (ZMod 3)))
    (hlarge : 64 ≤ Nat.card (F false ⊓ F true : Subgroup G)) :
    ¬ Nonempty ((pResidual 2 (F false)) ≃* alternatingGroup (Fin 4)) := by
  rintro ⟨eR⟩
  let : Finite (F true) := h.finite true
  obtain ⟨v, hv, hn, hi⟩ := h.exists_small_centralizer_involution_of_alternating eR eA
  rcases residual_cubic_or_alternatingFour_of_involution_index_le_two eB hv hn hi with h3 | h4
  · exact hC h3
  · obtain ⟨eR'⟩ := h4
    have hh := h.overlap_card_le_thirtyTwo_of_alternating_residuals eR eR'
    omega

/-- The original finite left endpoint has no A₄ residual when the common
Sylow is large and the opposite endpoint has characteristic two. -/
theorem original_left_residual_not_alternating [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hB : generalizedFitting B = pCore 2 B)
    (hlarge : 64 ≤ Nat.card (A ⊓ B : Subgroup G)) :
    ¬ Nonempty ((pResidual 2 A) ≃* alternatingGroup (Fin 4)) := by
  let α := inclusionAmalgam A B
  let F := RankTwoAmalgam.Universal.cosetFamily α
  let hP := primitiveCubic_of_goldschmidt h hcore
  let e := RankTwoAmalgam.Universal.markedIso α hP.sylow.left_injective hP.sylow.right_injective
  have ht : CubicTreeAction F := universalCubicTreeAction_of_goldschmidt h hcore
  let rA := (e.left.subgroupMap (pResidual 2 A)).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 e.left))
  let rB := (e.right.subgroupMap (pResidual 2 B)).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 e.right))
  have eA : ((F false) ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3) :=
    (LocalCoreTransport.quotientEquiv 2 e.left.symm).trans h.quotient_left.some
  have eB : ((F true) ⧸ pCore 2 (F true)) ≃* Equiv.Perm (Fin 3) :=
    (LocalCoreTransport.quotientEquiv 2 e.right.symm).trans h.quotient_right.some
  have hC : ¬ Nonempty ((pResidual 2 (F true)) ≃* Multiplicative (ZMod 3)) := by
    rintro ⟨c⟩
    exact residual_not_cubic_of_characteristicTwo hB ⟨rB.trans c⟩
  have hlarge' : 64 ≤ Nat.card (F false ⊓ F true : Subgroup _) := by
    exact hlarge.trans_eq (Nat.card_congr e.middle.toEquiv)
  rintro ⟨a⟩
  exact ht.residual_not_alternating_of_large_overlap eA eB hC hlarge' ⟨rA.symm.trans a⟩

/-- Both original endpoints avoid the small alternating residual. -/
theorem original_residual_not_alternating [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hlarge : 64 ≤ Nat.card (A ⊓ B : Subgroup G)) (i : Bool) :
    ¬ Nonempty ((pResidual 2 (if i then B else A : Subgroup G)) ≃*
      alternatingGroup (Fin 4)) := by
  cases i
  · exact original_left_residual_not_alternating (A := A) (B := B) h hcore hB hlarge
  · exact original_left_residual_not_alternating (A := B) (B := A) h.symm hcore hA
      (by simpa only [inf_comm B A] using hlarge)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
