module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreDegree
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalSylowBound

/-!
# Excluding both marked Hall–Janko zero-core rows

The original moved reduced subgroup lies in S and is normal there. Its
order is at least sixteen. A whole-overlap isomorphism transports S to a
Sylow subgroup of the model Borel, hence to a Sylow of the actual carrier.
The certified normal-elementary bounds are four in J₂ and eight in its
full automorphism group, contradicting that same original subgroup.

Only the parabolic equivalence required by F.1.12 is used; no compatibility
of the overlap maps or equality S = T is assumed. Both bounds are
discharged on the concrete ATLAS carrier, including the proved isomorphism
from its extension to its full automorphism group. Recognition of the
model alternatives remains with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, printed p.648, and F.1.12(I)(10–11), p.263.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A literal Borel marking into a Sylow overgroup transfers the original
normal elementary actor; a bound of eight contradicts its size of at least sixteen. -/
theorem LocalData.zeroCore_no_small_normal_sylow_borel
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {X : Type*} [Group X] [Finite X] (Q : Sylow 2 X) (B₀ : Subgroup X)
    (hQB : (Q : Subgroup X) ≤ B₀)
    (hb : ∀ E : Subgroup Q, E.Normal → IsElementaryAbelian 2 E → Nat.card E ≤ 8)
    (e : (Global.sourceS L H ⊔ (B ⊓ R) : Subgroup G) ≃* B₀) : False := by
  let S := Global.sourceS L H
  let C := S ⊔ (B ⊓ R)
  have hs := (d.hypothesisF11 h hH c hd hz).sylow_commonBorel
  rw [d.zeroCore_commonBorel hz] at hs
  obtain ⟨P,hP⟩ := hs
  let a : P ≃* S := ((P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr hP)
  let P' : Sylow 2 B₀ := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b : S ≃* Q := a.symm.trans
    (((P : Subgroup C).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((P'.equiv (Q.subtype hQB)).trans (subgroupOfEquivOfLe hQB)))
  obtain ⟨hU,hUT,hlower⟩ := h.moved_reduced_size
  let := hU
  have hUS : ⁅W,L⁆ ≤ S := by
    rw [←d.S_intersection_left] at hUT
    exact hUT.trans inf_le_left
  let U := ⁅W,L⁆.subgroupOf S
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUS
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    ((Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans h.moved_reduced_normalizes)
  let E := U.map b.toMonoidHom
  have hEn : E.Normal := Normal.map inferInstance b.toMonoidHom b.surjective
  have hEe : IsElementaryAbelian 2 E := IsElementaryAbelian.map b.toMonoidHom
  have hupper := hb E hEn hEe
  rw [card_map_of_injective b.injective,
    Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv] at hupper
  have hl : 16 ≤ Nat.card (⁅W,L⁆ : Subgroup G) := le_trans
    (show 2 ^ 4 ≤ 2 ^ (2 * n) from Nat.pow_le_pow_right (by decide)
      (by have := h.exponent; omega)) hlower
  omega

/-- Every genuine Hall–Janko parabolic marking is excluded, regardless of
orientation; only its actual whole-overlap isomorphism is needed. -/
theorem LocalData.zeroCore_not_janko_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ¬ ChapterF.GreenBook.HallJanko.IsJ2ParabolicModel (zeroCoreAmalgam L H B D R) := by
  rintro ⟨m,⟨e⟩⟩
  apply d.zeroCore_no_small_normal_sylow_borel h hH c hd hz m.S m.toMarking.B
    m.toMarking.S_le_B _ e.middle
  intro E hn he
  exact (Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four m.S E hn he).trans
    (by decide)

/-- The full automorphism Hall–Janko marking is excluded by the bound eight
on normal elementary subgroups of its actual Sylow subgroup. -/
theorem LocalData.zeroCore_not_autJanko_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ¬ ChapterF.GreenBook.HallJanko.IsAutJ2ParabolicModel (zeroCoreAmalgam L H B D R) := by
  rintro ⟨m,⟨e⟩⟩
  apply d.zeroCore_no_small_normal_sylow_borel h hH c hd hz m.S m.toMarking.B
    m.toMarking.S_le_B _ e.middle
  exact NormalSylowElementary.bound_equiv
    Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionEquivAut.symm 8
    Sporadic.LeechRelated.J2.extension_sylow_normal_elementary_card_le_eight m.S

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
