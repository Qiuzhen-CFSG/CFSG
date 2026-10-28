module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.PairPropagation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.MovedModel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ThompsonCommutator
/-!
# The covered S₅ source conclusion for the original component

The same fixed characteristic pair gives centrality of its original first
subgroup, normality of its second member, or an actual A₅ block. The third
alternative also identifies the intrinsic block module with [U,L], proves
its support in the original module U, and gives L=[L,J(R)]. Every assertion
uses the original covered natural projection, component and Sylow subgroup.

The first subgroup is allowed to be any C≤Z(R) inside the prescribed first
member; this retains the C₁(T) used when the original two-group T is external.
Source: C.1.21(2), C.1.23(1), printed pp.128–130.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB Theory.SpecificGroups.SymmetricFive
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The marked covered-S₅ source conclusion retains the original component,
its module, the original pair, and its full Thompson commutator. -/
theorem marked_source_conclusion
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hR : (R : Subgroup H).map q = OuterFourGeometry.eight)
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann (R : Subgroup H)))
    (hD : D.Universal.{u,u}) (C : Subgroup H)
    (hC : C ≤ (center (R : Subgroup H)).map (R : Subgroup H).subtype)
    (hCD : C ≤ D.first.map (baumann (R : Subgroup H)).subtype) :
    C ≤ center H ∨ (D.second.map (baumann (R : Subgroup H)).subtype).Normal ∨
      (IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L = ⁅L,elementaryAbelianMaxJ (R : Subgroup H)⁆ ∧
        (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U) := by
  rcases marked_quotient_block_alternatives R hfit L hcomp hprod eL U q hq hk hR hL
    p hp he hfix hJ D hD C hC hCD with h | h | hb
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    have hQ : pCore 2 H ≤ q.ker := by
      rw [←MonoidHom.comap_bot]
      apply map_le_iff_le_comap.mp
      rw [←Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot]
      exact le_sSup ⟨Subgroup.Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
    obtain ⟨ha,hs⟩ := alternating_block_of_covered_quotient U q hq hk L hL hb
      (hQ.trans_eq hk) p hp he hfix
    have hUR : U ≤ R := (show U ≤ pCore 2 H from
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans
        (pCore_isPGroup.le_sylow_of_normal R)
    have hJi := (marked_quotient_images R U hUR q hq hk hR p hp he hfix hJ).1
    have hkp := action_kernel_twoGroup q L R hprod R.isPGroup' hL (Nat.card_congr eL.toEquiv)
    have hcomm : L = ⁅L,elementaryAbelianMaxJ (R : Subgroup H)⁆ :=
      @component_eq_thompson_commutator H inferInstance (R : Subgroup H) L inferInstance
        hb.short.twoPerfect q hkp hL hJi
    exact ⟨hb,ha,hcomm,hs,hs.le.trans (commutator_le_left U L)⟩

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
