module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.NaturalIrreducibility
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
/-!
# Shortness of the original two-residual

The identified layer is elementary and central in its actual two-core.
Its literal natural coordinates give irreducibility, while the original
actor identifies the core quotient as quasisimple or cubic. Together with
residual two-perfection and inherited characteristic two these establish
all seven defining clauses of a short group.

Source: Aschbacher–Smith C.1.7 and C.1.18, printed pp.123,126;
Campbell II.8, printed p.38.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
variable (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hc : ⁅pResidual 2 H,pCore 2 H⁆≤Campbell.V H)
variable {F : Type} [Field F] [Finite F] [CharP F 2] (m : NaturalModel e F)

include h hB hc m in
theorem residual_elementary : IsElementaryAbelian 2 (blockU (pResidual 2 H)) := by
  let : IsElementaryAbelian 2 (localV e):=h.localV_elementary
  let : IsElementaryAbelian 2 (moved e):=IsElementaryAbelian.of_le (moved_le_localV e)
  exact IsElementaryAbelian.of_surjective (residualUEquiv h hB hc m).symm.toMonoidHom
    (residualUEquiv h hB hc m).symm.surjective

include h hB hc m in
theorem residual_central : blockU (pResidual 2 H)≤centralizer (pCore 2 (pResidual 2 H):Set (pResidual 2 H)) := by
  intro u hu q hq
  apply Subtype.ext
  have huV:(u:H)∈moved e := by
    rw [←h.campbellV_eq_moved hB m,←residual_blockU_map_eq_campbellV h hB hc]
    exact mem_map_of_mem _ hu
  have hqQ:(q:H)∈pCore 2 H := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 H).Normal).isSubnormal] at hq
    exact hq
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp (h.moved_le_coreOmegaCenter huV)).2.2 q hqQ

include h hB hc m in
theorem residual_quotient_quasisimple_or_three :
    IsQuasisimple (pResidual 2 H⧸pCore 2 (pResidual 2 H)) ∨
      Nat.card (pResidual 2 H⧸pCore 2 (pResidual 2 H))=3 := by
  have htwo : 2≤Nat.card F:=Finite.one_lt_card
  rcases htwo.eq_or_lt with h2|h2
  · right
    exact (Nat.card_congr (residualCoreEquiv h hB hc).toEquiv).trans
      (m.actor_card_of_field_card_two e h2.symm)
  · left
    obtain ⟨E,hE⟩:=m.exists_actor_equiv_sl h2
    let ep:=Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F)
    let : Group.IsPerfect PSL(2,F):=⟨derived_psl_eq_top_of_two_lt_card h2⟩
    let : Group.IsPerfect SL(2,F):=Group.IsPerfect.ofSurjective (f:=ep.symm.toMonoidHom) ep.symm.surjective
    have hcF:4≤Nat.card F := by
      let : Fintype F:=Fintype.ofFinite F
      obtain ⟨n,_,hn⟩:=FiniteField.card F 2
      have hn':Nat.card F=2^(n:ℕ):=by simpa only [Nat.card_eq_fintype_card] using hn
      have hn2:2≤(n:ℕ) := by
        by_contra hnot
        have hnlt : (n:ℕ)<2 := Nat.lt_of_not_ge hnot
        have hnpos : 0<(n:ℕ):=n.property
        have hone:(n:ℕ)=1:=by omega
        rw [hone,pow_one] at hn'
        omega
      rw [hn']
      exact Nat.pow_le_pow_right (by decide : 0<2) hn2
    let : IsQuasisimple SL(2,F) := {
      toIsPerfect := inferInstance
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcF }
    exact IsQuasisimple.of_mulEquiv ((residualCoreEquiv h hB hc).trans E).symm

include h hB hc m in
theorem residual_short : IsShort (pResidual 2 H) := by
  refine ⟨inferInstance,isPPerfect_pResidual 2,residual_generalizedFitting_eq_core h,
    residual_elementary h hB hc m,residual_central h hB hc m, residual_quotient_quasisimple_or_three h hB hc m,?_⟩
  exact (residualNaturalModel h hB hc m).irreducible _ (derivedNatural_irreducible m)
end CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
