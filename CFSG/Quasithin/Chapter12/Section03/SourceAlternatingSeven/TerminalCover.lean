module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Setup
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Eliminating the central A₇ cover from cubic Sylow commutativity

The two-core quotient is perfect, has trivial two-core, and has central
quotient A₇. Its center therefore has order one or three. Transfer from an
abelian Sylow three-subgroup rules out central three-torsion, leaving the
original two-core as the full central kernel. The resulting A₇ equivalence
commutes with the original projection on every element of L.

This is the covering step in 12.3.13, conditional on cubic Sylow
commutativity supplied by the preceding A₅ component argument. Source:
Aschbacher--Smith, printed p.811. It does not assert the remaining
O^{3′}(N_G(L)) identity or discharge the Sylow premise.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} (S : Setup T L V)

private def quotientEquiv :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* CentralQuotient L := by
  let f := (QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
    (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) := by
    ext a
    simp [f]
  exact (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)

include S in
/-- The central cover collapses once the actual cubic Sylow is abelian.
The abelian-Sylow premise is a conclusion required from the A₅ component
argument, not a replacement for the central-quotient source hypothesis. -/
theorem central_kernel_eq_twoCore_of_abelian_threeSylow
    (P : Sylow 3 (L ⧸ pCore 2 L)) (hP : IsMulCommutative P) :
    (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = pCore 2 L := by
  let := S.hypothesis.quasisimple
  let e := quotientEquiv (L := L)
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot (G := L) 2) _ le_rfl
  have hn : ¬ 3 ∣ Nat.card (center (L ⧸ pCore 2 L)) := by
    have hh := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
      (QuotientGroup.mk' (center (L ⧸ pCore 2 L)))
      (by rw [QuotientGroup.ker_mk']) P hP
    simpa only [QuotientGroup.ker_mk'] using hh
  have hc : Nat.card (center (L ⧸ pCore 2 L)) = 1 := by
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 7 (by decide)
      (e.trans S.quotient) ho with hc | ⟨_, hc⟩
    · exact hc
    · exact (hn (by rw [hc])).elim
  rw [Subgroup.card_eq_one.mp hc]
  exact QuotientGroup.ker_mk' _

/-- The resulting A₇ marking still uses the original central quotient map. -/
def quotientEquivOfAbelianThreeSylow
    (P : Sylow 3 (L ⧸ pCore 2 L)) (hP : IsMulCommutative P) :
    (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7) :=
  (QuotientGroup.quotientMulEquivOfEq
    (central_kernel_eq_twoCore_of_abelian_threeSylow S P hP).symm).trans S.quotient

theorem quotientEquivOfAbelianThreeSylow_apply
    (P : Sylow 3 (L ⧸ pCore 2 L)) (hP : IsMulCommutative P) (l : L) :
    quotientEquivOfAbelianThreeSylow S P hP (QuotientGroup.mk' (pCore 2 L) l) =
      S.projection l := rfl

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
