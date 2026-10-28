module
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Stellmacher.SectionTwo.LemmaTwoFour
public import Stellmacher.SectionTwo.NativeBaumannActionFactors
public import Stellmacher.SectionOne.OneSevenDerivedModuleProduct
public import Stellmacher.SectionOne.SelectedProductIrreducibleSupport
public import Stellmacher.TwoResidualSylowSupplement

/-!
# The residual kernel in a solvable minimal parabolic

The two-layer centralizer theorem identifies the two-residual's intersection
with the canonical module centralizer with its two-core intersection. After
factoring out the actual core commutator, a central two-kernel over an
abelian three-group vanishes by two-perfection.

These are the kernel reductions for the solvable C.1.29 outside-block
construction, using Stellmacher (2.4), journal p.20,
`refs/latex/stellmacher-n-group.tex`. The original quotient and commutator
subgroups are retained; the whole module centralizer need not be a two-group.
-/

public section
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
open Subgroup Stellmacher
open scoped commutatorElement

variable {G B : Type*} [Group G] [Group B]

private theorem twoResidualSubgroup_eq_pResidual [Finite G] (L : Subgroup G) :
    twoResidualSubgroup L = pResidual 2 L := by
  unfold twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    let := hN
    refine ⟨hN, IsPGroup.of_card (n := n) ?_⟩
    simpa only [index_eq_card] using hn
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    exact ⟨hN, n, by simpa only [index_eq_card] using hn⟩

theorem twoResidualAmbient_top_eq_pResidual [Finite G] :
    twoResidualAmbient (⊤ : Subgroup G) = pResidual 2 G := by
  rw [twoResidualAmbient, twoResidualSubgroup_eq_pResidual]
  exact map_pResidual 2 (topEquiv : (⊤ : Subgroup G) ≃* G)

/-- A two-perfect extension has precisely its commutator layer as kernel
when that kernel is two-primary and central modulo the layer. -/
theorem ker_eq_of_twoPerfect_of_elementary_three
    (hp : IsPPerfect 2 G) (f : G →* B) [IsElementaryAbelian 3 B]
    (W : Subgroup G) [W.Normal] (hW : W ≤ f.ker)
    (hker : IsPGroup 2 f.ker) (hcomm : ⁅f.ker, (⊤ : Subgroup G)⁆ ≤ W) :
    f.ker = W := by
  let q := QuotientGroup.mk' W
  let fbar := QuotientGroup.lift W f hW
  have hbarKer : fbar.ker = f.ker.map q := QuotientGroup.ker_lift W f hW
  have hcentral : fbar.ker ≤ center (G ⧸ W) := by
    rw [hbarKer]
    rintro x ⟨a, ha, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective W y
    have hzero : ⁅q a, q b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hcomm (commutator_mem_commutator ha (mem_top b)))
    exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm
  have htwo : IsPGroup 2 fbar.ker := by
    rw [hbarKer]
    exact hker.map q
  have hperfect : IsPPerfect 2 (G ⧸ W) :=
    hp.of_surjective q (QuotientGroup.mk'_surjective W)
  have hinj : Function.Injective fbar :=
    MonoidHom.injective_of_isPPerfect_of_coprime_abelian_image hperfect fbar
      hcentral htwo
      (fun x y => (IsMulCommutative.is_comm (M := B)).comm (fbar x) (fbar y))
      (by decide : Nat.Coprime 2 3)
      (fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 B) (fbar x))
  exact ((QuotientGroup.injective_lift_iff W f hW).mp hinj).symm

variable [Finite G]

/-- The original residual's centralizer kernel is exactly its two-core intersection. -/
theorem residual_inf_centralizer_eq
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    (hW : ⁅pCore 2 G, pResidual 2 G⁆ ≤ SectionTwo.vSubgroup S)
    (hQC : pCore 2 G ≤ centralizer (SectionTwo.vSubgroup S : Set G)) :
    pResidual 2 G ⊓ centralizer (SectionTwo.vSubgroup S : Set G) =
      pResidual 2 G ⊓ pCore 2 G := by
  let V := SectionTwo.vSubgroup S
  let : V.Normal := Subgroup.normalClosure_normal
  let : IsElementaryAbelian 2 V :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  have ht := two_layer_le_radical (pCore 2 G) V (pCore 2 G)
    (IsElementaryAbelian.isPGroup 2 V)
    (pCore_quotient_pCore_eq_bot 2) (inf_le_right.trans h.centralizer_twoCore_le)
  apply le_antisymm
  · apply le_inf inf_le_left
    apply le_trans _ ht
    exact le_inf inf_le_right
      (inf_le_left.trans (le_commutatorPreimage le_top (by rwa [commutator_comm])))
  · exact inf_le_inf_left _ hQC

end CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
