module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Splitting
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Movement
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The original seed cannot lie in the moving summand

The displaced point is the actual commutator of W with the conjugate
center. Commuting centers and the coprime direct sum place its tilded
image in the moving summand. The point itself vanishes in the tilded
quotient, so the marked plane and its whole H-orbit lie there as well.
That orbit spans U-tilde, contradicting a nonzero tilded center.

Source: Aschbacher--Smith 14.3.15, printed p.995, final paragraph.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

omit [Finite G] in
private theorem tilde_commutator (F : InvariantFlag T V 2)
    (A B : Subgroup G) (hAH : A ≤ F.H) (hBH : B ≤ F.H) :
    F.tilde ⁅A,B⁆ = ⁅F.tilde A,F.tilde B⁆ := by
  have hC : ⁅A,B⁆ ≤ F.H := (Subgroup.commutator_le_sup A B).trans (sup_le hAH hBH)
  have hsub : (⁅A,B⁆).subgroupOf F.H = ⁅A.subgroupOf F.H,B.subgroupOf F.H⁆ := by
    apply map_injective F.H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hC,
      map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hBH]
  change ((⁅A,B⁆).subgroupOf F.H).map F.tildeProjection = _
  rw [hsub,map_commutator]
  rfl

/-- Once the displaced point is the actual commutator, its tilded line lies
in the moving summand. The literal H-orbit of that line spans U-tilde. -/
theorem terminal_tilde_seed_splitting_contradiction
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V]
    (L : Subgroup G) (hLV : L ≤ normalizer (V : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hc : ⁅F.ZU,conjugate F.ZU g⁆ = ⊥)
    (he : ⁅F.W,conjugate F.ZU g⁆ = conjugate (F.Vi 1) g)
    (hs : F.tilde F.U = ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ ⊔ F.tilde F.ZU)
    (hd : Disjoint ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ (F.tilde F.ZU))
    (hZ : F.ZU ≠ F.Vi 1) : False := by
  let D := ⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆
  have hUH : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hKH : F.H ≤ normalizer (centerConjugateResidual F g : Set G) := centerConjugateResidual_normalized F g
  have hn : F.tilde F.H ≤ normalizer (D : Set F.G₁tilde) := by
    intro a ha
    change a ∈ normalizer ((⁅F.tilde F.U,F.tilde (centerConjugateResidual F g)⁆ : Subgroup _) : Set _)
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (F.tilde_normalizes F.H F.U hUH ha),
      mem_normalizer_iff_map_conj_eq.mp (F.tilde_normalizes F.H (centerConjugateResidual F g) hKH ha)]
  have hg := F.conjugate_center_le_H g (F.P_le_seed_normalizer L hLV hgP)
  have hnorm : F.tilde (conjugate F.ZU g) ≤ normalizer (D : Set F.G₁tilde) :=
    (map_mono (comap_mono hg)).trans hn
  have hDU : D ≤ F.tilde F.U := le_normalizer_iff_commutator_le_left.mp
    (F.tilde_normalizes (centerConjugateResidual F g) F.U
      ((centerConjugateResidual_le_H F g hg).trans hUH))
  have hZU : F.tilde F.ZU ≤ F.tilde F.U := map_mono (comap_mono (map_subtype_le (center F.U)))
  have hfixed : ⁅F.tilde F.ZU,F.tilde (conjugate F.ZU g)⁆ = ⊥ := by
    rw [←tilde_commutator F F.ZU (conjugate F.ZU g)
      ((map_subtype_le (center F.U)).trans F.U_le_H) hg,hc]
    change ((⊥ : Subgroup G).subgroupOf F.H).map F.tildeProjection = ⊥
    rw [bot_subgroupOf,Subgroup.map_bot]
  have hUD : ⁅F.tilde F.U,F.tilde (conjugate F.ZU g)⁆ ≤ D := by
    rw [hs]
    exact commutator_sup_le_of_relative_normal (F.tilde F.U) D (F.tilde F.ZU)
      (F.tilde (conjugate F.ZU g)) D (normalizer_commutator_ge_left _ _) hDU hZU
      (le_normalizer_iff_commutator_le_left.mp hnorm) (hfixed.le.trans bot_le)
  have hpD : F.tilde (conjugate (F.Vi 1) g) ≤ D := by
    rw [←he,tilde_commutator F F.W (conjugate F.ZU g)
      ((show F.W ≤ F.U from inf_le_left).trans F.U_le_H) hg]
    exact (commutator_mono (map_mono (comap_mono (show F.W ≤ F.U from inf_le_left))) le_rfl).trans hUD
  have hpbot : F.tilde (F.Vi 1) = ⊥ := by
    change ((F.Vi 1).subgroupOf F.H).map F.tildeProjection = ⊥
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [show F.tildeProjection.ker = (F.Vi 1).subgroupOf F.H from QuotientGroup.ker_mk' _]
  have hpH : conjugate (F.Vi 1) g ≤ F.H :=
    (map_mono (F.point_le_ZU (by decide))).trans hg
  have hseed : F.tilde V ≤ D := by
    have hv : V = F.Vi 1 ⊔ conjugate (F.Vi 1) g :=
      F.last.symm.trans (F.plane_eq_point_join_conjugate (by decide) L hLV g hgP hgH)
    rw [congrArg (fun A : Subgroup G => F.tilde A) hv]
    change ((F.Vi 1 ⊔ conjugate (F.Vi 1) g).subgroupOf F.H).map F.tildeProjection ≤ D
    rw [subgroupOf_sup ((F.le_seed 1).trans ((le_conjugateSpanBy _ _).trans F.U_le_H)) hpH,
      Subgroup.map_sup]
    exact sup_le (hpbot.le.trans bot_le) hpD
  have hfull : F.tilde F.U ≤ D := by
    change F.tilde (F.UH F.H) ≤ D
    rw [F.tilde_UH_eq_span F.H le_rfl]
    exact conjugateSpanBy_le hseed hn
  have hzero : F.tilde F.ZU = ⊥ := hd.eq_bot_of_ge (hZU.trans hfull)
  apply hZ
  apply le_antisymm ?_ (F.point_le_ZU (by decide))
  intro z hz
  let a : F.H := ⟨z,((map_subtype_le (center F.U)).trans F.U_le_H) hz⟩
  have hm : F.tildeProjection a ∈ F.tilde F.ZU := mem_map_of_mem _ hz
  rw [hzero,mem_bot] at hm
  exact (QuotientGroup.eq_one_iff a).mp hm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
