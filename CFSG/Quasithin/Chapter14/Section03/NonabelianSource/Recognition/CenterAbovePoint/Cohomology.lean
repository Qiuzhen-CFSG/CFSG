module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Residual
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# A cohomological center-point criterion for the original rank-two flag

If the center exceeds the point, the original center-conjugate residual
has nontrivial normal dotted image. Movement of W identifies its ambient
commutator with the displaced point; that point and the original seed
then generate U modulo V₁ under the residual.

The literal map U/V₁ → U/Z(U) is therefore a commutator-generated central
cover for that same normal dotted image. Vanishing dual H¹ kills its
kernel and gives Z(U)=V₁. No replacement quotient or action is used.

Source: Aschbacher–Smith 12.8.13, 14.3.15 and I.1.5, printed
pp.854,994–995,408.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Representation.OneCohomology
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis κ T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hnsolv : ¬ Group.IsSolvable F.TerminalHdot)

omit [IsElementaryAbelian 2 (rankTwoSeed T M)] in
include hyp hnsolv in
private theorem normal_coinvariants_top (A : Subgroup F.TerminalHdot)
    [A.Normal] (hA : A ≠ ⊥) :
    Coinvariants.ker (F.terminalRepresentation.comp A.subtype) = ⊤ := by
  let : IsIrreducible F.terminalRepresentation := hyp.irreducible_of_not_solvable hnsolv
  let C : Subrepresentation F.terminalRepresentation := {
    toSubmodule := Coinvariants.ker (F.terminalRepresentation.comp A.subtype)
    apply_mem_toSubmodule a w hw := Coinvariants.le_comap_ker _ A a hw }
  rcases (inferInstance : IsIrreducible F.terminalRepresentation).eq_bot_or_eq_top C with he | he
  · exfalso
    apply hA
    apply le_bot_iff.mp
    intro a ha
    apply mem_bot.mpr
    apply hyp.faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    have hw := Coinvariants.sub_mem_ker (ρ := F.terminalRepresentation.comp A.subtype) ⟨a,ha⟩ w
    rw [show Coinvariants.ker (F.terminalRepresentation.comp A.subtype) = ⊥ from
      congrArg Subrepresentation.toSubmodule he,Submodule.mem_bot] at hw
    exact sub_eq_zero.mp hw
  · exact congrArg Subrepresentation.toSubmodule he

include h d hne hgP hgH hyp hnsolv

private theorem center_source_generation
    (hZ : F.ZU ≠ F.Vi 1)
    (hmove : ⁅F.W,conjugate F.ZU g⁆ = conjugate (F.Vi 1) g) :
    F.U = ⁅F.U,centerConjugateResidual F g⁆ ⊔ F.Vi 1 := by
  classical
  obtain ⟨hNH,hHN,hNC,hN⟩ := rankTwo_center_residual_geometry
    h F d hne g hgP hgH hyp hZ
  let N := centerConjugateResidual F g
  let A := F.terminalDot N
  let C := ⁅F.U,N⁆
  have hUH : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCU : C ≤ F.U := le_normalizer_iff_commutator_le_left.mp (hNH.trans hUH)
  have hHC : F.H ≤ normalizer (C : Set G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hUH ha),mem_normalizer_iff_map_conj_eq.mp (hHN ha)]
  let : (N.subgroupOf F.H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  -- A nontrivial normal image has full commutator space on the irreducible quotient.
  have hCfull : hatSpace F C = ⊤ := by
    apply top_unique
    rw [←normal_coinvariants_top F g hyp hnsolv A hN]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨b,hb,he⟩ := a.property
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
    have hw : w = Additive.ofMul (QuotientGroup.mk' (center F.U) u) := congrArg Additive.ofMul hu.symm
    rw [hw]
    let u' := F.U.normalizerMonoidHom ⟨b,hUH b.property⟩ u
    change (F.terminalRepresentation a.val _ - _).toMul ∈ hatImage F C
    refine ⟨u' * u⁻¹,?_,?_⟩
    · change ⁅(b:G),(u:G)⁆ ∈ ⁅F.U,N⁆
      rw [commutator_comm F.U N]
      exact commutator_mem_commutator hb u.property
    · rw [toMul_sub,←he,F.terminalRepresentation_apply_mk]
      change QuotientGroup.mk' (center F.U) (u' * u⁻¹) =
        F.terminalHatAction b (QuotientGroup.mk' (center F.U) u) /
          QuotientGroup.mk' (center F.U) u
      rw [F.terminalHatAction_apply_mk]
      simp only [map_mul,map_inv,div_eq_mul_inv]
      rfl

  have hs : F.U = C ⊔ F.ZU := by
    apply le_antisymm ?_ (sup_le hCU (map_subtype_le (center F.U)))
    intro u hu
    let q := QuotientGroup.mk' (center F.U)
    have hm : Additive.ofMul (q ⟨u,hu⟩) ∈ hatSpace F C := hCfull ▸ Submodule.mem_top
    obtain ⟨c,hc,he⟩ := hm
    change q c = q ⟨u,hu⟩ at he
    have hk : c⁻¹ * ⟨u,hu⟩ ∈ center F.U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (_ * _) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hh := (C ⊔ F.ZU).mul_mem (mem_sup_left hc)
      (mem_sup_right (mem_map_of_mem F.U.subtype hk))
    change (c:G) * ((c:G)⁻¹ * u) ∈ C ⊔ F.ZU at hh
    change u ∈ C ⊔ F.ZU
    simpa only [mul_inv_cancel_left] using hh
  have hg := F.conjugate_center_le_H g
    (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
  have hc := rankTwo_centers_commute h F d hne g hgP hgH
  have huc : ⁅F.U,conjugate F.ZU g⁆ ≤ C := by
    rw [hs]
    exact commutator_sup_le_of_relative_normal F.U C F.ZU (conjugate F.ZU g) C
      (normalizer_commutator_ge_left _ _) hCU (map_subtype_le (center F.U))
      (le_normalizer_iff_commutator_le_left.mp (hg.trans hHC)) (hc.le.trans bot_le)
  have hpoint : conjugate (F.Vi 1) g ≤ C := by
    rw [←hmove]
    exact (commutator_mono (show F.W ≤ F.U from inf_le_left) le_rfl).trans huc
  -- The displaced point and the H-orbit of the seed generate U modulo V₁.
  have hseed : rankTwoSeed T M ≤ C ⊔ F.Vi 1 := by
    calc
      rankTwoSeed T M = F.Vi 1 ⊔ conjugate (F.Vi 1) g :=
        F.last.symm.trans (F.plane_eq_point_join_conjugate (by decide)
          L h.L_normalizes_seed g hgP hgH)
      _ ≤ C ⊔ F.Vi 1 := sup_le le_sup_right (hpoint.trans le_sup_left)
  apply le_antisymm ?_ (sup_le hCU ((F.le_seed 1).trans (le_conjugateSpanBy _ _)))
  apply conjugateSpanBy_le hseed
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp (hHC ha),
    mem_normalizer_iff_map_conj_eq.mp ha]

/-- The literal central cover has zero kernel once all normal action images
have vanishing dual first cohomology and the displaced point is moved. -/
theorem rankTwo_center_eq_point_of_normal_cohomology
    (hmove : F.ZU ≠ F.Vi 1 → ⁅F.W,conjugate F.ZU g⁆ = conjugate (F.Vi 1) g)
    (hcoh : ∀ (A : Subgroup F.TerminalHdot) [A.Normal], A ≠ ⊥ →
      finrank (ZMod 2) (H1 (Representation.dual (F.terminalRepresentation.comp A.subtype))) = 0) :
    F.ZU = F.Vi 1 := by
  by_contra hZ
  classical
  obtain ⟨hNH,hHN,hNC,hN⟩ := rankTwo_center_residual_geometry
    h F d hne g hgP hgH hyp hZ
  let N := centerConjugateResidual F g
  let NH := N.subgroupOf F.H
  let A := F.terminalDot N
  let : NH.Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point d.two d.frattini_point
  -- Descend the action on the point quotient through the actual dotted map.
  let q₀ := QuotientGroup.mk' F.terminalHatAction.ker
  let q : NH →* A := q₀.subgroupMap NH
  have hq : Function.Surjective q := q₀.subgroupMap_surjective NH
  let α := (F.localTildeAction F.H le_rfl).comp NH.subtype
  have hk : q.ker ≤ α.ker := by
    intro a ha
    have he : (a:F.H) ∈ F.terminalHatAction.ker :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val ha)
    have hc : (a:F.H) ∈ pCore 2 F.H :=
      ((terminal_restricted_kernel_eq_core F d N hNC) ▸
        (show (a:F.H) ∈ NH ⊓ F.terminalHatAction.ker from ⟨a.property,he⟩)).2
    change (a:F.H) ∈ (F.localTildeAction F.H le_rfl).ker
    rw [d.tilde_kernel]
    exact hc
  let β : A →* MulAut (F.tilde F.U) := q.liftOfSurjective hq ⟨α,hk⟩
  have hβ (a : NH) : β (q a) = α a := q.liftOfRightInverse_comp_apply _ _ _ a
  let σ : Representation (ZMod 2) A (Additive (F.tilde F.U)) :=
    Representation.elementaryRepresentation (p := 2) β
  have hσ (a : NH) (w : Additive (F.tilde F.U)) :
      σ (q a) w = Additive.ofMul (F.localTildeAction F.H le_rfl a.val w.toMul) := by
    change Additive.ofMul (β (q a) w.toMul) = _
    rw [hβ]
    rfl
  let ρ : Representation (ZMod 2) A (Additive F.Uhat) :=
    F.terminalRepresentation.comp A.subtype
  let π := F.tildeToUhat (by decide : 1 ≤ 2)
  let p : σ.IntertwiningMap ρ :=
    π.toAdditive.toZModLinearMap 2 |>.intertwiningMap_of_isIntertwiningMap σ ρ (by
      intro a w
      obtain ⟨b,rfl⟩ := hq a
      rw [hσ]
      exact congrArg Additive.ofMul (F.tildeToUhat_equivariant (by decide) b.val w.toMul))
  -- Verify the central-cover conditions for the literal map U/V₁ → U/Z(U).
  have hp : Function.Surjective p := by
    intro w
    obtain ⟨u,hu⟩ := F.tildeToUhat_surjective (by decide : 1 ≤ 2) w.toMul
    exact ⟨Additive.ofMul u,congrArg Additive.ofMul hu⟩
  have hpfix : p.toLinearMap.ker ≤ fixed σ := by
    intro w hw a
    obtain ⟨b,rfl⟩ := hq a
    have hwZ : w.toMul ∈ (F.tilde F.ZU).subgroupOf (F.tilde F.U) := by
      rw [←F.tildeToUhat_ker (by decide)]
      exact congrArg Additive.toMul hw
    obtain ⟨z,hz,he⟩ := hwZ
    change F.tildeProjection z = (w.toMul : F.G₁tilde) at he
    rw [hσ]
    apply Additive.toMul.injective
    apply Subtype.ext
    change F.tildeProjection b.val * (w.toMul:F.G₁tilde) *
      (F.tildeProjection b.val)⁻¹ = (w.toMul:F.G₁tilde)
    rw [←he,←map_mul,←map_inv,←map_mul]
    apply congrArg F.tildeProjection
    apply Subtype.ext
    change (b.val:G)*(z:G)*(b.val:G)⁻¹ = (z:G)
    have hbz : (z:G) * (b.val:G) = (b.val:G) * (z:G) :=
      mem_centralizer_iff.mp (hNC b.property) z hz
    rw [←hbz,mul_assoc,mul_inv_cancel,mul_one]
  have hpgen : Coinvariants.ker σ = ⊤ := by
    let Q := F.tildeMap F.U F.U_le_H
    let E : Subgroup (F.tilde F.U) := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'
    let C := (E.comap Q).map F.U.subtype
    have hcomm : ⁅F.U,N⁆ ≤ C := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro a ha u hu
      let b : NH := ⟨⟨a,hNH ha⟩,ha⟩
      let uU : F.U := ⟨u,hu⟩
      let u' := F.uAction b.val uU
      refine ⟨u' * uU⁻¹,?_,rfl⟩
      change Additive.ofMul (Q (u' * uU⁻¹)) ∈ Coinvariants.ker σ
      have hm := Coinvariants.sub_mem_ker (ρ := σ) (q b) (Additive.ofMul (Q uU))
      have he : σ (q b) (Additive.ofMul (Q uU)) = Additive.ofMul (Q u') := by
        rw [hσ]
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change F.tildeProjection b.val * F.tildeProjection ⟨u,F.U_le_H hu⟩ *
          (F.tildeProjection b.val)⁻¹ = F.tildeProjection _
        rw [←map_inv,←map_mul,←map_mul]
        rfl
      rw [he] at hm
      simpa only [map_mul,map_inv,ofMul_mul,ofMul_inv,sub_eq_add_neg] using hm
    have hpoint : F.Vi 1 ≤ C := by
      intro z hz
      have hzU : z ∈ F.U := ((F.le_seed 1).trans (le_conjugateSpanBy _ _)) hz
      refine ⟨⟨z,hzU⟩,?_,rfl⟩
      change Q ⟨z,hzU⟩ ∈ E
      have he : Q ⟨z,hzU⟩ = 1 := by
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff _).mpr hz
      rw [he]
      exact E.one_mem
    have hUC : F.U ≤ C := by
      rw [center_source_generation h F d hne g hgP hgH hyp hnsolv hZ (hmove hZ)]
      exact sup_le hcomm hpoint
    apply top_unique
    intro w _
    obtain ⟨u,hu⟩ := F.tildeMap_surjective F.U F.U_le_H w.toMul
    obtain ⟨b,hb,he⟩ := hUC u.property
    have hx : Q u ∈ E := (Subtype.ext he : b=u) ▸ hb
    rw [hu] at hx
    exact hx
  -- Vanishing dual cohomology kills the central kernel of this cover.
  have hbound := finrank_ker_le_H1_of_cover p ⟨hp,hpfix,hpgen⟩
  have hzero := hcoh A hN
  have hinj : Function.Injective p.toLinearMap := LinearMap.ker_eq_bot.mp
    (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero (hzero ▸ hbound)))
  apply hZ
  apply le_antisymm ?_ (F.point_le_ZU (by decide))
  intro z hz
  have hzU := (map_subtype_le (center F.U)) hz
  let u : F.U := ⟨z,hzU⟩
  let w := F.tildeMap F.U F.U_le_H u
  have hpw : p (Additive.ofMul w) = 0 := by
    change Additive.ofMul (π w) = 0
    rw [F.tildeToUhat_apply_map]
    apply congrArg Additive.ofMul
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨c,hc,he⟩ := hz
    exact (Subtype.ext he : c=u) ▸ hc
  have hw : w = 1 := congrArg Additive.toMul
    (hinj (hpw.trans (map_zero p.toLinearMap).symm))
  have hqz : F.tildeProjection ⟨z,F.U_le_H hzU⟩ = 1 := congrArg Subtype.val hw
  have hmem : (⟨z,F.U_le_H hzU⟩ : F.H) ∈ (F.Vi 1).subgroupOf F.H :=
    (QuotientGroup.eq_one_iff _).mp hqz
  exact hmem

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
