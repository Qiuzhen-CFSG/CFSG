module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankCubic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ActorRankIntersection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterPoint
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.SingularPlane
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Assembly

/-!
# The original orthogonal intersection in the rank-two parabolic

The full orthogonal action has no Sylow-invariant totally singular plane.
The actual intersection therefore has one-dimensional image modulo the center,
and is precisely the original seed. The local kernel intersection then gives
`O₂(H) ∩ Uᵍ = V`, with the quotient maps and conjugate closure unchanged.
The final theorem applies this to the original cubic Fitting branch.

Source: Aschbacher--Smith, 14.3.18(1), printed pp.995--996.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- In the full orthogonal source branch, the original intersection is the seed. -/
theorem intersection_eq_seed_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    (hne : ¬IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    F.E g = rankTwoSeed T M := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) (sourceResidual M Mc)
      h.L_normalizes_seed d.seed_center g hgP hgH).1
  obtain ⟨hs,hQ,hnd⟩ := quadratic_intersection_of_center_point F d (by decide) hZ g hdis
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (f:=QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hinv : ∀ t∈(P:Subgroup F.TerminalHdot), ∀ v∈hatSpace F (F.E g),
      F.terminalRepresentation t v∈hatSpace F (F.E g) :=
    rankTwo_terminal_intersection_invariant h F hne g hgP hgH
  have hform : ∀ t v, centerPointQuadraticForm F d (by decide) hZ
      (F.terminalRepresentation t v)=centerPointQuadraticForm F d (by decide) hZ v := by
    intro t v
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker t
    exact hQ a v.toMul
  have hb : finrank (ZMod 2) (hatSpace F (F.E g)) ≤ 1 := by
    by_contra hbad
    have hd : 2≤finrank (ZMod 2) (hatSpace F (F.E g)) := by omega
    obtain ⟨C,hCn,hCc⟩ := ChapterG.Section09.FittingRecognition.Four.normal_cubic_of_orthogonal_singular_plane
      F.terminalRepresentation ⊤ le_top hr (centerPointQuadraticForm F d (by decide) hZ)
      hnd hform P (hatSpace F (F.E g)) hd hs hinv
    let := hCn
    exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ C hCc
  have hVE : rankTwoSeed T M≤F.E g := F.seed_le_E_of_normalizes g
    (F.P_le_seed_normalizer (sourceResidual M Mc) h.L_normalizes_seed hgP)
  have hv : finrank (ZMod 2) (hatSpace F (rankTwoSeed T M))=1 :=
    (congrArg (fun A : Subgroup G => finrank (ZMod 2) (hatSpace F A)) F.last).symm.trans
      (finrank_hatSpace_plane F (by decide) d.seed_center)
  have hle : hatSpace F (rankTwoSeed T M)≤hatSpace F (F.E g) := by
    rintro v ⟨u,hu,rfl⟩
    exact ⟨u,hVE hu,rfl⟩
  have heq : hatSpace F (rankTwoSeed T M)=hatSpace F (F.E g) :=
    Submodule.eq_of_le_of_finrank_le hle (by simpa only [hv] using hb)
  apply le_antisymm ?_ hVE
  intro x hx
  let u : F.U := ⟨x,(show F.E g≤F.U from inf_le_left.trans inf_le_left) hx⟩
  have hum : Additive.ofMul (QuotientGroup.mk' (center F.U) u)∈hatSpace F (F.E g) :=
    ⟨u,hx,rfl⟩
  rw [←heq] at hum
  obtain ⟨v,hv,he⟩ := hum
  have hk : v⁻¹*u∈center F.U := by
    apply (QuotientGroup.eq_one_iff (N:=center F.U) (v⁻¹*u)).mp
    change QuotientGroup.mk' (center F.U) (v⁻¹*u)=1
    rw [map_mul,map_inv,he]
    exact inv_mul_cancel _
  have hz : ((v⁻¹*u:F.U):G)∈rankTwoSeed T M :=
    (show F.ZU≤rankTwoSeed T M from hZ ▸ F.le_seed 1) ⟨v⁻¹*u,hk,rfl⟩
  have hx' := (rankTwoSeed T M).mul_mem hv hz
  change (v:G)*((v:G)⁻¹*x)∈rankTwoSeed T M at hx'
  simpa only [mul_inv_cancel_left] using hx'

/-- The conjugate closure meets the point normalizer in its plane centralizer. -/
theorem conjugate_U_inf_H_eq_X
    {T : Sylow 2 G} {V L : Subgroup G}
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V]
    (hL : L≤normalizer (V:Set G))
    (g : G) (hgP : g∈F.P L) (hgH : g∉F.H) :
    conjugate F.U g ⊓ F.H=F.X g := by
  have hgG := F.P_le_G₂ (by decide) L hL hgP
  have hH : F.H≤centralizer (F.Vi 1:Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hc : F.U≤centralizer (F.Vi 1:Set G) :=
    le_centralizer_iff.mp ((F.point_le_ZU (by decide)).trans (centerIn_le_centralizer F.U))
  have hcg : conjugate F.U g≤centralizer (conjugate (F.Vi 1) g:Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [conjugate,conjugate,←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr hc,Subgroup.map_bot]
  rw [X_eq_conjugate_U_inf F g hgG]
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    apply le_centralizer_iff.mp
    rw [←F.binary_plane_point_span (by decide) L hL g hgP hgH]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans hH))
      (le_centralizer_iff.mp (inf_le_left.trans hcg))
  · exact le_inf inf_le_left ((X_eq_conjugate_U_inf F g hgG).symm.le.trans (F.X_le_H g hgG))

/-- Original 14.3.18(1), with Q the actual embedded local two-core. -/
theorem core_inf_conjugate_U_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    (hne : ¬IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    F.H.pCoreIn 2 ⊓ conjugate F.U g=rankTwoSeed T M := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hnat : 3≤2→Nonempty (AmbientNaturalMarking (sourceResidual M Mc) h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE (sourceResidual M Mc) M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  have hk := (F.binary_source_action_kernel_intersections (by decide) (sourceResidual M Mc)
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne
    d.seed_center g hgP hgH).1
  change F.X g ⊓ F.terminalHatAction.ker.map F.H.subtype=F.E g at hk
  rw [terminal_kernel_of_center_point F d hZ] at hk
  have hX := conjugate_U_inf_H_eq_X F h.L_normalizes_seed g hgP hgH
  have he := intersection_eq_seed_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
    F d hZ hne g hgP hgH hr
  apply Eq.trans ?_ (hk.trans he)
  rw [←hX]
  change F.H.pCoreIn 2 ⊓ conjugate F.U g=
    (conjugate F.U g ⊓ F.H) ⊓ F.H.pCoreIn 2
  have hcore : F.H.pCoreIn 2≤F.H := map_subtype_le _
  apply le_antisymm
  · exact fun x hx => ⟨⟨hx.2,hcore hx.1⟩,hx.1⟩
  · exact fun x hx => ⟨hx.2,hx.1.1⟩
/-- The cubic Fitting branch supplies the full marking internally in the
literal original 14.3.18(1) consumer. -/
theorem core_inf_conjugate_U_of_center_point_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T=∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G))={Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (T:Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M)=4)
    (e : (M⧸(centralizer (localModule T M:Set G)).subgroupOf M)≃*Equiv.Perm (Fin 3))
    (hnot : ¬ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬IsMulCommutative F.U) (hZ : F.ZU=F.Vi 1)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot))
    (hs : Group.IsSolvable F.TerminalHdot) (hX : F.terminalDot (F.X g)≠⊥)
    (hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,F.terminalDot (F.X g)⁆ : Subgroup F.TerminalHdot)) :
    F.H.pCoreIn 2 ⊓ conjugate F.U g=rankTwoSeed T M := by
  have hr := full_orthogonal_of_center_point_cubic hG T hempty hM hu hmany hcard e hnot
    F d hne hZ g hgP hgH hyp cover hs hX hc
  exact core_inf_conjugate_U_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
    F d hZ hne g hgP hgH hr

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
