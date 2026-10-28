module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorSuzukiContainment
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import Theory.GroupTheory.SolvableSylowContainment

/-!
# Containment of the entire original tensor section centralizer

Work in N = N_{G_z}(X), where X is normal even when it is not normal in G_z.
Its image modulo O₂(N) is the original elementary nine. Rank saturation and
the genuine SQTK classification put every C-component of N on the Suzuki
row and inside Y = C_N(X/O₂(X)). The Borel and H-star argument, now relative
to N, puts all these components in M.

Source 1.2.1(1) then puts the solvable residual of N, and hence that of Y,
in M. A solvable supplement containing the original Sylow S of Y lies in M
by the proved 8.3.6. This proves Y ≤ M without a minimal-parabolic callback.
The relative Frattini product gives N ≤ M. Quiet point escape now rules
out normality of X in G_z and makes its actual normal closure a strict
C-component orbit, retaining every original cubic Sylow and quotient marking.

The remaining nonnormal model exclusions and G_z factorization, tensor-base
recognition, strict r and point-core bounds, both quiet tensor exclusions,
and FixedSupportRowsAt/ModuleChoiceAt remain with the selected-module owner.
Final point control remains with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 8.3.7, printed pp.724--725, using 1.2.1(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem twoCore_quotient_sqtk {H : Type*} [Group H] [Finite H]
    (h : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
  refine ⟨?_,h.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

private theorem sqtk_residual_le_of_components (H : Subgroup G)
    (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hc : ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn H → K ≤ D.maximalLocal) :
    (solvableResidual H).map H.subtype ≤ D.maximalLocal := by
  have hgen : cComponentLayer H = solvableResidual H :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      (twoCore_quotient_sqtk hsq)
  rw [←hgen]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro K hK
  have he : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective K
  exact map_le_iff_le_comap.mp (hc _ ⟨map_subtype_le _,by rwa [he]⟩)

private theorem point_normalizer_sqtk {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    IsSQTK KnownSimple.IsKnownSimple (d.Gz ⊓ normalizer (d.X : Set G) : Subgroup G) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hsq := D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe (show N ≤ d.Gz from inf_le_left))).mp
    (hsq.subgroup (N.subgroupOf d.Gz))

private theorem sylow_le_point_normalizer {z : G}
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (T : Subgroup G) ≤ d.Gz ⊓ normalizer (d.X : Set G) := by
  refine le_inf hzT ?_
  rw [←quiet_point_residual_eq (T := T) (L := L) hzT]
  exact (show (T : Subgroup G) ≤ (CentralizerSetup.XT ⟨T,localOrbit T L,z⟩) from le_sup_right).trans
    (le_normalizer_embedded_pResidual 2 _)

private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide) _

/-- Inside the actual normalizer of X, every C-component centralizes the
original nine-section and has a Suzuki two-core quotient. Normality of X
in the full point centralizer is not needed. -/
theorem quiet_tensor_point_normalizer_components
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let N := d.Gz ⊓ normalizer (d.X : Set G)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn N →
      K ≤ commutatorPreimage N d.X (d.X.pCoreIn 2) ∧
      ∃ m, 1 ≤ m ∧ Nonempty
        (Chapter1.XiQuotient K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  dsimp only
  intro K hK
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  have hXN : d.X ≤ N := le_inf (d.X_le.trans inf_le_right) d.X.le_normalizer
  let B := d.X.subgroupOf N
  let : B.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (d.X : Set G) from inf_le_right)
  let q := QuotientGroup.mk' (pCore 2 N)
  let E := B.map q
  let : E.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  let b := subgroupOfEquivOfLe hXN
  let bq := QuotientGroup.congr (pCore 2 B) (pCore 2 d.X) b (pCore_map_iso 2 b)
  obtain ⟨cX⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  let cE := (Normal.isSubnormal (inferInstance : B.Normal)).quotientCoreImageEquiv 2
  let c : E ≃* Multiplicative (Fin 2 → ZMod 3) := cE.symm.trans (bq.trans cX)
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.of_injective c.toMonoidHom c.injective
  have hE : Nat.card E = 9 := by
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  let J := K.subgroupOf N
  have hJ : J.IsCComponent := hK.2
  let := hJ.perfect
  constructor
  · apply le_commutatorPreimage hK.1
    have hc := map_mono (f := N.subtype) (perfect_centralizes_normal_nine_section B hE J)
    rw [map_commutator,map_subgroupOf_eq_of_le hK.1,map_subgroupOf_eq_of_le hXN] at hc
    have he : (B.pCoreIn 2).map N.subtype = d.X.pCoreIn 2 := by
      rw [pCoreIn_subgroupOf 2 d.X N hXN,
        map_subgroupOf_eq_of_le ((d.X.pCoreIn_le 2).trans hXN)]
    rwa [he] at hc
  · let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
    obtain ⟨m,hm,⟨cJ⟩⟩ := Chapter1.Section02.cComponent_suzuki_of_normal_elementary_nine
      (twoCore_quotient_sqtk (point_normalizer_sqtk D hzV hz1))
      (pCore_quotient_pCore_eq_bot 2) E hE (hJ.map_quotient (pCore 2 N))
    let k := subgroupOfEquivOfLe hK.1
    let kq := QuotientGroup.congr (pCore 2 J) (pCore 2 K) k (pCore_map_iso 2 k)
    exact ⟨m,hm,⟨kq.symm.trans ((hJ.subnormal.quotientCoreImageEquiv 2).trans cJ)⟩⟩

/-- All components of the actual point normalizer lie in M, including
those that need not be components of the full point centralizer. -/
theorem quiet_tensor_point_normalizer_components_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn (d.Gz ⊓ normalizer (d.X : Set G)) →
      K ≤ D.maximalLocal := by
  dsimp only
  intro K hK
  obtain ⟨hKY,hm⟩ := quiet_tensor_point_normalizer_components D hn e hbase hzV hz1 hzT K hK
  exact quiet_tensor_section_suzuki_le_in D hmany hmin hn hJ cL e hbase hzV hz1 hzT
    _ (sylow_le_point_normalizer hzT) inf_le_left (commutatorPreimage_le _ _ _) K hK hKY hm

/-- The full original section centralizer lies in M. The original
Sylow S and a solvable Frattini supplement discharge its solvable part;
source component generation discharges its residual part. -/
theorem quiet_tensor_point_sectionCentralizer_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2) ≤
      D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
  have hRN := sqtk_residual_le_of_components D N (point_normalizer_sqtk D hzV hz1)
    (quiet_tensor_point_normalizer_components_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT)
  have hR : (solvableResidual Y).map Y.subtype ≤ D.maximalLocal :=
    (map_solvableResidual_mono (commutatorPreimage_le _ _ _)).trans hRN
  obtain ⟨P,hP⟩ := quiet_point_sectionCentralizer_sylow (T := T) (L := L) hzT
  apply subgroup_le_of_residual_and_solvable_sylow_overgroups Y D.maximalLocal P hR
  intro A hAY hSA hsolv
  let := hsolv
  apply quiet_tensor_solvable_overgroup_le D hn e hbase hzV hz1 hzT A
  exact (quiet_point_sectionCentralizer_sylow (T := T) (L := L) hzT).restrict
    (by rwa [hP] at hSA) hAY

/-- The entire literal normalizer N_{G_z}(X) lies in the original M. -/
theorem quiet_tensor_point_normalizer_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    d.Gz ⊓ normalizer (d.X : Set G) ≤ D.maximalLocal := by
  dsimp only
  rw [quiet_tensor_point_normalizer_factor D hJ e hbase hzV hzT]
  exact sup_le (quiet_tensor_point_sectionCentralizer_le
    D hmany hmin hn hJ cL e hbase hzV hz1 hzT) inf_le_right

/-- The normal-X case of 8.3.7 is impossible. Component containment and a
solvable Sylow supplement put the full section centralizer in M, and the
original Frattini product then contradicts quiet point escape. -/
theorem quiet_tensor_point_residual_not_normal
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    ¬ (d.X.subgroupOf d.Gz).Normal := by
  dsimp only
  intro hnormal
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  have hNM : N ≤ D.maximalLocal :=
    quiet_tensor_point_normalizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT
  have hGN : d.Gz ≤ N := le_inf le_rfl
    ((normal_subgroupOf_iff_le_normalizer (d.X_le.trans inf_le_right)).mp hnormal)
  exact quiet_point_centralizer_not_le D hmany hJ hzV hzT (hGN.trans hNM)

/-- The literal normal closure of the original cubic residual strictly
contains that residual; the normal-X alternative is discharged. -/
theorem quiet_tensor_point_normalClosure_strict
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    d.X < d.Kz := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  apply lt_of_le_of_ne d.X_le_Kz
  intro he
  apply quiet_tensor_point_residual_not_normal D hmany hmin hn hJ cL e hbase hzV hz1 hzT
  rw [he]
  exact d.Kz_normal

/-- The original normal closure is an actual C-component orbit, moved by
every prescribed original cubic Sylow. The remaining nonnormal model rows
are retained with their actual quotient isomorphisms. -/
theorem quiet_tensor_point_normalClosure_component
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let P₀ := (P : Subgroup d.X).map d.X.subtype
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn d.Gz ∧ IsQuasisimple (Chapter1.XiQuotient K) ∧
      d.Kz = componentOrbit K (T : Subgroup G) ∧ ⁅d.Kz,P₀⁆ = d.Kz ∧
      Nonempty (P₀ ≃* Chapter1.XiEmbedding.Plane 3) ∧
      ((Chapter1.XiEmbedding.SwappedFactors (T : Subgroup G) P₀ K ∧
          Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient K)) ∨
        ((T : Subgroup G) ≤ normalizer (K : Set G) ∧
          (Chapter1.XiEmbedding.LinearThreeModel 3 (Chapter1.XiQuotient K) ∨
            Chapter1.XiEmbedding.ExceptionalModel (Chapter1.XiQuotient K) ∨
            Nonempty (Chapter1.XiQuotient K ≃* Held.He)))) := by
  rcases quiet_tensor_point_normalClosure_alternatives D hn e hbase hzV hz1 hzT P with he | hc
  · exact ((quiet_tensor_point_normalClosure_strict
      D hmany hmin hn hJ cL e hbase hzV hz1 hzT).ne he.symm).elim
  · exact hc

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
