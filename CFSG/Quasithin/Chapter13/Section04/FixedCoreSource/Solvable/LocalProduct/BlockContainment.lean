module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.BlockAction
public import Theory.Representation.BinaryPermutation.SixCoreResidualSubmodules
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups

/-!
# The original residual moved space in the centralizer module

The short-block hypothesis identifies U(L) with the original chosen V.
Its Sylow module centralizer Q=C_T(V) therefore satisfies [Q,L]≤V.
Under the centralizing Thompson alternative and the earlier V≤J(R₁),
V_H lies in Q, so [V_H,L₁] lies in V∩V_H. In the two-core action-kernel
branch the actual cubic divisor of |L₁| prevents this commutator from
vanishing. Two-perfect commutator idempotence shows that L₁ moves V∩V_H.
The six-letter invariant-subspace calculation, transported through the
literal C_L(z) action, then gives [V,L₁]≤V_H.

This discharges the moved-space premise of BlockAction. When O₂(L)=V,
the centralizing Thompson assumption also gives O₂(L)≤C_G(V_H), proving
noncentrality and applying the existing S₃ quotient and moved-plane theorem
to the actual Thompson span. In the remaining O₂(L)>V case, the separate
C.1.13(d) core-centralizer argument is still required. No core equality
is asserted for that case. The larger action kernel and the remaining
13.4.8–9 assembly stay with qt-d-1341-solvable-source; the earlier-source
inputs retain final discharge with qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.8, printed p.904, and C.1.11–13, pp.124–125.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The actual chosen module is the short block's entire commutator layer. -/
theorem chosen_eq_block_layer (D : ChosenModule T L V) (hb : ChapterC.IsShort L) :
    (ChapterC.blockU L).map L.subtype = V := by
  let N := V.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  have hVU : V ≤ (ChapterC.blockU L).map L.subtype := by
    rw [D.eq_commutator,ChapterC.blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    exact commutator_mono D.le_componentCore le_rfl
  have hNU : N ≤ ChapterC.blockU L := by
    intro v hv
    exact (mem_map_iff_mem L.subtype_injective).mp (hVU hv)
  rcases ChapterC.RankOne.ChiProduct.short_normal_layer_dichotomy hb N hNU with hc | he
  · have hcen : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      exact congrArg Subtype.val (mem_center_iff.mp
        (hc (show (⟨v,D.le_component hv⟩ : L) ∈ N from hv)) ⟨l,hl⟩)
    exact (D.ne_bot (D.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hcen))).elim
  · have hh := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le D.le_component] at hh
    exact hh.symm

/-- The block's Sylow module centralizer has displacement contained in the original V. -/
theorem sylow_module_centralizer_commutator_le_chosen
    (D : ChosenModule T L V) (hb : ChapterC.IsShort L) :
    ⁅(T : Subgroup G) ⊓ centralizer (V : Set G),L⁆ ≤ V := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQ : (T : Subgroup G) ⊓ centralizer (V : Set G) = Q := by
    rw [← chosen_eq_block_layer D hb]
    exact hb.sylow_centralizer_blockU_eq_pCoreIn D.sylow_normalizes_component
  rw [hQ]
  have hLQ : L ≤ normalizer (Q : Set G) := le_sup_left.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQL : Q ≤ normalizer (L : Set G) :=
    (hQ.symm.le.trans inf_le_left).trans D.sylow_normalizes_component
  have hcomm : ⁅Q,L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 _).to_le (le_normalizer_iff_commutator_le_left.mp hLQ))
    (le_normalizer_iff_commutator_le_right.mp hQL) (normalizer_commutator_ge_right Q L)
  have hid := commutator_isPPerfect_idempotent L Q hb.twoPerfect (isPGroup_pCoreIn 2 _) hLQ
  rw [← chosen_eq_block_layer D hb,ChapterC.blockU,map_commutator,
    ← MonoidHom.range_eq_map,range_subtype]
  exact hid.symm.le.trans (commutator_mono hcomm le_rfl)

/-- A noncentral invariant part of the five-space contains the original residual's moved space. -/
theorem firstCentralizerResidual_moved_le_invariant
    (D : ChosenModule T L V) (m : CoreMarking D) (z : V)
    (hzL : z.val ∉ centralizer (L : Set G))
    (N : Subgroup G) (hNV : N ≤ V)
    (hn : L ⊓ centralizer ({z.val} : Set G) ≤ normalizer (N : Set G))
    (hm : ¬ firstCentralizerResidual L z.val ≤ centralizer (N : Set G)) :
    ⁅V,firstCentralizerResidual L z.val⁆ ≤ N := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let w := (m.coordinate z).toAdd
  obtain ⟨f,hf,_,he⟩ := component_centralizer_action D m z
  let U : Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)) :=
    AddSubgroup.toZModSubmodule 2
      ((N.subgroupOf V).map m.coordinate.toMonoidHom).toAddSubgroup'
  have hmem (v : V) : (m.coordinate v).toAdd ∈ U ↔ v.val ∈ N := by
    change m.coordinate v ∈ (N.subgroupOf V).map m.coordinate.toMonoidHom ↔ _
    exact mem_map_iff_mem (f := m.coordinate.toMonoidHom) m.coordinate.injective
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro h
    exact hzL ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) w).mp h))
  have hU : ∀ a : BinaryPermutation.SixCoreStabilizer.stabilizer w,
      ∀ v ∈ U, BinaryPermutation.alternatingCoreRepresentation (Fin 6) a.val v ∈ U := by
    intro a v hv
    obtain ⟨c,rfl⟩ := hf a
    let u := m.coordinate.symm (Multiplicative.ofAdd v)
    have hu : u.val ∈ N := (hmem u).mp (by simpa only [u,MulEquiv.apply_symm_apply,toAdd_ofAdd] using hv)
    have hh := (hmem (V.normalizerMonoidHom ⟨c.val,D.normalizes c.property.1⟩ u)).mpr
      (le_normalizer_iff.mp hn c.val c.property u.val hu)
    rw [he] at hh
    simpa only [u,MulEquiv.apply_symm_apply,toAdd_ofAdd] using hh
  have hmove : ∃ a : BinaryPermutation.SixCoreStabilizer.stabilizer w,
      a ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) ∧
      ∃ v ∈ U, BinaryPermutation.alternatingCoreRepresentation (Fin 6) a.val v ≠ v := by
    classical
    by_contra! hh
    apply hm
    intro a ha n hnN
    rw [firstCentralizerResidual_eq] at ha
    obtain ⟨c,hc,rfl⟩ := ha
    have hfc : f c ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) := by
      rw [← map_primeToResidual_of_surjective 3 f hf]
      exact mem_map_of_mem f hc
    let v : V := ⟨n,hNV hnN⟩
    have heq := (he c v).trans (hh (f c) hfc (m.coordinate v).toAdd ((hmem v).mpr hnN))
    have hval := congrArg Subtype.val (m.coordinate.injective (Multiplicative.toAdd.injective heq))
    exact (mul_inv_eq_iff_eq_mul.mp hval).symm
  have hfull := BinaryPermutation.SixCoreResidualSubmodules.residual_displacements_mem w hfix U hU hmove
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha v hv
  rw [firstCentralizerResidual_eq] at ha
  obtain ⟨c,hc,rfl⟩ := ha
  have hfc : f c ∈ primeToResidual 3 (BinaryPermutation.SixCoreStabilizer.stabilizer w) := by
    rw [← map_primeToResidual_of_surjective 3 f hf]
    exact mem_map_of_mem f hc
  let v₀ : V := ⟨v,hv⟩
  let d : V := V.normalizerMonoidHom ⟨c.val,D.normalizes c.property.1⟩ v₀ * v₀⁻¹
  have hd : (m.coordinate d).toAdd ∈ U := by
    change (m.coordinate (_ * _)).toAdd ∈ U
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,← sub_eq_add_neg,he]
    exact hfull (f c) hfc (m.coordinate v₀).toAdd
  exact (hmem d).mp hd


/-- In the two-core-kernel branch, the centralizing Thompson alternative forces
 the full residual moved space into the actual V_H. -/
theorem firstCentralizerResidual_moved_le_orbit_of_centralizing_thompson
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) (z : V)
    (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G))) :
    ⁅V,firstCentralizerResidual L z.val⁆ ≤ centralizerOmegaOrbit T z.val := by
  let H := centralizer ({z.val} : Set G)
  let U := centralizerOmegaOrbit T z.val
  let A := firstCentralizerResidual L z.val
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hAH : A ≤ H := (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hAL : A ≤ L := (firstCentralizerResidual_le L z.val).trans inf_le_left
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hAU := hAH.trans hHU
  have hUT : U ≤ T := (centralizerOmegaOrbit_le_core h₀ hz hz1).trans (by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH))
  have hUV : U ≤ centralizer (V : Set G) := le_centralizer_iff.mp (hVJ.trans hJ)
  have hWL : ⁅U,A⁆ ≤ V :=
    (commutator_mono (le_inf hUT hUV) hAL).trans
      (sylow_module_centralizer_commutator_le_chosen D hb)
  have hWU : ⁅U,A⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hAU
  have hpU : IsPGroup 2 U := T.isPGroup'.to_le hUT
  have hid := commutator_isPPerfect_idempotent A U
    (firstCentralizerResidual_twoPerfect L z.val) hpU hAU
  obtain ⟨e⟩ := ordinary
  have hc := centralCore_eq_twoCore_of_ordinary e
  have hcore : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) :=
    hc ▸ pCore_isPGroup
  have hthree := (firstCentralizerResidual_order_of_core_marking D m hcore z hzL).2
  have hnon := firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree
  have hm : ¬ A ≤ centralizer ((V ⊓ U : Subgroup G) : Set G) := by
    intro hc
    have he : ⁅⁅U,A⁆,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      ((le_inf hWL hWU).trans (le_centralizer_iff.mp hc))
    apply hnon
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hid.symm.trans he))
  have hn : L ⊓ H ≤ normalizer ((V ⊓ U : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans D.normalizes) (inf_le_right.trans hHU)).trans
      inf_normalizer_le_normalizer_inf
  exact (firstCentralizerResidual_moved_le_invariant D m z hzL (V ⊓ U)
    inf_le_left hn hm).trans inf_le_right

/-- The block movement theorem discharges the moved-space premise in the existing
 action contradiction. The separate C.1.13(d) core-centralizer bound remains explicit. -/
theorem centralizer_thompson_noncentral_of_short_core_bound
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hLc : L.pCoreIn 2 ≤ centralizer (centralizerOmegaOrbit T z.val : Set G)) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  intro hJ
  exact firstCentralizerResidual_moved_not_le_orbit h₀ D m ordinary z hz hzL hsolv hkernel hLc
    (firstCentralizerResidual_moved_le_orbit_of_centralizing_thompson h₀ D m hb ordinary z hz hzL R hVJ hJ hkernel)

/-- The U(L)=O₂(L) branch of C.1.13(d) discharges the core-centralizer
 bound directly in the centralizing Thompson contradiction. -/
theorem centralizer_thompson_noncentral_of_core_eq_chosen
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hcore : L.pCoreIn 2 = V) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  intro hJ
  have hLc : L.pCoreIn 2 ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) :=
    hcore.le.trans (hVJ.trans hJ)
  exact centralizer_thompson_noncentral_of_short_core_bound h₀ D m hb ordinary
    z hz hzL hsolv R hVJ hkernel hLc hJ

/-- The actual Thompson span has its S₃ quotient and moved plane in the short-block
 branch once the remaining C.1.13(d) core-centralizer input is supplied. -/
theorem centralizer_single_factor_data_of_short_core_bound
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hLc : L.pCoreIn 2 ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hAN : firstCentralizerResidual L z.val ≤ normalizer (R : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 := by
  have hJ := centralizer_thompson_noncentral_of_short_core_bound h₀ D m hb ordinary
    z hz hzL hsolv R hVJ hkernel hLc
  obtain ⟨e⟩ := ordinary
  have hc := centralCore_eq_twoCore_of_ordinary e
  have hcore : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) :=
    hc ▸ pCore_isPGroup
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore z hzL
  exact centralizer_thompson_single_factor_data_of_firstResidual h₀ hz
    (fun he => hzL (he ▸ one_mem _)) R hRT hnR hQR hJ hsolv hkernel ho hthree hAN

/-- The S₃ quotient and moved plane in the block branch with O₂(L)=V,
 with both geometric premises of the action contradiction discharged. -/
theorem centralizer_single_factor_data_of_core_eq_chosen
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hcore : L.pCoreIn 2 = V)
    (hAN : firstCentralizerResidual L z.val ≤ normalizer (R : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 := by
  have hJ := centralizer_thompson_noncentral_of_core_eq_chosen h₀ D m hb ordinary
    z hz hzL hsolv R hVJ hkernel hcore
  obtain ⟨e⟩ := ordinary
  have hc := centralCore_eq_twoCore_of_ordinary e
  have hp : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) :=
    hc ▸ pCore_isPGroup
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hp z hzL
  exact centralizer_thompson_single_factor_data_of_firstResidual h₀ hz
    (fun he => hzL (he ▸ one_mem _)) R hRT hnR hQR hJ hsolv hkernel ho hthree hAN

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
