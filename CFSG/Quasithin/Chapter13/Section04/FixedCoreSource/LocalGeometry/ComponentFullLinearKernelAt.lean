module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullSixAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PointKernelAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SelectedOutside
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullCentralizer

/-!
# The full linear action kernels and normalizer at the original G,T

The actual selected natural eight detects the original normalizer residual.
Its outside image is a {2,3}-group, while the original ordinary kernel is
three-free. Two-perfectness kills the residual, proving N_G(L)=N_G(V)=LT.
The natural action then gives N_{C_G(z)}(U)=KT and both full orbit action
kernels. The orbit and its moved part lie in the original point radical.

All structural facts are guarded at the same G,T. The final cardinality
consumer is used by ComponentFullLinearAt after its full tensor exclusion,
and ComponentLinearPairAt discharges the normalizer premise internally.
Source: Aschbacher--Smith 13.3.8,13.4.6(4),13.4.10(7), pp.886--887,898,909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

open Chapter12.Section08 Section03.Noncentrality.SupercriticalSource
theorem linear_component_normalizer_supplement_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizerActionResidual L V = ⊥ ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      normalizer (V : Set G) = L ⊔ (T : Subgroup G) := by
  obtain ⟨DK,_,⟨eL⟩,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry_at
    hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  have hu := h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huK := hK12.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let M := normalizer (L : Set G)
  let R := normalizerActionResidual L V
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  obtain ⟨hM,hnR,hRC,hpR,hRz⟩ := normalizer_action_residual_at h structural D m
  have hRN : R ≤ normalizer (K : Set G) := (hRz z.val z.property).trans hHN
  have houtside : M ∈ Chapter1.HOutside G (T : Set G)
      (normalizer (K : Set G) : Set G) := by
    refine ⟨⟨Chapter1.mem_H_of_isTwoLocal hu.1.1,D.sylow_normalizes_component⟩,?_⟩
    intro hMN
    have he := hu.2 _ huK.1 (sup_le (L.le_normalizer.trans hMN) (h1332 K hfK).1)
    exact hKM (K.le_normalizer.trans he.le)
  obtain ⟨_,_,e,_,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup BinaryLinearThree.Group := Matrix.PSL3Two.equiv.isSimpleGroup
  have hc : Nat.card (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card BinaryLinearThree.Vector = 8
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have h23 := selected_eight_outside_twoThree_at hK12 structural DK eK.isSimpleGroup hc
    houtside hRM hnR hRN (hRC.trans (centralizer_le (hZ.le.trans inf_le_left)))
  have hR : R ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) := map_subtype_le _
  have h3 : ¬ 3 ∣ Nat.card R := by
    intro hd
    exact ordinary_normalizer_kernel_three_free_at h structural D m eL
      (hd.trans (card_dvd_of_le hR))
  have hid := hpR.hom_eq_one_of_isPGroup (isPGroup_two_of_isPiGroup_twoThree h23 h3)
    (MonoidHom.id R)
  have hb : normalizerActionResidual L V = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact mem_bot.mpr (congrArg (fun a : R => a.val)
      (DFunLike.congr_fun hid ⟨x,hx⟩))
  have hs : normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
    simpa only [hb,sup_bot_eq] using hM
  exact ⟨⟨eL⟩,hb,hs,(normalizer_component_eq_module_at h structural D m).symm.trans hs⟩

private theorem natural_normalizer_in_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hLK : Solvable.firstCentralizerResidual L z.val ≤ K)
    {U : Subgroup G} (DK : ChosenModule T K U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : U ≃* Multiplicative BinaryLinearThree.Vector)
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
        BinaryLinearThree.W (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ U ⊔ zpowers z.val) :
    (centralizer ({z.val} : Set G)) ⊓ normalizer (U : Set G) = K ⊔ (T : Subgroup G) ∧
      (centralizer ({z.val} : Set G)) ⊓ centralizer (U : Set G) =
        (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := centralizer ({z.val} : Set G)
  let X := K ⊔ (T : Subgroup G)
  have hTH := Solvable.original_sylow_le_centralizer hzT
  have hXH : X ≤ H := sup_le hKz hTH
  have hXU : X ≤ normalizer (U : Set G) := sup_le DK.normalizes hTU
  have hker : H ⊓ centralizer (U : Set G) ≤ X := by
    intro x hx
    have hz : x ∈ centralizer (zpowers z.val : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
      exact hx.1
    have hZc : U ⊔ zpowers z.val ≤ centralizer ({x} : Set G) :=
      sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hx.2 v hv))
        (fun v hv => mem_centralizer_singleton_iff.mpr (hz v hv))
    have hZx : x ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
      fun v hv => mem_centralizer_singleton_iff.mp (hZc (hZ hv))
    have hMx : x ∈ normalizer (L : Set G) := by
      rw [←fixed_generator_centralizer_at h structural D m
        ⟨m.constant.property,m.constant_fixed⟩
        (fun hh => m.constant_ne_one (Subtype.ext hh))]
      exact mem_centralizer_singleton_iff.mpr
        (hZx m.constant.val (m.constant_mem_central_four_at h structural).2).symm
    have hp : x ∈ Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
      rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
      exact ⟨hM ▸ hMx,hx.1⟩
    exact sup_le_sup_right hLK _ hp
  let := DK.elementary
  let ca := e.toAdditive.trans (AddEquiv.additiveMultiplicative (G := BinaryLinearThree.Vector))
  let c : Additive U ≃ₗ[ZMod 2] BinaryLinearThree.Vector :=
    { ca with map_smul' := ZMod.map_smul ca }
  let a : InvariantFlag.AmbientNaturalMarking K DK.normalizes 3 :=
    ⟨q.trans (BinaryLinear.OuterCyclic.slEquivLinear 3),c,fun k v => he k v.toMul⟩
  have hn : H ⊓ normalizer (U : Set G) = X := by
    apply le_antisymm ?_ (le_inf hXH hXU)
    intro x hx
    obtain ⟨k,hk,ha⟩ := a.full_action (U.normalizerMonoidHom ⟨x,hx.2⟩)
    have hc : k⁻¹ * x ∈ centralizer (U : Set G) := by
      intro v hv
      have hh := ha ⟨v,hv⟩
      change k * v * k⁻¹ = x * v * x⁻¹ at hh
      have hh' := congrArg (fun y : G => k⁻¹ * y * x) hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
        mul_inv_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh'
    have hm := X.mul_mem (mem_sup_left hk)
      (hker ⟨H.mul_mem (H.inv_mem (hKz hk)) hx.1,hc⟩)
    simpa only [mul_inv_cancel_left] using hm
  refine ⟨hn,?_⟩
  have hi : H ⊓ centralizer (U : Set G) = X ⊓ centralizer (U : Set G) :=
    le_antisymm (le_inf hker inf_le_right) (inf_le_inf_right _ hXH)
  exact hi.trans (chosen_linear_three_join DK hTU q e he).1

omit [Finite G] in
private theorem reduced_ambient_kernel_of_two_group
    (H W A : Subgroup G) (hWH : W ≤ H)
    (hr : IsPReduced 2 (W.subgroupOf H)) (hp : IsPGroup 2 A)
    (hC : H ⊓ centralizer (W : Set G) ≤ A) :
    H ⊓ centralizer (W : Set G) = H.pCoreIn 2 := by
  let B := W.subgroupOf H
  let := hr.normal
  let C : Subgroup H := centralizer (B : Set H)
  let f : C →* A := (H.subtype.comp C.subtype).codRestrict A (by
    intro x
    apply hC
    refine ⟨x.val.property,?_⟩
    intro w hw
    exact congrArg Subtype.val (x.property ⟨w,hWH hw⟩ hw))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) hxy
  have hc : C = pCore 2 H := le_antisymm
    (le_sSup ⟨inferInstance,hp.of_injective f hf⟩)
    (le_centralizer_iff.mp hr.le_centralizer_pCore)
  have hmap : C.map H.subtype = H ⊓ centralizer (W : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,fun w hw => congrArg Subtype.val (ha ⟨w,hWH hw⟩ hw)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,(fun w hw => Subtype.ext (hc w.val hw)),rfl⟩
  rw [←hmap,hc]
  rfl

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- The full orbit still lies in the original centralizer intersection. Its
K-moved part lies in O₂(K) and normalizes the original cubic residual. Under
the earlier M=LT conclusion the whole orbit lies in the literal O₂(L₁T). -/
theorem component_full_orbit_placement_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    let Q := ⁅W,K⁆
    let J := Solvable.firstCentralizerResidual L z.val
    W ≤ H ⊓ normalizer (L : Set G) ∧ Q ≤ K.pCoreIn 2 ∧
      Q ≤ normalizer (J : Set G) ∧ W ≤ (J ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := centralizer ({z.val} : Set G)
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let Q := ⁅W,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  let C := H ⊓ normalizer (L : Set G)
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨hrW,_,_,_,_,_,_,hQW,hnQ,_⟩ := component_full_orbit_at h₀ h structural
    D m hindex z hzT hzL hKz hHN hKM
  have hWH : W ≤ H := Solvable.centralizerOmegaOrbit_le hzT
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 H).to_le
    (Solvable.centralizerOmegaOrbit_le_core h₀ hzT hz1)
  let : IsElementaryAbelian 2 (W.subgroupOf H) := hrW.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf H).map H.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hWH] at hh
  have hWC : W ≤ C := le_inf hWH
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizerOmegaOrbit_centralizer_le_normalizer_at h structural D m z.val))
  have hQK : Q ≤ K := le_normalizer_iff_commutator_le_right.mp (hWH.trans hHN)
  have hQcore : Q ≤ K.pCoreIn 2 := le_pCoreIn_of_normalizes (hpW.to_le hQW) hQK
    (hKz.trans hnQ)
  have hJn : C ≤ normalizer (J : Set G) := by
    change C ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G)
    rw [←Solvable.firstCentralizerResidual_eq_intersection_residual z.val
      (original_normalizer_residual_at h structural eL)]
    exact C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))
  have hC : C = J ⊔ (T : Subgroup G) := by
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    change H ⊓ normalizer (L : Set G) = _
    rw [hM,inf_comm]
  have hWcore : W ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes hpW hWC
    (inf_le_left.trans (le_normalizer_conjugateSpanBy _ H))
  exact ⟨hWC,hQcore,hQW.trans (hWC.trans hJn),hC ▸ hWcore⟩

/-- The selected natural three-space has normalizer KT inside the full
centralizer. Its centralizer is the original O₂(KT). The full centralizer
orbit and its K-moved subgroup both have kernel O₂(C_G(z)). -/
theorem linear_component_full_orbit_kernels_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let H := centralizer ({z.val} : Set G)
    let X := K ⊔ (T : Subgroup G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := ⁅conjugateSpanBy Z K,K⁆
    let W := conjugateSpanBy Z H
    let Q := ⁅W,K⁆
    H ⊓ normalizer (U : Set G) = X ∧
      H ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
      H ⊓ centralizer (W : Set G) = H.pCoreIn 2 ∧
      H ⊓ centralizer (Q : Set G) = H.pCoreIn 2 ∧
      H.pCoreIn 2 ≤ X.pCoreIn 2 ∧
      W ≤ H ⊓ normalizer (L : Set G) ∧ Q ≤ K.pCoreIn 2 ∧
      Q ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G) ∧
      W ≤ (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := centralizer ({z.val} : Set G)
  let X := K ⊔ (T : Subgroup G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let W := conjugateSpanBy Z H
  let Q := ⁅W,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (Solvable.original_sylow_le_centralizer hzT).trans hHN
  obtain ⟨DK,q,e,he,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨eL⟩ := ordinary_original_of_linear_component_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hLK := (ordinary_linear_component_residuals_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK eL).1
  have hredU := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hXU : X ≤ normalizer (U : Set G) := le_normalizer_of_normal_subgroupOf
    (DK.le_reduced.trans (map_subtype_le _)) (hK := hredU.normal)
  have hs := component_seed_split h₀ hzT hz1 hKz hTK
  rw [component_full_fixed_line_at h structural z.val hz1 hzT hindex K hKz hKM] at hs
  have hZU : Z ≤ U ⊔ zpowers z.val := hs ▸ le_conjugateSpanBy Z K
  obtain ⟨hn,hc⟩ := natural_normalizer_in_centralizer h structural D m eL hM z hzT hzL
    hKz hLK DK (le_sup_right.trans hXU) q e he hZU
  obtain ⟨hrW,_,_,_,_,_,hUQ,hQW,_,heq⟩ := component_full_orbit_at h₀ h structural
    D m hindex z hzT hzL hKz hHN hKM
  have hb : H ⊓ centralizer (W : Set G) ≤ X.pCoreIn 2 := by
    rw [←hc]
    exact inf_le_inf_left H (centralizer_le (hUQ.trans hQW))
  have hWH : W ≤ H := conjugateSpanBy_le_self
    (fun _ hv => Solvable.original_sylow_le_centralizer hzT
      ((mem_omegaOneCenterAmbient_iff _ _).mp hv).1)
  have hk := reduced_ambient_kernel_of_two_group H W (X.pCoreIn 2) hWH hrW
    (isPGroup_pCoreIn 2 X) hb
  exact ⟨hn,hc,hk,heq.symm.trans hk,hk ▸ hb,
    component_full_orbit_placement_at h₀ h structural D m hindex eL hM z hzT hzL hKz hHN hKM⟩

/-- Once the full-centralizer moved orbit has natural dimension, the actual
normalizer computation gives C_G(z)=KT, identifies its quotient, and shows
that enlarging the original seed orbit did not change it. The bound on the
full orbit remains the tensor-row exclusion in source 13.4.10(7). -/
theorem linear_full_centralizer_of_full_moved_card_le_eight_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hsmall : Nat.card (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G))
      (centralizer ({z.val} : Set G)),K⁆ : Subgroup G) ≤ 8) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    H = K ⊔ (T : Subgroup G) ∧
      conjugateSpanBy Z H = conjugateSpanBy Z K ∧
      ⁅conjugateSpanBy Z H,K⁆ = ⁅conjugateSpanBy Z K,K⁆ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) := by
  let H := centralizer ({z.val} : Set G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let Q := ⁅conjugateSpanBy Z H,K⁆
  obtain ⟨DK,q,e,_,_,_,_,_⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hcard : Nat.card U = 8 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card BinaryLinearThree.Vector = 8
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  obtain ⟨_,_,_,_,_,_,hUQ,_,hn,_⟩ := component_full_orbit_at h₀ h structural
    D m hindex z hzT hzL hKz hHN hKM
  have hU : U = Q := eq_of_le_of_card_ge hUQ (by simpa only [hcard] using hsmall)
  have hnorm := (linear_component_full_orbit_kernels_at hl h₀ h structural modules
    D m h1332 fixed hindex hM z hzT hzL hKz hHN hKM hfK eK).1
  have hnU : H ≤ normalizer (U : Set G) := by
    rw [hU]
    exact hn
  have hH : H = K ⊔ (T : Subgroup G) := by
    rw [←hnorm]
    exact (inf_eq_left.mpr hnU).symm
  have hTK := (Solvable.original_sylow_le_centralizer hzT).trans hHN
  have hseed : conjugateSpanBy Z H = conjugateSpanBy Z K := by
    rw [hH]
    exact conjugateSpanBy_sup_of_normalizes_seed Z K (T : Subgroup G)
      ((le_centralizer_iff.mp (fun _ hz => (mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2)).trans
        (Subgroup.centralizer_le_normalizer _)) hTK
  have hquot := (linear_component_whole_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK).2.2.2.2
  refine ⟨hH,hseed,hU.symm,?_⟩
  change Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group)
  rw [hH]
  exact hquot

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
