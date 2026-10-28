module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallEnlargementKernel
public import Theory.Representation.BinaryOffender.SmallFixedCodimension
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Theory.Representation.SpecialLinearNatural
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# The original module in the second center of the enlargement core

The actual containing-core image is elementary and preserves the two original
binary three-spaces. Its action on each space is quadratic: a two-group fixes
a nonzero vector, leaving fixed codimension at most two. The exact original
coordinates transfer this to `[[V,Q],Q]=1`.

The collapsed parabolic factorization `O₂(H)=Q O₂(L₀T)` and the original
action kernel transfer the same quadratic action to `R=O₂(E)`. Together
with the proved absorption `V≤R`, this puts V in the literal second center
of R. The nontrivial commutator lies in `Ω₁Z(R)∩Φ(R)`; it is not declared
characteristic, and no centralization of V by R is inferred.
Source: the original binary natural geometry in Aschbacher--Smith 10.2.5,
printed p.748, and elementary binary quadratic action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise Matrix commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Representation Representation.BinaryOffender

private theorem three_quadratic {A W : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hd : Module.finrank (ZMod 2) W = 3) :
    IsQuadratic ρ ⊤ := by
  have hne : (⊤ : Submodule (ZMod 2) W) ≠ ⊥ := by
    intro he
    have hh := congrArg (fun S : Submodule (ZMod 2) W => Module.finrank (ZMod 2) S) he
    simp only [finrank_top,finrank_bot,hd] at hh
    omega
  obtain ⟨v,_,hv,hfix⟩ := PermutedSupports.exists_nonzero_fixed ρ ⊤
    ((IsElementaryAbelian.isPGroup 2 A).to_subgroup ⊤) ⊤ hne (by
      apply le_subspaceStabilizer
      intro a ha w hw
      trivial)
  let : Nontrivial (fixedSpace ρ ⊤) := nontrivial_of_ne
    (⟨v,hfix⟩ : fixedSpace ρ ⊤) 0 (fun he => hv (congrArg Subtype.val he))
  have hpos := Module.finrank_pos (R := ZMod 2) (M := fixedSpace ρ ⊤)
  have hsum := fixedCodim_add_finrank ρ ⊤
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype (⊤ : Subgroup A).subtype_injective
  apply isQuadratic_of_fixedCodim_le_two
  omega

private def coordinateHom (U : Subgroup Actor) (hr : ∀ u ∈ U, u.right = 1)
    (i : Bit) : U →* Matrix.PSL3Two.SL where
  toFun u := u.val.left i
  map_one' := rfl
  map_mul' u v := by simp [hr u u.property]

private theorem base_quadratic (U : Subgroup Actor) [IsElementaryAbelian 2 U]
    (hr : ∀ u ∈ U, u.right = 1) (a b : U) (v : Space) :
    action a (action b v * v⁻¹) = action b v * v⁻¹ := by
  funext i
  let ρ := (specialLinearNatural 3).comp (coordinateHom U hr i)
  have hq := three_quadratic ρ (by simp)
  have hh := hq a (mem_top a) b (mem_top b) (v i).toAdd
  change (a.val.left i).val *ᵥ ((b.val.left i).val *ᵥ (v i).toAdd - (v i).toAdd) =
    (b.val.left i).val *ᵥ (v i).toAdd - (v i).toAdd at hh
  simp only [action_apply,hr a a.property,hr b b.property,inv_one,one_mul,
    Pi.mul_apply,Pi.inv_apply]
  exact congrArg Multiplicative.ofAdd (by simpa only [sub_eq_add_neg,toAdd_mul,toAdd_inv,toAdd_ofAdd] using hh)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

private theorem core_lift_elementary (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    IsElementaryAbelian 2
      ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map f.hom) := by
  let A := ((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)
  let U := A.map f.hom
  let : IsElementaryAbelian 2 (A.map (joinAction D)) := h.core_action_elementary f hi hP
  have hsquare (u : U) : u ^ 2 = 1 := by
    obtain ⟨q,hq,he⟩ := u.property
    have hq2 : q ^ 2 ∈ (joinAction D).ker := by
      change joinAction D (q ^ 2) = 1
      rw [map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (mem_map_of_mem (joinAction D) hq)
    rw [←f.kernel_eq_action_kernel] at hq2
    apply Subtype.ext
    change (u : Actor) ^ 2 = 1
    rw [←he,←map_pow]
    exact hq2
  exact {
    toIsMulCommutative := ⟨⟨fun u v => Commute.of_orderOf_dvd_two
      (fun w => orderOf_dvd_of_pow_eq_one (hsquare w)) u v⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

/-- The elementary containing-core image acts quadratically on both actual
three-dimensional factors of the original module. -/
theorem Data.core_module_second_commutator
    (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    ⁅⁅D.fullModule,(enlargedResidual T L H).pCoreIn 2⁆,
      (enlargedResidual T L H).pCoreIn 2⁆ = ⊥ := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let J := localJoin T L
  let U := (Q.subgroupOf J).map f.hom
  let : IsElementaryAbelian 2 U := core_lift_elementary h f hi hP
  have hQJ : Q ≤ J := h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
  have hr : ∀ u ∈ U, u.right = 1 := by
    rintro _ ⟨q,hq,rfl⟩
    exact f.right_eq_one_of_normalizes q (h.enlargedResidual_core_le_intersection hq).1.2
  rw [commutator_comm D.fullModule Q]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply commutator_le.mpr
  intro q hq v hv r hrQ
  let q' : J := ⟨q,hQJ hq⟩
  let r' : J := ⟨r,hQJ hrQ⟩
  let v' : D.fullModule := ⟨v,hv⟩
  let d := joinAction D q' v' * v'⁻¹
  have hd : joinAction D r' d = d := by
    apply (fullCoordinates s hz).injective
    rw [f.equivariant]
    have hc : fullCoordinates s hz d =
        action (f.hom q') (fullCoordinates s hz v') * (fullCoordinates s hz v')⁻¹ := by
      dsimp only [d]
      rw [map_mul,map_inv,f.equivariant]
    rw [hc]
    exact base_quadratic U hr ⟨f.hom r',mem_map_of_mem f.hom hrQ⟩
      ⟨f.hom q',mem_map_of_mem f.hom hq⟩ (fullCoordinates s hz v')
  have he := congrArg Subtype.val hd
  change r * ⁅q,v⁆ * r⁻¹ = ⁅q,v⁆ at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The enlargement core and the containing core have the same literal
commutator with the original module. -/
theorem Data.enlargement_module_commutator_eq
    (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ =
      ⁅D.fullModule,(enlargedResidual T L H).pCoreIn 2⁆ := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let R := (enlargement T L H).pCoreIn 2
  let R₀ := (localJoin T L).pCoreIn 2
  have hQR : Q ≤ R := pCoreIn_mono_of_normalizes h.enlargedResidual_le_enlargement
    (le_normalizer_conjugateSpanBy _ _)
  have hRQ : R ≤ Q ⊔ R₀ := h.enlargement_core_le_parabolic_core.trans
    (h.collapsed_parabolic_core_eq_join f hi hP hc).le
  have hR₀Q : R₀ ≤ normalizer (Q : Set G) :=
    ((join_core_le_stabilizer D).trans (inf_le_left.trans (h.sylow_le.trans le_sup_right))).trans
      (enlargement_normalizes_core T L H)
  have hR₀C : R₀ ≤ centralizer (D.fullModule : Set G) := by
    rintro _ ⟨q,hq,rfl⟩
    rw [←f.kernel_eq_join_core,f.kernel_eq_action_kernel,joinAction_ker] at hq
    exact hq
  apply le_antisymm ?_ (commutator_mono le_rfl hQR)
  apply commutator_le.mpr
  intro v hv r hr
  have hrprod : r ∈ (Q : Set G) * (R₀ : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q R₀ hR₀Q]
    exact hRQ hr
  obtain ⟨q,hq,c,hc,he⟩ := hrprod
  rw [←he,commutatorElement_mul_right_eq_mul_conj,
    (mem_centralizer_iff_commutator_eq_one.mp (hR₀C hc)) v hv,
    mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hv hq

/-- The same factorization transfers quadraticity to the whole enlargement core. -/
theorem Data.enlargement_module_second_commutator
    (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ⁅⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆,(enlargement T L H).pCoreIn 2⁆ = ⊥ := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let R₀ := (localJoin T L).pCoreIn 2
  have hVQ : ⁅D.fullModule,Q⁆ ≤ D.fullModule := by
    rw [commutator_comm]
    exact (h.core_module_commutator_le s.full_eq_local).trans inf_le_left
  have hR₀C : R₀ ≤ centralizer (D.fullModule : Set G) := by
    rintro _ ⟨q,hq,rfl⟩
    rw [←f.kernel_eq_join_core,f.kernel_eq_action_kernel,joinAction_ker] at hq
    exact hq
  rw [h.enlargement_module_commutator_eq f hi hP hc]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply h.enlargement_core_le_parabolic_core.trans
  rw [h.collapsed_parabolic_core_eq_join f hi hP hc]
  exact sup_le (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (h.core_module_second_commutator f hi hP)))
    (hR₀C.trans (centralizer_le hVQ))

variable {I : Subgroup G}

/-- The original source module lies in the second upper central term of
the actual enlargement core. -/
theorem Data.fullModule_le_enlargement_second_center
    (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    D.fullModule ≤ (Subgroup.upperCentralSeries ((enlargement T L H).pCoreIn 2) 2).map
      ((enlargement T L H).pCoreIn 2).subtype := by
  let R := (enlargement T L H).pCoreIn 2
  have hVR := h.fullModule_le_enlargement_core f hn hs hK hp ho hm hmod hP hc
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp
    (h.enlargement_module_second_commutator f hs.toLocalInput hP hc)
  intro v hv
  apply mem_map_of_mem R.subtype (x := ⟨v,hVR hv⟩)
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro r
  rw [Subgroup.upperCentralSeries_one]
  apply mem_center_iff.mpr
  intro t
  apply Subtype.ext
  exact hcentral (commutator_mem_commutator hv r.property) t t.property

/-- Its nonzero movement is an actual elementary central Frattini subgroup;
centrality of this subgroup does not assert centrality of the full module. -/
theorem Data.enlargement_module_central_frattini
    (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ ≠ ⊥ ∧
      ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ ≤
        omegaCenterIn ((enlargement T L H).pCoreIn 2) ⊓
        (frattini ((enlargement T L H).pCoreIn 2)).map
          ((enlargement T L H).pCoreIn 2).subtype := by
  let R := (enlargement T L H).pCoreIn 2
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hVR := h.fullModule_le_enlargement_core f hn hs hK hp ho hm hmod hP hc
  have hcommV : ⁅D.fullModule,R⁆ ≤ D.fullModule := by
    rw [h.enlargement_module_commutator_eq f hs.toLocalInput hP hc,commutator_comm]
    exact (h.core_module_commutator_le s.full_eq_local).trans inf_le_left
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp
    (h.enlargement_module_second_commutator f hs.toLocalInput hP hc)
  refine ⟨?_,le_inf ?_ ?_⟩
  · intro he
    exact h.collapsed_enlargement_core_moves_fullModule hn hmodel hc
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  · intro d hd
    exact (mem_omegaCenterIn_iff R d).mpr ⟨hVR (hcommV hd),hcentral hd,
      elemPow_eq_one_of_isElementaryAbelian d (hcommV hd)⟩
  · exact h.trivial_image_enlargement_frattini_displacement f hs.toLocalInput hP hc
      (h.moduleFrattiniImage_eq_bot f hn hs hK hp ho hm hmod hP hc)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open BinaryThreeAction BinaryThreeAction.Parabolics Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unchanged original obstruction has its full module in the actual
second center and retains a nontrivial central Frattini movement subgroup. -/
theorem SourceCubicNormalizerEnlargement.exists_second_center_localization
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ _h : Data D H,
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      D.fullModule ≤ (Subgroup.upperCentralSeries ((enlargement T L H).pCoreIn 2) 2).map
        ((enlargement T L H).pCoreIn 2).subtype ∧
      ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ ≠ ⊥ ∧
      ⁅D.fullModule,(enlargement T L H).pCoreIn 2⁆ ≤
        omegaCenterIn ((enlargement T L H).pCoreIn 2) ⊓
        (frattini ((enlargement T L H).pCoreIn 2)).map
          ((enlargement T L H).pCoreIn 2).subtype := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  exact ⟨H,P,h,hs.toLocalInput,
    h.fullModule_le_enlargement_second_center f hn hs hK hp ho hm h24 hP hcollapse,
    h.enlargement_module_central_frattini f hn hmodel hs hK hp ho hm h24 hP hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
