module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityParabolicFactors
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# The higher-dimensional hyperplane residual as a genuine local component

For W=U∩V and F=N_L(W), restriction of the full natural action to W is
surjective. An element fixing W has square fixing V, so its square lies in
O₂(L); consequently the restriction kernel is a two-group. For d>3 the
binary group Aut(W) is simple and perfect. Thus the literal Y=O²(F) still
surjects onto Aut(W), with kernel O₂(Y). The quotient isomorphism retains
conjugation on each representative and gives the natural SL_(d−1)(2) model.

The p-perfect lifting theorem makes Y a genuine C-component in every
normalizing overgroup. Its original Sylow join has nontrivial two-core,
so Y lies in the Chapter 1 local family. Applying the proved 1.2.4 source
theorem inside N_G(C_T(U)) constructs its actual normal containing component.
This supplies the component input used on printed p.805. Identifying that
component with Y, excluding the exceptional overgroups, and finishing the
tensor/dimension argument remain with qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed pp.804--806. The binary simplicity theorem uses
the attributed ATLAS port imported above.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U H P : Subgroup G} {d : ℕ}

abbrev hyperplaneNormalizer (L U V : Subgroup G) :=
  L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)

def hyperplaneAction (L U V : Subgroup G) :
    hyperplaneNormalizer L U V →* MulAut (U ⊓ V : Subgroup G) :=
  (U ⊓ V : Subgroup G).normalizerMonoidHom.comp (inclusion inf_le_right)

omit [Finite G] in
theorem hyperplaneAction_surjective (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) :
    Function.Surjective (hyperplaneAction L U V) := RigidityResidual.hyperplane_full D A

omit [Finite G] in
theorem hyperplaneAction_kernel_isPGroup (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    IsPGroup 2 (hyperplaneAction L U V).ker := by
  let := D.elementary
  let W := U ⊓ V
  intro x
  have hxW : (x.val : G) ∈ centralizer (W : Set G) := by
    intro w hw
    have hh := MulEquiv.congr_fun (MonoidHom.mem_ker.mp x.property) (⟨w,hw⟩ : W)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm
  have hXV : zpowers (x.val : G) ≤ normalizer (V : Set G) :=
    zpowers_le.mpr (D.normalizes x.val.property.1)
  have hXW : zpowers (x.val : G) ≤ normalizer (W : Set G) :=
    zpowers_le.mpr ((Subgroup.centralizer_le_normalizer _) hxW)
  have hd : ⁅zpowers (x.val : G),V⁆ ≤ W := by
    rw [commutator_comm]
    exact commutator_le_of_normalized_index_two V W _ inf_le_right
      (RigidityResidual.hyperplane_index A C) hXV hXW
  have hs : (x.val : G)^2 ∈ centralizer (V : Set G) := by
    intro v hv
    have hw : ⁅(x.val : G),v⁆ ∈ W := hd (commutator_mem_commutator (mem_zpowers _) hv)
    have he : ⁅(x.val : G)^2,v⁆ = 1 := by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,←hxW _ hw,mul_inv_cancel_right]
      simpa only [pow_two] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) ⁅(x.val : G),v⁆ hw.2
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  let l : L := ⟨x.val,x.val.property.1⟩
  have hk : l^2 ∈ pCore 2 L := by
    rw [← A.componentAut_ker D]
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hs v v.property).symm
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)) ⟨l^2,hk⟩
  refine ⟨n+1,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (fun z : pCore 2 L => (z.val : G)) hn
  simpa only [coe_pow,coe_one,pow_add,pow_one,←pow_mul,Nat.mul_comm] using hh

/-- Coordinates retain the original hyperplane, whose order fixes its dimension. -/
def hyperplaneCoordinates [IsElementaryAbelian 2 (U ⊓ V : Subgroup G)] (C : CyclicLocalAnalysis T L V d H P U) :
    Additive (U ⊓ V : Subgroup G) ≃ₗ[ZMod 2] (Fin (d-1) → ZMod 2) := by
  apply LinearEquiv.ofFinrankEq
  rw [Module.finrank_fin_fun]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (U ⊓ V : Subgroup G))
  change Nat.card (U ⊓ V : Subgroup G) = _ at hc
  rw [Nat.card_zmod,C.hyperplane] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm

private theorem perfect_residual_top {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : pResidual 2 X = ⊤ := by
  apply (pResidual_eq_top_iff 2 X).mpr
  intro N hn hp
  let := hn
  by_contra hne
  let : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent

private theorem simple_perfect_core_bot {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] [Group.IsPerfect X] : pCore 2 X = ⊥ := by
  rcases (inferInstance : (pCore 2 X).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hp : IsPGroup 2 X := ((ht ▸ (pCore_isPGroup (p := 2) (G := X)) :
        IsPGroup 2 (⊤ : Subgroup X))).of_equiv topEquiv
    exact (Group.IsPerfect.not_isNilpotent X hp.isNilpotent).elim

private theorem simple_perfect_quasisimple {X : Type*} [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] : IsQuasisimple X := by
  have hc : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp ht)).elim
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).isSimpleGroup }

/-- The automorphism group of the original hyperplane is the actual binary
special linear group in the displayed coordinates. -/
def hyperplaneAutEquiv [IsElementaryAbelian 2 (U ⊓ V : Subgroup G)]
    (C : CyclicLocalAnalysis T L V d H P U) :
    MulAut (U ⊓ V : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin (d-1)) (ZMod 2) :=
  (BinaryFixedLine.linearAutEquiv.trans
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr (hyperplaneCoordinates C))).trans
      (BinaryLinear.OuterCyclic.slEquivLinear (d-1)).symm

theorem hyperplaneAut_simple_perfect (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) :
    IsSimpleGroup (MulAut (U ⊓ V : Subgroup G)) ∧
      Group.IsPerfect (MulAut (U ⊓ V : Subgroup G)) := by
  let := C.elementary
  let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (show U ⊓ V ≤ U from inf_le_left))
      (inclusion_injective _)
  let e := (hyperplaneAutEquiv C).trans (BinaryLinear.OuterCyclic.slEquivLinear (d-1))
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup (d-1)) :=
    BinaryLinear.linearGroup_isPerfect (d-1) (by omega)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (d-1)) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (d-1) (by omega)
  let : IsSimpleGroup (BinaryLinear.OuterCyclic.LinearGroup (d-1)) :=
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d-1)).symm.isSimpleGroup
  exact ⟨e.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

/-- Restriction of the actual two-residual to the original hyperplane. -/
def residualHyperplaneAction (L U V : Subgroup G) :
    rigidityHyperplaneResidual L U V →* MulAut (U ⊓ V : Subgroup G) :=
  (hyperplaneAction L U V).comp (inclusion (map_subtype_le _))

theorem residualHyperplaneAction_surjective (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) : Function.Surjective (residualHyperplaneAction L U V) := by
  let F := hyperplaneNormalizer L U V
  let f := hyperplaneAction L U V
  let := (hyperplaneAut_simple_perfect C hd).2
  have he : (pResidual 2 F).map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f (hyperplaneAction_surjective D A), perfect_residual_top]
  intro a
  obtain ⟨x,hx,hxa⟩ := mem_map.mp (he.symm ▸ (mem_top a))
  exact ⟨⟨x,mem_map_of_mem F.subtype hx⟩,hxa⟩

theorem residualHyperplaneAction_ker (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) :
    (residualHyperplaneAction L U V).ker = pCore 2 (rigidityHyperplaneResidual L U V) := by
  let := (hyperplaneAut_simple_perfect C hd).1
  let := (hyperplaneAut_simple_perfect C hd).2
  have hk : IsPGroup 2 (residualHyperplaneAction L U V).ker :=
    (hyperplaneAction_kernel_isPGroup D A C).comap_of_injective
      (inclusion (map_subtype_le _)) (inclusion_injective _)
  have he := (residualHyperplaneAction L U V).comap_pCore_of_ker_isPGroup
    (residualHyperplaneAction_surjective D A C hd) hk
  simpa only [simple_perfect_core_bot, MonoidHom.comap_bot] using he

/-- The quotient isomorphism is induced by the literal conjugation action. -/
def residualQuotientAutEquiv (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) :
    (rigidityHyperplaneResidual L U V ⧸ pCore 2 (rigidityHyperplaneResidual L U V)) ≃*
      MulAut (U ⊓ V : Subgroup G) :=
  (QuotientGroup.quotientMulEquivOfEq (residualHyperplaneAction_ker D A C hd).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residualHyperplaneAction_surjective D A C hd))

theorem residualQuotientAutEquiv_apply (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) (y : rigidityHyperplaneResidual L U V) (w : (U ⊓ V : Subgroup G)) :
    (residualQuotientAutEquiv D A C hd (QuotientGroup.mk' _ y) w : G) =
      (y : G) * (w : G) * (y : G)⁻¹ := rfl

/-- The literal residual is a genuine C-component in any normalizing overgroup. -/
theorem residual_isCComponent_in (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K : Subgroup G} (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hKY : K ≤ normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    ((rigidityHyperplaneResidual L U V).subgroupOf K).IsCComponent := by
  let Y := rigidityHyperplaneResidual L U V
  let F := hyperplaneNormalizer L U V
  let e := residualQuotientAutEquiv D A C hd
  let := (hyperplaneAut_simple_perfect C hd).1
  let := (hyperplaneAut_simple_perfect C hd).2
  let : IsQuasisimple (MulAut (U ⊓ V : Subgroup G)) := simple_perfect_quasisimple
  let : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv e.symm
  have hc : (⊤ : Subgroup Y).IsCComponent :=
    isCComponent_top_of_isPPerfect_of_quasisimple_quotient (pCore 2 Y) pCore_isPGroup
      (isPPerfect_embedded_pResidual 2 F)
  let j := (subgroupOfEquivOfLe hYK).symm
  have htop : (⊤ : Subgroup (Y.subgroupOf K)).IsCComponent := by
    have hh := hc.map_equiv j
    rw [map_top_of_surjective j.toMonoidHom j.surjective] at hh
    exact hh
  have hn : (Y.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKY
  simpa only [← MonoidHom.range_eq_map,range_subtype] using htop.map_subtype hn.isSubnormal

/-- The hyperplane quotient acts as its natural module, with the original
conjugation formula on every representative. -/
theorem residual_natural_model (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) :
    Chapter6.Source.IsConjugationModel (rigidityHyperplaneResidual L U V) (U ⊓ V)
      (Representation.specialLinearNatural (k := ZMod 2) (d-1)) := by
  let := C.elementary
  let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (show U ⊓ V ≤ U from inf_le_left))
      (inclusion_injective _)
  let c := hyperplaneCoordinates C
  let f := c.toAddEquiv.toMultiplicativeRight
  let e := (residualQuotientAutEquiv D A C hd).trans (hyperplaneAutEquiv C)
  refine ⟨e,f,?_⟩
  intro y w
  let a := residualQuotientAutEquiv D A C hd (QuotientGroup.mk' _ y)
  have hm : Representation.specialLinearNatural (d-1) (hyperplaneAutEquiv C a)
      (Multiplicative.toAdd (f w)) = Multiplicative.toAdd (f (a w)) := by
    change (BinaryLinear.OuterCyclic.slEquivLinear (d-1) (hyperplaneAutEquiv C a))
      (c (Additive.ofMul w)) = c (Additive.ofMul (a w))
    simp only [hyperplaneAutEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply]
    change c ((BinaryFixedLine.linearAutEquiv a) (c.symm (c (Additive.ofMul w)))) = _
    rw [c.symm_apply_apply]
    rfl
  change (f.symm (Multiplicative.ofAdd
    (Representation.specialLinearNatural (d-1) (hyperplaneAutEquiv C a)
      (Multiplicative.toAdd (f w)))) : G) = _
  rw [hm]
  change (f.symm (f (a w)) : G) = _
  rw [f.symm_apply_apply]
  exact residualQuotientAutEquiv_apply D A C hd y w

omit [Finite G] in
/-- The original Sylow subgroup normalizes the literal hyperplane residual. -/
theorem sylow_normalizes_residual (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V d H P U)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) := by
  have hTW : (T : Subgroup G) ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTF : (T : Subgroup G) ≤ normalizer (hyperplaneNormalizer L U V : Set G) :=
    (le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hTF.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- The original residual belongs to the genuine Sylow local-component family. -/
theorem residual_mem_local_family (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    rigidityHyperplaneResidual L U V ∈ Chapter1.L G (T : Subgroup G) := by
  let Y := rigidityHyperplaneResidual L U V
  let J := Y ⊔ (T : Subgroup G)
  let W := U ⊓ V
  have hJW : J ≤ normalizer (W : Set G) := sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf)
  have hWJ : W ≤ J := (inf_le_right.trans D.le_sylow).trans le_sup_right
  have hWcore : W ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le (inf_le_right.trans D.le_sylow)) hWJ hJW
  have hWne : W ≠ ⊥ := by
    intro he
    have hc := C.hyperplane
    change Nat.card W = _ at hc
    rw [he,card_bot] at hc
    have hp : 1 < 2 ^ (d-1) := one_lt_pow₀ (by decide) (by omega)
    omega
  have hYn : J ≤ normalizer (Y : Set G) :=
    sup_le Y.le_normalizer (sylow_normalizes_residual D C hTV)
  refine ⟨?_, ⟨T.subtype le_sup_right, by
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩,
    ne_bot_of_le_ne_bot hWne hWcore⟩
  exact residual_isCComponent_in D A C hd le_sup_left hYn

/-- The actual containing C-component in N_G(C_T(U)), normal in that
normalizer. Equality with Y is the remaining component-sieve obligation. -/
theorem exists_normal_containing_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    ∃ K : Subgroup G,
      K ≤ normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
      (K.subgroupOf (normalizer
        (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V ≤ K ∧
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
        normalizer (K : Set G) ∧ K ∈ Chapter1.L G (T : Subgroup G) := by
  let Y := rigidityHyperplaneResidual L U V
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let N := normalizer (R : Set G)
  have hTN : (T : Subgroup G) ≤ N :=
    (le_inf (T : Subgroup G).le_normalizer
      (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hRN : R ≤ N := R.le_normalizer
  have hRne : R ≠ ⊥ := ne_bot_of_le_ne_bot
    (C.core_ne_bot (by omega : 2 ≤ d)) (le_inf C.core_le_sylow (by
      let := C.elementary
      exact le_centralizer U))
  have hNH : N ∈ Chapter1.H G := ne_bot_of_le_ne_bot hRne
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left) hRN le_rfl)
  have hTV := ((structural G T L h).2.2 V D).1
  have hYL := residual_mem_local_family D A C hd hTV
  have hYN : Y ≤ N := B.residual_normalizes
  let S := T.subtype hTN
  have hlocal : Y.subgroupOf N ∈ Chapter1.L N (S : Subgroup N) := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (Chapter1.mem_LIn_iff_subgroupOf hTN hYN).mp ⟨hYN,hYL⟩
  have hSY : (S : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hYN]
    exact comap_mono (sylow_normalizes_residual D C hTV)
  obtain ⟨K,⟨hK,hYK,hn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hNH) S hlocal hSY
  let K' := K.map N.subtype
  have hKN : K' ≤ N := map_subtype_le _
  have he : K'.subgroupOf N = K := comap_map_eq_self_of_injective N.subtype_injective _
  have hcmp : (K'.subgroupOf N).IsCComponent := he.symm ▸ hK
  have hnorm : N ≤ normalizer (K' : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKN).mp (he.symm ▸ hn)
  refine ⟨K',hKN,hcmp,?_,hnorm,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hYN] using map_mono (f := N.subtype) hYK
  · exact Chapter1.mem_L_of_cComponent hNH
      ⟨S,by simp only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN]⟩ hKN hcmp

/-- Source application: the common centralizers are discharged internally,
and the actual hyperplane action and containing component are both supplied. -/
theorem source_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    Chapter6.Source.IsConjugationModel (rigidityHyperplaneResidual L U V) (U ⊓ V)
        (Representation.specialLinearNatural (k := ZMod 2) (d-1)) ∧
      rigidityHyperplaneResidual L U V ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ K : Subgroup G,
        K ≤ normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
        (K.subgroupOf (normalizer
          (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G))).IsCComponent ∧
        rigidityHyperplaneResidual L U V ≤ K ∧
        normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
          normalizer (K : Set G) ∧ K ∈ Chapter1.L G (T : Subgroup G) :=
  ⟨residual_natural_model D A C hd,
    residual_mem_local_family D A C hd (((structural G T L h).2.2 V D).1),
    exists_normal_containing_component h D structural A C
      (RigidityKernel.source_centralizers h D structural A C hnone) hd⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
