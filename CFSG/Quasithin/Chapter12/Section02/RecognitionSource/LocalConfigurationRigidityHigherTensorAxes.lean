module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherComponentsFaithful
public import Theory.Representation.BinaryDoubledNaturalCentralizer

/-!
# The original conjugate axes as two identical natural modules

For W=U∩V, the pair construction gives U=W Wᵍ with equal axis orders.
Multiplication therefore defines an actual product isomorphism. If P
normalizes the hyperplane residual Y, the proved commutator bound [I,Y]≤U
makes their actions on U commute. The product coordinates then intertwine
Y with the same full natural action on both copies of W. The induced
surjective matrix homomorphism and linear coordinates are retained.

The same calculation identifies O₂(Y) with U when C_G(U)=U. These are
conditional action statements; qt-d-12213-local-rigidity still owns the
component argument establishing the normality premise. The cubic-actor
and dimension consumers are in LocalConfigurationRigidityHigherTensor.

Source: Aschbacher--Smith, original 12.2.25, printed pp.805--806.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

omit [Finite G] in
theorem pair_action_commutes (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hYU : rigidityHyperplaneResidual L U V ≤ normalizer (U : Set G))
    (hPY : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G))
    (p : P) (y : rigidityHyperplaneResidual L U V) :
    Commute (U.normalizerMonoidHom ⟨p,C.overgroup_normalizes_core
      ((show P ≤ H by rw [C.overgroup]; exact le_sup_left) p.property)⟩)
      (U.normalizerMonoidHom ⟨y,hYU y.property⟩) := by
  let := C.elementary
  let p' : normalizer (U : Set G) := ⟨p,C.overgroup_normalizes_core
    ((show P ≤ H by rw [C.overgroup]; exact le_sup_left) p.property)⟩
  let y' : normalizer (U : Set G) := ⟨y,hYU y.property⟩
  have hc : ⁅p',y'⁆ ∈ U.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    apply le_centralizer U
    exact RigidityParabolic.residual_pair_commutator D A C hPY
      (commutator_mem_commutator (mem_sup_left (mem_sup_left p.property)) y.property)
  have he := MonoidHom.mem_ker.mp hc
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at he
  exact he

theorem exists_pair_coordinates (C : CyclicLocalAnalysis T L V d H P U) :
    ∃ (g : P) (e : ((U ⊓ V : Subgroup G) × (U ⊓ V : Subgroup G)) ≃* U),
      g ≠ 1 ∧ ∀ w, (e w : G) = (w.1 : G) * (g : G) * (w.2 : G) * (g : G)⁻¹ := by
  let := C.elementary
  obtain ⟨g,hg,hg1,hI,hU⟩ := C.pair
  have hgN : g ∈ normalizer (U : Set G) := C.overgroup_normalizes_core
    ((show P ≤ H by rw [C.overgroup]; exact le_sup_left) hg)
  let W := U ⊓ V
  let j : W →* U := inclusion inf_le_left
  let a := U.normalizerMonoidHom ⟨g,hgN⟩
  let f := j.coprod (a.toMonoidHom.comp j)
  have hf : Function.Surjective f := by
    intro u
    have hn : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G) :=
      ((le_sup_right.trans hU.symm.le).trans
        ((le_centralizer U).trans (centralizer_le inf_le_left))).trans
          (Subgroup.centralizer_le_normalizer _)
    have hu : (u : G) ∈ (W : Set G) * (W.map (MulAut.conj g).toMonoidHom : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left W _ hn,hU.symm]
      exact u.property
    obtain ⟨w,hw,z,⟨v,hv,rfl⟩,he⟩ := hu
    refine ⟨(⟨w,hw⟩,⟨v,hv⟩),Subtype.ext ?_⟩
    exact he
  have hc : Nat.card (W × W) = Nat.card U := by
    rw [Nat.card_prod,C.hyperplane,C.dimension,←pow_add,two_mul]
  exact ⟨⟨g,hg⟩,MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩),
    fun he => hg1 (congrArg Subtype.val he),fun w => by
      change (w.1 : G) * (g * (w.2 : G) * g⁻¹) = _
      group⟩

theorem core_le_residual_of_pair_normalizes (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d)
    (hPY : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    U ≤ rigidityHyperplaneResidual L U V := by
  obtain ⟨g,hg,hg1,hI,hU⟩ := C.pair
  have hW := (hyperplane_le_residual_core D A C hd).trans (pCoreIn_le 2 _)
  apply hU.le.trans
  exact sup_le hW (by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hW
    have he : (rigidityHyperplaneResidual L U V).map (MulAut.conj g).toMonoidHom =
        rigidityHyperplaneResidual L U V := mem_normalizer_iff_map_conj_eq.mp (hPY hg)
    rwa [he] at hh)

theorem exists_equivariant_pair_coordinates (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hYU : rigidityHyperplaneResidual L U V ≤ normalizer (U : Set G))
    (hPY : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    ∃ e : ((U ⊓ V : Subgroup G) × (U ⊓ V : Subgroup G)) ≃* U,
      ∀ (y : rigidityHyperplaneResidual L U V) w,
        U.normalizerMonoidHom ⟨y,hYU y.property⟩ (e w) =
          e (residualHyperplaneAction L U V y w.1, residualHyperplaneAction L U V y w.2) := by
  obtain ⟨g,e,hg,he⟩ := exists_pair_coordinates C
  refine ⟨e,fun y w => ?_⟩
  let a := U.normalizerMonoidHom ⟨y,hYU y.property⟩
  let b := U.normalizerMonoidHom ⟨g,C.overgroup_normalizes_core
    ((show P ≤ H by rw [C.overgroup]; exact le_sup_left) g.property)⟩
  let j : (U ⊓ V : Subgroup G) →* U := inclusion inf_le_left
  have hform (w) : e w = j w.1 * b (j w.2) := by
    apply Subtype.ext
    change (e w : G) = (w.1 : G) * ((g : G) * (w.2 : G) * (g : G)⁻¹)
    simpa only [mul_assoc] using he w
  have hact (w) : a (j w) = j (residualHyperplaneAction L U V y w) := rfl
  rw [hform,map_mul]
  have hc : a (b (j w.2)) = b (a (j w.2)) :=
    MulEquiv.congr_fun (pair_action_commutes D A C hYU hPY g y).eq.symm _
  rw [hc,hact,hact, hform]


/-- The same natural matrix acts on both original conjugate axes. -/
theorem exists_natural_double (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d)
    (hYU : rigidityHyperplaneResidual L U V ≤ normalizer (U : Set G))
    (hPY : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    letI := C.elementary
    ∃ q : rigidityHyperplaneResidual L U V →*
        Matrix.SpecialLinearGroup (Fin (d-1)) (ZMod 2),
      Function.Surjective q ∧
      ∃ e : Additive U ≃ₗ[ZMod 2] Representation.BinaryDoubledNatural.Space (d-1),
        ∀ (y : rigidityHyperplaneResidual L U V) (u : U),
          e (Additive.ofMul (U.normalizerMonoidHom ⟨y,hYU y.property⟩ u)) =
            Representation.BinaryDoubledNatural.representation (d-1) (q y)
              (e (Additive.ofMul u)) := by
  let := C.elementary
  let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (show U ⊓ V ≤ U from inf_le_left))
      (inclusion_injective _)
  obtain ⟨f,hf⟩ := exists_equivariant_pair_coordinates D A C hYU hPY
  let c := hyperplaneCoordinates C
  let a := f.symm.toAdditive.trans (AddEquiv.prodAdditive _ _)
  let b : Additive U ≃ₗ[ZMod 2]
      (Additive (U ⊓ V : Subgroup G) × Additive (U ⊓ V : Subgroup G)) :=
    { a with map_smul' := ZMod.map_smul a }
  let e := (b.trans (c.prodCongr c)).trans (LinearEquiv.finTwoArrow
    (ZMod 2) (Fin (d-1) → ZMod 2)).symm
  let q := (hyperplaneAutEquiv C).toMonoidHom.comp (residualHyperplaneAction L U V)
  refine ⟨q,(hyperplaneAutEquiv C).surjective.comp
    (residualHyperplaneAction_surjective D A C hd),e,?_⟩
  intro y u
  obtain ⟨w,rfl⟩ := f.surjective u
  rw [hf]
  have hm (w) : c (Additive.ofMul (residualHyperplaneAction L U V y w)) =
      Representation.specialLinearNatural (d-1) (q y) (c (Additive.ofMul w)) := by
    change _ = (BinaryLinear.OuterCyclic.slEquivLinear (d-1)
      (hyperplaneAutEquiv C (residualHyperplaneAction L U V y))) _
    simp only [hyperplaneAutEquiv,MulEquiv.trans_apply,MulEquiv.apply_symm_apply,
      BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply]
    rw [c.symm_apply_apply]
    rfl
  have he (w) : e (Additive.ofMul (f w)) =
      ![c (Additive.ofMul w.1),c (Additive.ofMul w.2)] := by
    change ![c (Additive.ofMul (f.symm (f w)).1),
      c (Additive.ofMul (f.symm (f w)).2)] = _
    rw [f.symm_apply_apply]
  rw [he,he]
  funext i
  fin_cases i <;> exact hm _


/-- The pair core is the literal two-core of the residual once the pair
normalizes it and its ambient centralizer is itself. -/
theorem residual_core_eq_of_pair_normalizes (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d)
    (hYU : rigidityHyperplaneResidual L U V ≤ normalizer (U : Set G))
    (hPY : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G))
    (hCU : centralizer (U : Set G) = U) :
    (rigidityHyperplaneResidual L U V).pCoreIn 2 = U := by
  let := C.elementary
  have hUY := core_le_residual_of_pair_normalizes D A C hd hPY
  apply le_antisymm ?_
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) hUY hYU)
  rintro x ⟨y,hy,rfl⟩
  have hk := (residualHyperplaneAction_ker D A C hd).symm.le hy
  have he := MonoidHom.mem_ker.mp hk
  obtain ⟨e,hact⟩ := exists_equivariant_pair_coordinates D A C hYU hPY
  have hf : U.normalizerMonoidHom ⟨y,hYU y.property⟩ = 1 := by
    ext u
    obtain ⟨w,rfl⟩ := e.surjective u
    rw [hact,he]
    rfl
  have hc : (y : G) ∈ centralizer (U : Set G) := by
    have hk' : (⟨y,hYU y.property⟩ : normalizer (U : Set G)) ∈
        U.normalizerMonoidHom.ker := hf
    rwa [normalizerMonoidHom_ker] at hk'
  exact hCU.le hc

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
