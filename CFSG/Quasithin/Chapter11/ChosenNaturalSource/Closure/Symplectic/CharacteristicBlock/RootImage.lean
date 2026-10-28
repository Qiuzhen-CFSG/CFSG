module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSPair
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Sylow and characteristic-two inputs in the root-image branch

Suppose the original Q₁ = O₂(G₁) has just the marked long-root image.
The nonbinary root torus shows that [Q₁,L₁X] has that same image and lies
in Q₁ ∩ L. Since O₂(L) ≤ Q₁, the whole original root preimage lies in Q₁.
It follows that the kernel of the original V-action on LQ₁ lies in Q₁.

The marked opposite pair has the literal first-plane SL₂ image. Its root
is a Sylow two-subgroup by the native upper-unipotent theorem. Transporting
relative indices through the original action, with the kernel contained in
Q₁, proves that Q₁ itself is Sylow in IQ₁. The normal chosen V and the
two-group action kernel give F*(IQ₁)=O₂(IQ₁); the two-local hypothesis gives
SQTK. The actual opposite-pair generation excludes every nontrivial
characteristic subgroup of Q₁ normalized by I.

The source application discharges all these inputs from the preceding
radical and opposite-core proofs. Excluding the resulting root-image case
still belongs to qt-d-1222-natural-closure-sp4.

Source: Aschbacher--Smith 11.5.7, printed p.783; C.1.29, printed p.134.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

private theorem root_parabolic_commutator {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) :
    ⁅RootSubgroup.group (F := F) 0,pointParabolic (F := F)⁆ = RootSubgroup.group (F := F) 0 := by
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp RootNormalizerResidual.normalizer_zero_eq.ge
  · calc
      RootSubgroup.group (F := F) 0 = ⁅RootSubgroup.group 0,RootTori.torus 0⁆ :=
        (RootTori.commutator_eq 0 hF).symm
      _ ≤ ⁅RootSubgroup.group 0,pointParabolic⁆ := commutator_mono le_rfl
        ((RootTori.torus_le_normalizer 0).trans_eq RootNormalizerResidual.normalizer_zero_eq)

/-- The original local-Cartan image moves its entire central long root. -/
theorem root_image_commutator (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom) (hXL : E.X ≤ L) :
    ⁅(center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype,
      actionImage (V := V) (E.L₁ ⊔ E.X)⁆ =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  have hF : 2 < Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    have hh := Nat.pow_lt_pow_right (a := 2) (by decide) E.input.nonbinary
    simpa using hh
  rw [FullAction.center_eq_marked_root m g (PointModel.local_identification m g hpoint),
    ← FullAction.image_eq m _ (sup_le E.L₁_le hXL), hcartan,
    ← map_commutator, ← map_commutator, root_parabolic_commutator hF]

/-- In the root-image case, the Cartan commutator supplies that image inside Q₁ ∩ L. -/
theorem core_cartan_commutator_of_root_image (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom) (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    ⁅E.G₁.pCoreIn 2,E.L₁ ⊔ E.X⁆ ≤ E.G₁.pCoreIn 2 ⊓ L ∧
      actionImage (V := V) ⁅E.G₁.pCoreIn 2,E.L₁ ⊔ E.X⁆ =
        actionImage (V := V) (E.G₁.pCoreIn 2) := by
  refine ⟨le_inf ?_ ?_,?_⟩
  · exact le_normalizer_iff_commutator_le_left.mp
      ((sup_le E.L₁_le_G₁ hXG).trans (point_normalizer_normalizes_core E))
  · exact (commutator_mono le_rfl (sup_le E.L₁_le hXL)).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((core_le_sylow E m).trans D.sylow_normalizes_component))
  · rw [Terminal.actionImage_commutator V _ _
      ((core_le_sylow E m).trans E.input.sylow_normalizes)
      ((sup_le E.L₁_le hXL).trans D.normalizes), hroot,
      root_image_commutator E m g hpoint hcartan hXL]

/-- The genuine O₂(L) bound lifts the root-image commutator to the full original root preimage. -/
theorem root_preimage_le_core (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom) (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    FullAction.rootPreimage (E := E) ≤ E.G₁.pCoreIn 2 := by
  obtain ⟨hC,heC⟩ := core_cartan_commutator_of_root_image E m g hpoint hcartan hXL hXG hroot
  let C := ⁅E.G₁.pCoreIn 2,E.L₁ ⊔ E.X⁆
  rintro x ⟨l,hl,rfl⟩
  have hm : FullAction.componentHom (D := D) l ∈ actionImage (V := V) C := by
    rw [heC,hroot]
    exact hl
  obtain ⟨c,hc,he⟩ := hm
  let cL : L := ⟨c.val,(hC hc).2⟩
  have he' : FullAction.componentHom (D := D) cL = FullAction.componentHom (D := D) l := he
  have hk : l*cL⁻¹ ∈ (FullAction.componentHom (D := D)).ker := by
    change FullAction.componentHom (D := D) (l*cL⁻¹) = 1
    rw [map_mul,map_inv,he',mul_inv_cancel]
  rw [FullAction.componentHom_ker E] at hk
  have hq : l.val*c.val⁻¹ ∈ E.G₁.pCoreIn 2 := hcore (mem_map_of_mem L.subtype hk)
  have hh := (E.G₁.pCoreIn 2).mul_mem hq ((hC hc).1)
  change l.val*c.val⁻¹*c.val ∈ E.G₁.pCoreIn 2 at hh
  change l.val ∈ E.G₁.pCoreIn 2
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh


/-- The original V-action on LQ₁ has its entire kernel in Q₁. -/
theorem core_join_action_kernel_of_root_image (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom) (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2 := by
  have hQN := (core_le_sylow E m).trans E.input.sylow_normalizes
  rintro x ⟨hxC,hxJ⟩
  change x ∈ (↑(L ⊔ E.G₁.pCoreIn 2) : Set G) at hxJ
  rw [coe_mul_of_right_le_normalizer_left L _
    ((core_le_sylow E m).trans D.sylow_normalizes_component)] at hxJ
  obtain ⟨l,hl,q,hq,rfl⟩ := hxJ
  let lL : L := ⟨l,hl⟩
  let qN : normalizer (V : Set G) := ⟨q,hQN hq⟩
  have he : FullAction.componentHom (D := D) lL =
      (V.normalizerMonoidHom qN)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    change V.normalizerMonoidHom ⟨l,D.normalizes hl⟩ * V.normalizerMonoidHom qN = 1
    rw [←map_mul, ←MonoidHom.mem_ker, normalizerMonoidHom_ker]
    exact hxC
  have hqimage : V.normalizerMonoidHom qN ∈
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
    rw [←hroot]
    exact mem_map_of_mem _ (show qN ∈ (E.G₁.pCoreIn 2).subgroupOf _ from hq)
  have hlroot : l ∈ FullAction.rootPreimage (E := E) := by
    refine ⟨lL,?_,rfl⟩
    change FullAction.componentHom (D := D) lL ∈
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype
    rw [he]
    exact inv_mem hqimage
  exact (E.G₁.pCoreIn 2).mul_mem
    (root_preimage_le_core E m g hpoint hcartan hXL hXG hcore hroot hlroot) hq

private theorem root_pair_odd_index {F : Type*} [Field F] [Finite F] [CharP F 2] :
    Odd ((RootSubgroup.group (F := F) 0).relIndex OppositeLongRootPair.pair) := by
  open Matrix.SpecialLinearGroup in
  have hmap : (upperUnipotent F).map OppositeLongRootPair.embedding =
      RootSubgroup.group (F := F) 0 := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
      rw [OppositeLongRootPair.embedding_upper]
      exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩
    · intro x hx
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hx
      exact ⟨transvection zero_ne_one t,(mem_upperUnipotent F _).mpr ⟨t,rfl⟩,
        OppositeLongRootPair.embedding_upper t⟩
  have hi := relIndex_map_map_of_injective (Matrix.SpecialLinearGroup.upperUnipotent F) ⊤
    (OppositeLongRootPair.embedding_injective (F := F))
  rw [hmap,←MonoidHom.range_eq_map,OppositeLongRootPair.embedding_range,relIndex_top_right] at hi
  rw [hi]
  exact Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2).not_dvd_index)


/-- Both actual opposite generators lie in LQ₁. -/
theorem opposite_join_le_core_join (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L) :
    oppositeJoin (auxiliaryW E) y ≤ L ⊔ E.G₁.pCoreIn 2 := by
  have hWJ : auxiliaryW E ≤ L ⊔ E.G₁.pCoreIn 2 :=
    ((auxiliaryW_le_W E).trans hW).trans le_sup_right
  apply sup_le hWJ
  exact (map_mono hWJ).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp
      ((L ⊔ E.G₁.pCoreIn 2).le_normalizer (mem_sup_left hy)))

/-- The native SL₂ root index lifts to Sylow Q₁ in the actual marked IQ₁. -/
theorem root_case_sylow_of_kernel (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2) :
    ∃ S : Sylow 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G),
      (S : Subgroup _).map (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2).subtype =
        E.G₁.pCoreIn 2 := by
  let I := oppositeJoin (auxiliaryW E) y
  let Q := E.G₁.pCoreIn 2
  let J := I ⊔ Q
  have hJL : J ≤ L ⊔ Q := sup_le (opposite_join_le_core_join E hW hy) le_sup_right
  have hQN : Q ≤ normalizer (V : Set G) := (core_le_sylow E m).trans E.input.sylow_normalizes
  have hJN : J ≤ normalizer (V : Set G) := hJL.trans (sup_le D.normalizes hQN)
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion hJN)
  let QJ := Q.subgroupOf J
  have hmap (A : Subgroup G) (hAJ : A ≤ J) :
      (A.subgroupOf J).map f = actionImage (V := V) A := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a.val,hJN a.property⟩,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a.val,hAJ ha⟩,ha,rfl⟩
  have hk : f.ker ≤ QJ := by
    intro x hx
    apply hkernel
    refine ⟨?_,hJL x.property⟩
    change V.normalizerMonoidHom (inclusion hJN x) = 1 at hx
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker] at hx
    exact hx
  have hJimage : actionImage (V := V) J =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m) := by
    change ((I ⊔ Q).subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom = _
    rw [subgroupOf_sup (le_sup_left.trans hJN) hQN,Subgroup.map_sup]
    change actionImage (V := V) I ⊔ actionImage (V := V) Q = _
    rw [hpair,hroot,FullAction.center_eq_marked_root m g hlocal]
    exact sup_eq_left.mpr (map_mono (map_mono
      (show RootSubgroup.group 0 ≤ OppositeLongRootPair.pair from le_sup_left)))
  have hi := relIndex_map_map f QJ ⊤
  have htop : (⊤ : Subgroup J).map f = actionImage (V := V) J := by
    simpa only [subgroupOf_self] using hmap J le_rfl
  rw [hmap Q le_sup_right,htop,sup_eq_left.mpr hk,top_sup_eq,relIndex_top_right,
    hJimage,hroot,FullAction.center_eq_marked_root m g hlocal,
    relIndex_map_map_of_injective _ _ (FullAction.modelHom_injective m),
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  have hodd : Odd QJ.index := hi ▸ root_pair_odd_index
  have hp : IsPGroup 2 QJ := (isPGroup_pCoreIn 2 E.G₁).comap_subtype
  refine ⟨hp.toSylow (by simpa only [←even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hodd)),?_⟩
  rw [IsPGroup.toSylow_coe]
  exact map_subgroupOf_eq_of_le le_sup_right


private theorem subgroup_sqtk (m : MarkedFlag E) (J : Subgroup G)
    (hJL : J ≤ L ⊔ E.G₁.pCoreIn 2) : IsSQTK KnownSimple.IsKnownSimple J := by
  have hq := (core_join_sqtk E m).subgroup (J.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
  exact ⟨hq.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hJL).symm.toMonoidHom (subgroupOfEquivOfLe hJL).symm.injective,
    hq.isKGroup.of_injective (subgroupOfEquivOfLe hJL).symm.toMonoidHom
      (subgroupOfEquivOfLe hJL).symm.injective⟩

private theorem subgroup_characteristicTwo_of_kernel (m : MarkedFlag E) (J : Subgroup G)
    (hVJ : V ≤ J) (hJL : J ≤ L ⊔ E.G₁.pCoreIn 2)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2) :
    generalizedFitting J = pCore 2 J := by
  have hJN : J ≤ normalizer (V : Set G) := hJL.trans
    (sup_le D.normalizes ((core_le_sylow E m).trans E.input.sylow_normalizes))
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion hJN)
  have hk : f.ker ≤ (E.G₁.pCoreIn 2).subgroupOf J := by
    intro x hx
    apply hkernel
    refine ⟨?_,hJL x.property⟩
    change V.normalizerMonoidHom (inclusion hJN x) = 1 at hx
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker] at hx
    exact hx
  have hkp : IsPGroup 2 f.ker := (isPGroup_pCoreIn 2 E.G₁).comap_subtype.to_le hk
  have hkcore : f.ker ≤ pCore 2 J := le_sSup ⟨inferInstance,hkp⟩
  let := D.elementary
  have hvn : (V.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJN
  have hvcore : V.subgroupOf J ≤ pCore 2 J :=
    le_sSup ⟨hvn,(IsElementaryAbelian.isPGroup 2 V).comap_subtype⟩
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro x hx
  apply hkcore
  change V.normalizerMonoidHom (inclusion hJN x) = 1
  rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
  intro v hv
  exact congrArg Subtype.val (hx (⟨v,hVJ hv⟩ : J) (hvcore hv))

/-- The preceding source inputs construct the actual C.1.29 overgroup and Sylow, with characteristic-subgroup exclusion. -/
theorem root_case_inputs_of_preceding (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hne : ¬ IsMulCommutative E.W)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) :
    ∃ (g' : Sp E.input.field.Carrier) (y : L),
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y : G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g').toMonoidHom).map (FullAction.modelHom m) ∧
      ∃ S : Sylow 2 (oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2 : Subgroup G),
        (S : Subgroup _).map (oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2).subtype =
          E.G₁.pCoreIn 2 ∧
        IsSQTK KnownSimple.IsKnownSimple
          (oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2 : Subgroup G) ∧
        generalizedFitting (oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2 : Subgroup G) =
          pCore 2 (oppositeJoin (auxiliaryW E) (y : G) ⊔ E.G₁.pCoreIn 2 : Subgroup G) ∧
        ∀ C : Subgroup (E.G₁.pCoreIn 2), C.Characteristic → C ≠ ⊥ →
          ¬ oppositeJoin (auxiliaryW E) (y : G) ≤
            normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G) := by
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  obtain ⟨hV,hW,hU,hrootW,hmove,_,hPhi,_⟩ :=
    RadicalAction.initial_branch_of_preceding E m g hpoint hthree hcartan hXL hXG
      hn3 hirr hti hgen hVX hfour hfive hne
  have hcore := NaturalQuotient.core_le_point_core E m hX hV hW hrootW hmove hPhi
    hfour hfive hti (CoverGeometry.radical_commutator m g hpoint hthree) hgen
  have hkernel := core_join_action_kernel_of_root_image E m g hpoint hcartan hXL hXG hcore hroot
  obtain ⟨g',y,_,hlocal,_,hpair,_⟩ :=
    OppositeGeometry.exists_opposite_pair_geometry E m hW hrootW hPhi
  obtain ⟨S,hS⟩ := root_case_sylow_of_kernel E m hW y.property g' hlocal hpair hroot hkernel
  have hJL := sup_le (opposite_join_le_core_join E hW y.property) le_sup_right
  refine ⟨g',y,hpair,S,hS,subgroup_sqtk E m _ hJL,
    subgroup_characteristicTwo_of_kernel E m _ (hV.trans le_sup_right) hJL hkernel,?_⟩
  intro C hC hCne
  let := hC
  exact characteristic_not_normalized_by_marked_pair E m hout hW y.property g' hlocal hpair C hCne


/-- The root-case structure for a specified opposite pair, allowing the
Cartan-compatible choice to be retained in the residual argument. -/
theorem root_case_structure_of_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2) :
    ∃ S : Sylow 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G),
      (S : Subgroup _).map (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2).subtype =
        E.G₁.pCoreIn 2 ∧
      IsSQTK KnownSimple.IsKnownSimple
        (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G) ∧
      generalizedFitting (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G) =
        pCore 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G) ∧
      ∀ C : Subgroup (E.G₁.pCoreIn 2), C.Characteristic → C ≠ ⊥ →
        ¬ oppositeJoin (auxiliaryW E) y ≤ normalizer (C.map (E.G₁.pCoreIn 2).subtype : Set G) := by
  obtain ⟨S,hS⟩ := root_case_sylow_of_kernel E m hW hy g hlocal hpair hroot hkernel
  have hJL := sup_le (opposite_join_le_core_join E hW hy) le_sup_right
  refine ⟨S,hS,subgroup_sqtk E m _ hJL,
    subgroup_characteristicTwo_of_kernel E m _ (hV.trans le_sup_right) hJL hkernel,?_⟩
  intro C hC hCne
  let := hC
  exact characteristic_not_normalized_by_marked_pair E m hout hW hy g hlocal hpair C hCne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
