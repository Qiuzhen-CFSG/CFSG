module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCorePlacement
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.LinearThreeInvolutoryLift
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupAction.MaximalCosetOrbit

/-!
# Core displacements and the final orbit contradiction in 12.2.23

The coprime pair splitting gives |C_W(V)|=16. The natural-action kernel
identifies this with W∩O₂(LT), and W≤L identifies W∩O₂(L), also of order
sixteen. Normality of Φ(P)W and the fixed-point-free Frattini action give
the exact displacements on both cores. An involution of W outside O₂(L)
excludes the central SL₂(7) cover, proving [O₂(LT),L]=O₂(L).

Finally a fixed q in O₂(H) whose T-orbit together with V generates O₂(L)
would force [O₂(L),Φ(P)]≤V. Its order sixteen contradicts |V|=8.
The source construction of this q from the component module remains with
qt-d-12213-cyclic-block; no existence of that generator is asserted here.
LocalConfigurationCyclicExclusionCoreOrbitAssembly supplies these proved
calculations to the original cyclic-block consumer.
Source: Aschbacher–Smith, 12.2.23, printed p.804, and B.4.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

/-- The rotation-fixed complement centralizes the whole original pair. -/
theorem module_rotation_fixed_centralizes_chosen
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d) :
    W ⊓ centralizer (zpowers g : Set G) ≤ centralizer (V : Set G) := by
  let := S.elementary
  let C := W ⊓ centralizer (zpowers g : Set G)
  have hvW : v ∈ normalizer (W : Set G) :=
    S.normalizes (S.hstar.1.1.2 (D.le_sylow S.inverter_mem))
  have hvg : v ∈ normalizer (zpowers g : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (v * g * v⁻¹) = zpowers g
    rw [S.inverts_generator, zpowers_inv]
  have hvC : v ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hvW, normalizer_le_normalizer_centralizer _ hvg⟩
  have hcommC : ⁅C, zpowers v⁆ ≤ C :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hvC)
  have hcommU : ⁅C, zpowers v⁆ ≤ U :=
    (commutator_mono inf_le_left (zpowers_le.mpr S.inverter_mem)).trans
      (S.transvections.le.trans inf_le_left)
  have hzero : ⁅C, zpowers v⁆ = ⊥ := bot_unique
    ((le_inf hcommU hcommC).trans S.module_split_rotation.2.le_bot)
  have hvfix : zpowers v ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hUfix : U ≤ centralizer (C : Set G) := by
    intro u hu c hc
    exact le_centralizer W (S.core_le_module hu) c hc.1
  apply le_centralizer_iff.mp
  have hi : (U ⊓ V).relIndex V = 2 := by
    rw [← S.intersection]
    exact S.module_intersection_relIndex A
  rw [← sup_zpowers_eq_of_relIndex_prime (inf_le_right : U ⊓ V ≤ V)
    Nat.prime_two hi S.inverter_mem (fun hh => S.inverter_outside hh.1)]
  exact sup_le (inf_le_left.trans hUfix) hvfix

/-- The full action kernel on V splits on the two coprime pair summands. -/
theorem module_chosen_centralizer_split
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d) :
    W ⊓ centralizer (V : Set G) =
      (U ⊓ V) ⊔ (W ⊓ centralizer (zpowers g : Set G)) := by
  let := S.elementary
  let C := W ⊓ centralizer (zpowers g : Set G)
  have hC : C ≤ centralizer (V : Set G) := S.module_rotation_fixed_centralizes_chosen D A
  have hCU : C ≤ normalizer (U : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro c hc u hu
    exact le_centralizer W hc.1 u (S.core_le_module hu)
  apply le_antisymm
  · rintro x ⟨hxW, hxV⟩
    have hprod : x ∈ (U : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U C hCU, ← S.module_split_rotation.1]
      exact hxW
    obtain ⟨u, hu, c, hc, rfl⟩ := hprod
    have huC : u ∈ centralizer (V : Set G) := by
      have hh := (centralizer (V : Set G)).mul_mem hxV
        ((centralizer (V : Set G)).inv_mem (hC hc))
      simpa only [mul_inv_cancel_right] using hh
    have huV : u ∈ U ⊓ V := S.action_kernel ▸ ⟨hu, huC⟩
    exact mul_mem_sup huV hc
  · apply sup_le
    · exact le_inf (inf_le_left.trans S.core_le_module)
        (by rw [← S.action_kernel]; exact inf_le_right)
    · exact le_inf inf_le_left hC

/-- In the binary-three branch W meets the literal LT two-core in order sixteen. -/
theorem extraspecial_module_intersection_join_core_card
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hd : d = 3) (hW : Nat.card W = 64) :
    Nat.card (W ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G) = 16 := by
  let := S.elementary
  let C := W ⊓ centralizer (zpowers g : Set G)
  have hCnorm : C ≤ normalizer (U : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro c hc u hu
    exact le_centralizer W hc.1 u (S.core_le_module hu)
  have hcount := card_sup_eq_mul_of_normalizes_of_disjoint U C hCnorm S.module_split_rotation.2
  rw [← S.module_split_rotation.1, S.core_card, hd, hW] at hcount
  have hCcard : Nat.card C = 4 := by norm_num at hcount; omega
  have he : W ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = W ⊓ centralizer (V : Set G) := by
    let J := L ⊔ (T : Subgroup G)
    let a := V.normalizerMonoidHom.comp (inclusion (sup_le D.normalizes hTV))
    have hk := A.joinAut_ker D hTV
    ext w
    constructor
    · intro hw
      exact ⟨hw.1, D.core_centralizes hw.2⟩
    · intro hw
      have hj : w ∈ J := (le_sup_right : (T : Subgroup G) ≤ J) (S.module_le_sylow hw.1)
      refine ⟨hw.1, ⟨⟨w, hj⟩, ?_, rfl⟩⟩
      change (⟨w, hj⟩ : J) ∈ pCore 2 J
      rw [← hk]
      change (⟨w, hj⟩ : J) ∈ a.ker
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change w * (x : G) * w⁻¹ = x
      rw [← hw.2 x x.property, mul_inv_cancel_right]
  rw [he, S.module_chosen_centralizer_split D A]
  have hn : C ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro c hc u hu
    exact le_centralizer W hc.1 u (S.core_le_module hu.1)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint (U ⊓ V) C hn
    (S.module_split_rotation.2.mono_left inf_le_left), S.hyperplane, hd, hCcard]
  norm_num

/-- The literal component core has intersection of order sixteen with W. -/
theorem extraspecial_module_intersection_component_core_card
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) (hW : Nat.card W = 64) :
    Nat.card (W ⊓ L.pCoreIn 2 : Subgroup G) = 16 := by
  have hWL := S.extraspecial_module_le_component D A hTV he hf hd
  have heq : W ⊓ L.pCoreIn 2 = W ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    apply le_antisymm
    · exact inf_le_inf_left _ (pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
    · intro x hx
      exact ⟨hx.1, inf_pCoreIn_le_of_le 2 (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
        ⟨hWL hx.1, hx.2⟩⟩
  rw [heq]
  exact S.extraspecial_module_intersection_join_core_card D A hTV hd hW

private theorem frattini_commutator_eq_module_intersection
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (Q : Subgroup G) (hQT : Q ≤ (T : Subgroup G))
    (hPhiQ : (frattini P).map P.subtype ≤ normalizer (Q : Set G)) :
    ⁅Q, (frattini P).map P.subtype⁆ = W ⊓ Q := by
  let := S.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  let Φ := (frattini P).map P.subtype
  let Y := Φ ⊔ W
  have hΦW : Φ ≤ normalizer (W : Set G) := S.frattini_normalizes_module
  have hQY : Q ≤ normalizer (Y : Set G) :=
    hQT.trans (S.hstar.1.1.2.trans (S.extraspecial_frattini_module_normal he))
  have hdispY : ⁅Q, Φ⁆ ≤ Y :=
    (commutator_mono le_rfl le_sup_left).trans
      (le_normalizer_iff_commutator_le_right.mp hQY)
  have hdispQ : ⁅Q, Φ⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hPhiQ
  have hYT : Y ⊓ (T : Subgroup G) ≤ W := by
    rintro x ⟨hxY, hxT⟩
    have hprod : x ∈ (Φ : Set G) * (W : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right Φ W hΦW]
      exact hxY
    obtain ⟨a, ha, w, hw, rfl⟩ := hprod
    have haT : a ∈ (T : Subgroup G) := by
      simpa only [mul_inv_cancel_right] using (T : Subgroup G).mul_mem hxT
        ((T : Subgroup G).inv_mem (S.module_le_sylow hw))
    have ha1 : a = 1 := mem_bot.mp
      (((S.pgroup.to_le (map_subtype_le _)).disjoint_of_coprime T.isPGroup'
        S.odd_prime.coprime_two_right).le_bot ⟨ha, haT⟩)
    change a * w ∈ W
    rw [ha1, one_mul]
    exact hw
  apply le_antisymm
  · exact le_inf ((le_inf hdispY (hdispQ.trans hQT)).trans hYT) hdispQ
  · let E := W ⊓ Q
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
    have hn : Φ ≤ normalizer (E : Set G) :=
      (le_inf hΦW hPhiQ).trans inf_normalizer_le_normalizer_inf
    have hz : E ⊓ centralizer (Φ : Set G) = ⊥ := bot_unique
      ((inf_le_inf_right _ inf_le_left).trans hf.le)
    have hcop : Nat.Coprime (Nat.card Φ) (Nat.card E) := by
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
      rw [S.frattini_card_of_extraspecial he, hn]
      exact S.odd_prime.coprime_two_right.pow_right n
    have hm : ⁅E, Φ⁆ = E := by
      have hs := eq_commutator_sup_centralizer_of_solvable_coprime E Φ hn
        (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop
      simpa only [hz, sup_bot_eq] using hs.symm
    exact hm.ge.trans (commutator_mono inf_le_right le_rfl)

/-- The actual Frattini displacement on the component two-core is W∩O₂(L). -/
theorem extraspecial_component_core_displacement
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) : ⁅L.pCoreIn 2, (frattini P).map P.subtype⁆ = W ⊓ L.pCoreIn 2 := by
  have hQLQ := pCoreIn_mono_of_normalizes (p := 2) (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact S.frattini_commutator_eq_module_intersection he hf _ (hQLQ.trans hQT)
    ((S.extraspecial_frattini_le_component D A hTV he hf hd).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))

/-- An actual involution of W with nontrivial natural image excludes the
central SL₂(7) cover; hence O₂(L) is generated by its L-commutators. -/
theorem extraspecial_component_core_generated
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) (hW : Nat.card W = 64) : ⁅L.pCoreIn 2, L⁆ = L.pCoreIn 2 := by
  subst d
  let := S.elementary
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hWL := S.extraspecial_module_le_component D A hTV he hf rfl
  have hnot : ¬ W ≤ L.pCoreIn 2 := by
    intro hle
    have hc := S.extraspecial_module_intersection_component_core_card D A hTV he hf rfl hW
    rw [inf_eq_left.mpr hle, hW] at hc
    omega
  obtain ⟨w, hw, hwo⟩ := SetLike.not_le_iff_exists.mp hnot
  let l : L := ⟨w, hWL hw⟩
  have hl : l ∉ pCore 2 L := fun hl => hwo (mem_map_of_mem L.subtype hl)
  have hl2 : l ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)
  obtain ⟨e, _, _⟩ := A.natural
  have hcore := ChapterC.linearThree_core_eq_blockU_of_square_mem e l hl
    (hl2 ▸ (ChapterC.blockU L).one_mem)
  have heq := congrArg (Subgroup.map L.subtype) hcore
  change L.pCoreIn 2 = (⁅pCore 2 L, ⊤⁆ : Subgroup L).map L.subtype at heq
  rw [map_commutator, ← MonoidHom.range_eq_map, L.range_subtype] at heq
  exact heq.symm

/-- The exact source commutator on the larger kernel Q=O₂(LT). -/
theorem extraspecial_join_core_displacement
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, (frattini P).map P.subtype⁆ =
      W ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  exact S.frattini_commutator_eq_module_intersection he hf _ hQT
    (((S.extraspecial_frattini_le_component D A hTV he hf hd).trans
      (show L ≤ J from le_sup_left)).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

/-- The L-commutator of the larger kernel is precisely the component core. -/
theorem extraspecial_join_core_component_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) (hW : Nat.card W = 64) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ = L.pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hJL : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  have hJQ : J ≤ normalizer (Q : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  apply le_antisymm
  · exact (le_inf (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 J).trans hJL))
      (le_normalizer_iff_commutator_le_left.mp
        ((show L ≤ J from le_sup_left).trans hJQ))).trans
      (inf_pCoreIn_le_of_le 2 (show L ≤ J from le_sup_left))
  · rw [← S.extraspecial_component_core_generated h D A hTV he hf hd hW]
    exact commutator_mono (pCoreIn_mono_of_normalizes le_sup_left hJL) le_rfl

/-- The final T-orbit argument of 12.2.23. The construction of its fixed
orbit generator from the L₃(2) core module remains a separate source step. -/
theorem extraspecial_false_of_core_orbit
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P) (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hd : d = 3) (hW : Nat.card W = 64)
    (horbit : ∃ q ∈ H.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G),
      L.pCoreIn 2 = componentOrbit (zpowers q) (T : Subgroup G) ⊔ V) : False := by
  let Φ := (frattini P).map P.subtype
  let C := H.pCoreIn 2 ⊓ centralizer (Φ : Set G)
  obtain ⟨q, hq, hgen⟩ := horbit
  let R := componentOrbit (zpowers q) (T : Subgroup G)
  have hRC : R ≤ C := iSup_conjugates_le_of_le_normalizer _ _ _
    (zpowers_le.mpr hq) (S.hstar.1.1.2.trans
      (S.extraspecial_binary_three_core_centralizer_normal A he hcard hf hp hW))
  have hRV : R ≤ centralizer (V : Set G) :=
    (show R ≤ L.pCoreIn 2 from le_sup_left.trans hgen.ge).trans
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes)
  have hn : R ⊔ V ≤ normalizer (V : Set G) :=
    sup_le (hRV.trans (Subgroup.centralizer_le_normalizer _)) V.le_normalizer
  have hzero : ⁅R, Φ⁆ ≤ V := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr (hRC.trans inf_le_right)]
    exact bot_le
  have hbound : ⁅L.pCoreIn 2, Φ⁆ ≤ V := by
    rw [hgen]
    exact commutator_sup_le_of_relative_normal (R ⊔ V) R V Φ V hn
      le_sup_left le_sup_right hzero
      (le_normalizer_iff_commutator_le_left.mp S.frattini_normalizes)
  have hc := card_le_of_le hbound
  rw [S.extraspecial_component_core_displacement D A hTV he hf hd,
    S.extraspecial_module_intersection_component_core_card D A hTV he hf hd hW] at hc
  have hv : Nat.card V = 8 := by
    obtain ⟨_, e, _⟩ := A.natural
    rw [Nat.card_congr e.toEquiv, hd]
    norm_num
  omega

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
