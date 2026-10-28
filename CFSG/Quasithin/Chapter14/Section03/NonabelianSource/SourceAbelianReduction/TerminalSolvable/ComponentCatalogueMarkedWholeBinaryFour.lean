module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesWholeForms

/-!
# The whole marked A₈ exclusion

The self-dual G.9 representation is the deleted permutation six-space.
Its literal point stabilizer has three-rank two. The original center-residual
geometry places the component in the image of the center centralizer, whose
point stabilizer has three-rank at most one by 12.8.13(8). The center-point
case has the same upper bound directly. No larger-actor premise is used.

Source: Aschbacher–Smith G.9.3(12), G.11.7, 12.8.13(8), 14.3.13–15.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s
open Module ChapterG.Section09.DefiningCharacteristic
open scoped commutatorElement
/-- The original symplectic form gives self-duality on every actual subgroup. -/
private theorem whole_restriction_selfDual (L : Subgroup F.TerminalHdot) :
    Nonempty (Representation.Equiv (F.terminalRepresentation.comp L.subtype)
      (Representation.dual (F.terminalRepresentation.comp L.subtype))) := by
  refine ⟨Representation.Equiv.mk (B.toDual s.hypothesis.nondegenerate) ?_⟩
  intro a
  ext u w
  change B (F.terminalRepresentation a u) w =
    B u (F.terminalRepresentation (a⁻¹ : L) w)
  have he := s.hypothesis.preserves a u (F.terminalRepresentation (a⁻¹ : L) w)
  simpa only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv,
    mul_inv_cancel, map_one, Module.End.one_apply] using he


/-- Source 12.8.13(8) for the original tilded plane. -/
private theorem tilde_plane_three_rank_le_one :
    primeRank 3 F.terminalTildePlaneCentralizer ≤ 1 := by
  let L := sourceResidual M Mc
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e,_,_,_,hIG,hIN,_,_,_,_,hIC,_⟩ := F.binary_generation (by decide) L
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer
    hcomm hsquare hspan s.nonabelian g s.parabolic_mem s.normalizer_not_mem
  exact F.lemma_12_8_13_eight s.simple.quasithin (by decide) L hIG hIN hIC ⟨e⟩

/-- The point in the given G.10 hypothesis is the original plane image. -/
private theorem marked_line : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hg := F.P_le_G₂ (by decide) (sourceResidual M Mc) h.L_normalizes_seed s.parabolic_mem
  have hle : hatSpace F (F.Vi 2) ≤ Submodule.span (ZMod 2) {v} := by
    rw [← s.hypothesis.fixedSpace_in_W]
    intro u hu
    refine ⟨?_,?_⟩
    · exact (map_mono (f := QuotientGroup.mk' (center F.U))
        (comap_mono (plane_le_E F g hg))) hu
    · intro x
      exact Xdot_fixes_line F F.terminalHatAction F.terminalHatAction_apply_mk g hg
        x x.property u hu
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_hatSpace_plane F (by decide) d.seed_center,
    finrank_span_singleton s.hypothesis.point_ne_zero]

/-- If the center is the point, the dotted point-centralizer lifts into the
actual tilded-plane centralizer. -/
private theorem point_preimage_le_tilde_plane (hZ : F.ZU = F.Vi 1) :
    (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap
        (QuotientGroup.mk' F.terminalHatAction.ker) ≤
      F.terminalTildePlaneCentralizer.subgroupOf F.H := by
  intro a ha
  apply mem_map.mpr
  refine ⟨a,?_,rfl⟩
  change QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H) a ∈
    centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)
  apply mem_centralizer_iff.mpr
  rintro _ ⟨b,hb,rfl⟩
  let bU : F.U := ⟨b,(F.le_seed 2).trans (le_conjugateSpanBy _ _) hb⟩
  have hbline : Additive.ofMul (QuotientGroup.mk' (center F.U) bU) ∈
      Submodule.span (ZMod 2) {v} := s.marked_line ▸ ⟨bU,hb,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hbline
  have hfix : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
      (Additive.ofMul (QuotientGroup.mk' (center F.U) bU)) =
      Additive.ofMul (QuotientGroup.mk' (center F.U) bU) := by
    rw [← hc,map_smul]
    exact congrArg (fun w => c • w) ha
  have hq : QuotientGroup.mk' (center F.U)
      (F.U.normalizerMonoidHom ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ bU) =
      QuotientGroup.mk' (center F.U) bU := by
    change F.terminalHatAction a (QuotientGroup.mk' (center F.U) bU) = _ at hfix
    rwa [F.terminalHatAction_apply_mk] at hfix
  have hz : (F.U.normalizerMonoidHom
      ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ bU) * bU⁻¹ ∈ center F.U := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center F.U) (_ * _) = 1
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  have hcomm : (a:G) * (b:G) * (a:G)⁻¹ * (b:G)⁻¹ ∈ F.Vi 1 := by
    rw [← hZ]
    exact mem_map_of_mem F.U.subtype hz
  have he : QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H) (a*b*a⁻¹*b⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcomm
  rw [map_mul,map_mul,map_mul,map_inv,map_inv] at he
  exact (mul_inv_eq_one.mp he |> mul_inv_eq_iff_eq_mul.mp).symm

/-- Under the literal center-point equality, the dotted point centralizer
inherits the source three-rank bound through the proved two-group kernel. -/
private theorem point_three_rank_le_one_of_center_point (hZ : F.ZU = F.Vi 1) :
    primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) ≤ 1 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := C.comap q
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', Recognition.terminal_kernel_of_center_point F d hZ]
    exact pCore_isPGroup
  have hk : IsPGroup 2 (q.subgroupComap C).ker := by
    have he : (q.subgroupComap C).ker = q.ker.subgroupOf D := by
      ext x
      simp only [MonoidHom.mem_ker, Subtype.ext_iff]
      rfl
    rw [he]
    exact hq.comap_subtype
  have hcop : Nat.Coprime 3 (Nat.card (q.subgroupComap C).ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hr := primeRank_le_of_surjective_of_coprime 3 (q.subgroupComap C)
    (q.subgroupComap_surjective_of_surjective C (QuotientGroup.mk'_surjective _)) hcop
  have hm := Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion (s.point_preimage_le_tilde_plane hZ)) (inclusion_injective _)
  have he := primeRank_equiv 3
    (subgroupOfEquivOfLe F.terminalTildePlaneCentralizer_le_H)
  exact hr.trans (hm.trans (he.le.trans s.tilde_plane_three_rank_le_one))


/-- A cube-one point lift centralizing the original center centralizes the
original plane: its displacement is central and has both two-power and odd order. -/
private theorem point_preimage_centralizes_plane_of_cube_one (a : F.H)
    (ha : QuotientGroup.mk' F.terminalHatAction.ker a ∈
      ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : (a:G) ∈ centralizer (F.ZU : Set G)) (ha3 : a ^ 3 = 1) :
    (a:G) ∈ centralizer (F.Vi 2 : Set G) := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  intro b hb
  let bU : F.U := ⟨b,(F.le_seed 2).trans (le_conjugateSpanBy _ _) hb⟩
  have hbline : Additive.ofMul (QuotientGroup.mk' (center F.U) bU) ∈
      Submodule.span (ZMod 2) {v} := s.marked_line ▸ ⟨bU,hb,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hbline
  have hfix : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
      (Additive.ofMul (QuotientGroup.mk' (center F.U) bU)) =
      Additive.ofMul (QuotientGroup.mk' (center F.U) bU) := by
    rw [← hc,map_smul]
    exact congrArg (fun w => c • w) ha
  have hq : QuotientGroup.mk' (center F.U)
      (F.U.normalizerMonoidHom ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ bU) =
      QuotientGroup.mk' (center F.U) bU := by
    change F.terminalHatAction a (QuotientGroup.mk' (center F.U) bU) = _ at hfix
    rwa [F.terminalHatAction_apply_mk] at hfix
  have hz : (F.U.normalizerMonoidHom
      ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ bU) * bU⁻¹ ∈ center F.U := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center F.U) (_ * _) = 1
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  let z := (a:G)*b*(a:G)⁻¹*b⁻¹
  have hzZ : z ∈ F.ZU := mem_map_of_mem F.U.subtype hz
  let α := MulAut.conj (a:G)
  have hαb : α b = z*b := by dsimp [α,z]; group
  have hαz : α z = z := by
    change (a:G)*z*(a:G)⁻¹=z
    exact mul_inv_eq_iff_eq_mul.mpr (haZ z hzZ).symm
  have hα3 : α^3 = 1 := by
    rw [show α^3 = MulAut.conj ((a:G)^3) from (map_pow _ _ _).symm]
    rw [show (a:G)^3=1 from congrArg Subtype.val ha3,map_one]
  have hcalc : α (α (α b)) = b := by
    have he := congrArg (fun t : MulAut G => t b) hα3
    simpa only [pow_succ,pow_zero,
      MulAut.mul_apply,MulAut.one_apply] using he
  simp only [hαb,map_mul,hαz] at hcalc
  have hz3 : z^3=1 := by
    apply mul_right_cancel (b := b)
    simpa only [pow_succ,pow_zero,
      one_mul,mul_assoc] using hcalc
  let zU : F.U := ⟨z,map_subtype_le (center F.U) hzZ⟩
  have hdv : orderOf zU ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)
  have he : zU=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (d.two.orderOf_coprime (by decide : Nat.Coprime 2 3) zU)
      (dvd_refl _) hdv)
  have hz1 : z=1 := congrArg Subtype.val he
  have hab : (a:G)*b=b*(a:G) :=
    commutatorElement_eq_one_iff_mul_comm.mp hz1
  exact hab.symm

/-- Three-elements in the source point lift which centralize Z(U) actually
centralize the marked plane. The elementary-rank criterion transfers the
source tilded-plane rank bound to this full point lift. -/
private theorem center_centralizing_point_lift_three_rank_le_one :
    primeRank 3 ((ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap
      (QuotientGroup.mk' F.terminalHatAction.ker) ⊓
      (centralizer (F.ZU : Set G)).subgroupOf F.H : Subgroup F.H) ≤ 1 := by
  let P := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap
    (QuotientGroup.mk' F.terminalHatAction.ker) ⊓
    (centralizer (F.ZU : Set G)).subgroupOf F.H
  change primeRank 3 P ≤ 1
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E hE
  let := hE
  let f : E →* G := F.H.subtype.comp (P.subtype.comp E.subtype)
  have hf : Function.Injective f := F.H.subtype_injective.comp
    (P.subtype_injective.comp E.subtype_injective)
  have ht (e : E) : f e ∈ F.terminalTildePlaneCentralizer := by
    have he3 : e.val.val ^ 3 = 1 := congrArg (fun x : P => x.val)
      (elemPow_eq_one_of_isElementaryAbelian (A := E) e.val e.property)
    have hc := s.point_preimage_centralizes_plane_of_cube_one e.val.val
      e.val.property.1 e.val.property.2 he3
    apply mem_map.mpr
    refine ⟨e.val.val,?_,rfl⟩
    change QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H) e.val.val ∈
      centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)
    rintro _ ⟨b,hb,rfl⟩
    exact congrArg (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
      (Subtype.ext (hc b hb))
  let j := f.codRestrict F.terminalTildePlaneCentralizer ht
  have hj : Function.Injective j := by
    intro a b he
    apply hf
    exact congrArg (fun z : F.terminalTildePlaneCentralizer => (z:G)) he
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 3 j hj).trans
    s.tilde_plane_three_rank_le_one
  let : IsElementaryAbelian 3 (⊤ : Subgroup E) := IsElementaryAbelian.of_injective
    (⊤ : Subgroup E).subtype (⊤ : Subgroup E).subtype_injective
  simpa only [card_top] using (primeRank_le_iff_elementary_card_le E).mp hr
    (⊤ : Subgroup E) inferInstance

/-- The actual dotted image of the center-centralizer has point-stabilizer
three-rank at most one. The restricted quotient kernel is a two-group. -/
private theorem center_centralizing_point_image_three_rank_le_one :
    primeRank 3 ((ChapterG.Section10.pointCentralizer F.terminalRepresentation v).subgroupOf
      (F.terminalDot (centralizer (F.ZU : Set G)))) ≤ 1 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let P := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap q ⊓ C
  let D := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).subgroupOf (C.map q)
  let f : P →* D := {
    toFun := fun a => ⟨⟨q a,mem_map_of_mem q a.property.2⟩,a.property.1⟩
    map_one' := Subtype.ext (Subtype.ext (q.map_one))
    map_mul' := fun a b => Subtype.ext (Subtype.ext (q.map_mul a b)) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a,ha,he⟩ := y.val.property
    have hap : q a ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v :=
      he.symm ▸ y.property
    exact ⟨⟨a,⟨hap,ha⟩⟩,Subtype.ext (Subtype.ext he)⟩
  have hk : f.ker ≤ (pCore 2 F.H).subgroupOf P := by
    intro a ha
    apply Recognition.terminal_kernel_centralizer_le_core F d
    refine ⟨a.property.2,?_⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun z : D => z.val.val) ha)
  have hp : IsPGroup 2 f.ker :=
    (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf P)).to_le hk
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (primeRank_le_of_surjective_of_coprime 3 f hf hcop).trans
    s.center_centralizing_point_lift_three_rank_le_one


/-- The natural whole A₈ action contradicts the original E point-centralizer
bounds, both when the center is the marked point and when it is larger. -/
theorem not_whole_alternating_eight (hi : I = ⊤)
    (hHL : componentOrbit L ⊤ = L) (e₀ : L ≃* alternatingGroup (Fin 8)) : False := by
  have h9 := s.componentHypothesis_of_whole hi
  rw [hHL] at h9
  let : L.Normal := h9.normal_H
  obtain ⟨e,c,hc⟩ := BinaryLinearRecognition.four_alternating_natural_of_selfDual h9
    (s.whole_restriction_selfDual L) (e₀.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hLc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation s.hypothesis.faithful L e c hc
  let q := BinaryPermutation.TerminalOrthogonal.Eight.form.comp c.toLinearMap
  let c' : q.IsometryEquiv BinaryPermutation.TerminalOrthogonal.Eight.form :=
    { __ := c, map_app' := fun _ => rfl }
  obtain ⟨P,hPv,_,_⟩ := s.actor_normalSylow
  have hfix : ∀ a ∈ (P : Subgroup F.TerminalHdot),
      F.terminalFaithfulHatAction a v.toMul = v.toMul := fun a ha => hPv ha
  obtain ⟨_,_,_,_,_,_,hr,hge⟩ :=
    F.terminal_alternating_eight_residual_structure q c' L e
      (fun l u => hc l (Additive.ofMul u)) P v.toMul s.hypothesis.point_ne_zero hfix
  by_cases hZ : F.ZU = F.Vi 1
  · have hu := s.point_three_rank_le_one_of_center_point hZ
    change 2 ≤ primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) at hge
    omega
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  obtain ⟨hNH,hHN,hNC,hN⟩ := Recognition.rankTwo_center_residual_geometry
    h F d s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis hZ
  let N := Recognition.centerConjugateResidual F g
  let NH := N.subgroupOf F.H
  let : NH.Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  let : (F.terminalDot N).Normal := Normal.map inferInstance
    (QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 8))
  let : IsSimpleGroup L := e.isSimpleGroup
  have hLa : ¬ IsMulCommutative L := fun hh =>
    h9.component.isCComponent.not_isSolvable (by let := hh; infer_instance)
  have hLN : L ≤ F.terminalDot N :=
    simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot L hLa hLc _ hN
  have hLC : L ≤ F.terminalDot (centralizer (F.ZU : Set G)) :=
    hLN.trans (map_mono (comap_mono hNC))
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  let f : C.subgroupOf L →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hLC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := s.center_centralizing_point_image_three_rank_le_one
  change primeRank 3 (C.subgroupOf L) = 2 at hr
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega


/-- The binary PSL₄(2) carrier is the same excluded A₈ component. -/
theorem not_whole_binary_four (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    (e : L ≃* PSL(4,ZMod 2)) : False :=
  s.not_whole_alternating_eight hi hHL
    (e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)

/-- The impossible whole binary-four row closes the original local lift. -/
theorem local_lift_of_whole_binary_four (hi : I = ⊤)
    (hHL : componentOrbit L ⊤ = L) (e : L ≃* PSL(4,ZMod 2)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_binary_four hi hHL e).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
