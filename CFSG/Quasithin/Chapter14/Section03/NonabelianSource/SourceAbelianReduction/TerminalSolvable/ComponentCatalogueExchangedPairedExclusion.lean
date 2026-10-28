module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedRecognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubic
public import Theory.Representation.SimplePairCoordinates
public import Theory.Representation.BinaryPermutation.PairedPointRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import CFSG.Quasithin.Chapter12.Section08.Terminal.ThreeRank
public import Theory.Quasithin.Rank
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# The original paired direct-sum exclusion

The small-actor geometry makes the original center the marked point, so
12.8.13(8) bounds the dotted point-centralizer's three-rank by one. The
original square form has a nonzero singular vector in the selected A₅
constituent. A natural SL₂(4) action would make that entire constituent
singular, forcing its noncentral action kernel to vanish. Thus the literal
constituent is the orthogonal four-space. Separating conjugate quotient
maps give the actual A₅ × A₅ action on the direct sum; its Sylow-fixed point
has two independent cubic stabilizers, contradicting the source rank bound.

The original component, actor, invariant form, quotient maps and ambient
hypotheses are retained. This proves the unmarked paired branch exclusion,
not the different marked tensor/wreath branch.
Source: Aschbacher–Smith G.11.2(12), 12.8.13(7)–(8), and 14.3.15,
printed pp.364,855–856,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
local instance : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

open scoped MatrixGroups in
private theorem natural_marking_transitive {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J W)
    (a : J ≃* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : Representation.Equiv σ
      ((Representation.SL2.BinarySmall.natural).comp a.toMonoidHom)) :
    ∀ u w : W, u ≠ 0 → w ≠ 0 → ∃ z, σ z u = w := by
  intro u w hu hw
  have hcu : c u ≠ 0 := fun he => hu (c.toLinearEquiv.map_eq_zero_iff.mp he)
  have hcw : c w ≠ 0 := fun he => hw (c.toLinearEquiv.map_eq_zero_iff.mp he)
  obtain ⟨b,hb⟩ := Matrix.SL2.exists_mulVec_eq
    (Representation.OrthogonalFourMinus.FiniteModel.Field 1) (c u) (c w) hcu hcw
  refine ⟨a.symm b, c.injective ?_⟩
  have hc := Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap (a.symm b) u
  change c (σ (a.symm b) u) = Representation.SL2.BinarySmall.natural (a (a.symm b)) (c u) at hc
  rw [a.apply_symm_apply] at hc
  exact hc.trans hb

private theorem orthogonal_of_not_transitive {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) J W) [σ.IsIrreducible]
    (e : J ≃* alternatingGroup (Fin 5)) (hn : ∃ a, σ a ≠ 1)
    (ht : ¬ ∀ u w : W, u ≠ 0 → w ≠ 0 → ∃ a, σ a u = w) :
    ∃ a : J ≃* alternatingGroup (Fin 5), Nonempty (Representation.Equiv σ
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        a.toMonoidHom)) := by
  rcases (CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
    σ e hn).2 with ⟨a,⟨c⟩⟩ | h
  · exact (ht (natural_marking_transitive σ a c)).elim
  · exact h

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedPairedSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedPairedSource T M Mc F g B v L I)
include s
local instance : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

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



theorem center_eq_point : F.ZU = F.Vi 1 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card s.centralizer_quotient.some
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  exact (Recognition.rankTwo_small_actor_geometry h F g d s.nonabelian
    s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor).2.2.2.1

theorem point_three_rank_le_one :
    primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) ≤ 1 :=
  s.point_three_rank_le_one_of_center_point s.center_eq_point

theorem constituent_degree_four : finrank (ZMod 2) I = 4 := by
  let σ := s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype
  let : Representation.IsIrreducible σ := s.image_irreducible
  have hn : ∃ a, σ a ≠ 1 := by
    by_contra! ht
    apply s.image_ne_bot
    apply bot_unique
    intro a ha
    have hh := ht ⟨a,ha⟩
    exact mem_bot.mpr (s.image_setup.faithful (hh.trans (map_one s.imageAction).symm))
  exact (ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
    σ s.image_alternating_five.some hn).1

theorem degree_eight : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
  obtain ⟨hgeo,hspan,_⟩ := s.completion
  obtain ⟨x,_,he,hd,_⟩ := hgeo
  have hi := (LinearMap.GeneralLinearGroup.toLinearEquiv
    (F.terminalRepresentation.asGroupHom (x : F.TerminalHdot))).injective
  have hm := (Submodule.equivMapOfInjective (F.terminalRepresentation (x : F.TerminalHdot)) hi I).finrank_eq
  have hs := Submodule.finrank_sup_add_finrank_inf_eq I
    (I.map (F.terminalRepresentation (x : F.TerminalHdot)))
  rw [← he,hspan,finrank_top,hd.eq_bot,finrank_bot,add_zero,← hm,s.constituent_degree_four] at hs
  omega

theorem actor_rank_three : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 := by
  have hm := (s.hypothesis.numerical_equality_of_actor_dimension_le s.small_actor).2.1
  simpa only [s.degree_eight] using hm

theorem actor_card_eight : Nat.card (F.terminalDot (F.X g)) = 8 := by
  change Nat.card (Additive (F.terminalDot (F.X g))) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,s.actor_rank_three]
  decide

/-- The source square form supplies a nonzero singular vector in the selected
constituent and is nondegenerate on the whole terminal module. -/
theorem quadratic_singular_constituent :
    ∃ q : QuadraticForm (ZMod 2) (Additive F.Uhat), q.polarBilin.Nondegenerate ∧
      (∀ a u, q (F.terminalRepresentation a u) = q u) ∧
      ∃ i : I, i ≠ 0 ∧ q i = 0 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card s.centralizer_quotient.some
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  let q := Recognition.centerPointQuadraticForm F d (by decide) s.center_eq_point
  have hc := Recognition.rankTwo_small_actor_conclusions h F d s.nonabelian g
    s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor
  have hq : ∀ a u, q (F.terminalRepresentation a u) = q u := by
    intro a u
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hc.invariant a u.toMul
  obtain ⟨x,_,_,_,_,i,hi,hv,hiW,_⟩ := s.completion.1
  refine ⟨q,hc.nondegenerate,hq,⟨i,i.property.1⟩,?_,?_⟩
  · intro hz
    exact hi (congrArg Subtype.val hz)
  · apply hc.singular
    have hh : (i : Additive F.Uhat) ∈ I ⊓ hatSpace F (F.E g) := by
      rw [hiW]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact hh.2

/-- No transitive action on the nonzero constituent vectors can preserve
the original square form: the singular orbit would make this constituent
isotropic, forcing the noncentral action kernel to be trivial. -/
theorem not_transitive_constituent
    (ht : ∀ u w : I, u ≠ 0 → w ≠ 0 →
      ∃ a : componentOrbit L ⊤,
        (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
          s.selected.invariant).toRepresentation a u = w) : False := by
  let ρ := F.terminalRepresentation
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  obtain ⟨q,hnd,hq,i,hi,hqi⟩ := s.quadratic_singular_constituent
  have hz (u : I) : q u = 0 := by
    by_cases hu : u = 0
    · simp only [hu,Submodule.coe_zero,map_zero]
    · obtain ⟨a,ha⟩ := ht i u hi hu
      exact (congrArg (fun z : I => q z) ha).symm.trans ((hq a i).trans hqi)
  have hiso : ∀ u ∈ I, ∀ w ∈ I, q.polarBilin u w = 0 := by
    intro u hu w hw
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      hz ⟨u+w,I.add_mem hu hw⟩,hz ⟨u,hu⟩,hz ⟨w,hw⟩,sub_zero]
  have hpres : ∀ a u w, q.polarBilin (ρ a u) (ρ a w) = q.polarBilin u w := by
    intro a u w
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,← map_add]
    change q (F.terminalRepresentation a (u+w)) - q (F.terminalRepresentation a u) -
      q (F.terminalRepresentation a w) = _
    rw [hq,hq,hq]
  obtain ⟨hgeo,hspan,_,_⟩ := s.completion
  have hxinv (x : F.terminalDot (F.X g)) : (x : F.TerminalHdot)⁻¹ = x :=
    inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (x : F.TerminalHdot) x.property)
  have hpair (x : F.terminalDot (F.X g))
      (hx : I.map (ρ (x : F.TerminalHdot)⁻¹) ≠ I) :
      I ⊔ I.map (ρ (x : F.TerminalHdot)⁻¹) = ⊤ := by
    rw [hxinv] at hx ⊢
    exact (s.hypothesis.independent_orbit_pair I s.dimension_gt_two
      s.independent x hx).1.symm.trans hspan
  obtain ⟨x,hx,_⟩ := hgeo
  have hex : ∃ x : F.terminalDot (F.X g), I.map (ρ (x : F.TerminalHdot)⁻¹) ≠ I :=
    ⟨x,by rwa [hxinv]⟩
  obtain ⟨hf,_,_⟩ := s.selected.faithful_dual_of_isotropic_pair ρ
    s.hypothesis.faithful q.polarBilin hnd hpres s.fixedSpace_eq_bot s.irreducible
    hiso hex hpair
  apply s.noncentral_kernel
  rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
  exact bot_le

private theorem orbitProjection_action (a : componentOrbit L ⊤) :
    s.imageAction (s.orbitProjection a).val =
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation a := rfl

private theorem image_nontrivial :
    ∃ a : s.image (componentOrbit L ⊤), s.imageAction a.val ≠ 1 := by
  by_contra! ht
  apply s.image_ne_bot
  apply bot_unique
  intro a ha
  exact mem_bot.mpr (s.image_setup.faithful
    ((ht ⟨a,ha⟩).trans (map_one s.imageAction).symm))

private theorem image_not_transitive :
    ¬ ∀ u w : I, u ≠ 0 → w ≠ 0 →
      ∃ a : s.image (componentOrbit L ⊤), s.imageAction a.val u = w := by
  intro ht
  apply s.not_transitive_constituent
  intro u w hu hw
  obtain ⟨b,hb⟩ := ht u w hu hw
  obtain ⟨z,hz⟩ := s.orbitProjection_surjective b
  refine ⟨z,?_⟩
  rw [← s.orbitProjection_action z,hz]
  exact hb

open scoped MatrixGroups in
/-- The literal constituent image has the orthogonal A₅ module. Its natural
SL₂(4) alternative is excluded by the original square form, not by its degree. -/
theorem orthogonal_constituent :
    ∃ a : s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.Equiv
        (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
        (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
          a.toMonoidHom)) := by
  let σ := s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype
  let : Representation.IsIrreducible σ := s.image_irreducible
  exact orthogonal_of_not_transitive σ s.image_alternating_five.some
    s.image_nontrivial s.image_not_transitive

/-- The original orbit projection has its actual orthogonal module and a
nontrivial kernel. The latter is the source noncentral-kernel clause. -/
theorem orthogonal_orbit_projection :
    ∃ p : componentOrbit L ⊤ →* alternatingGroup (Fin 5),
      Function.Surjective p ∧ p.ker ≠ ⊥ ∧
      ∃ c : I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5),
        ∀ a u, c ((invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
          s.selected.invariant).toRepresentation a u) =
            BinaryPermutation.naturalRepresentation (Fin 5) (p a).val (c u) := by
  obtain ⟨e,⟨c⟩⟩ := s.orthogonal_constituent
  let p := e.toMonoidHom.comp s.orbitProjection
  refine ⟨p,e.surjective.comp s.orbitProjection_surjective,?_,c.toLinearEquiv,?_⟩
  · intro hb
    apply s.noncentral_kernel
    intro a ha
    have hR := congrArg Units.val (MonoidHom.mem_ker.mp ha)
    have hp : s.orbitProjection a = 1 := by
      apply Subtype.ext
      apply s.image_setup.faithful
      exact hR.trans (map_one s.imageAction).symm
    have ha1 : a = 1 := mem_bot.mp (hb ▸ (show a ∈ p.ker by
      change e (s.orbitProjection a) = 1
      rw [hp,map_one]))
    rw [ha1]
    exact one_mem _
  · intro a u
    exact Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap
      (s.orbitProjection a) u

/-- The same original component orbit acts as the direct sum of its two
orthogonal A₅ factors. Both the group and vector equivalences retain the
literal terminal action. -/
theorem paired_action_coordinates :
    ∃ e : componentOrbit L ⊤ ≃*
        (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
      ∃ c : Additive F.Uhat ≃ₗ[ZMod 2]
          (BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5)),
        ∀ (a : componentOrbit L ⊤) u, c (F.terminalRepresentation a u) =
          (BinaryPermutation.naturalRepresentation (Fin 5) (e a).1.val (c u).1,
           BinaryPermutation.naturalRepresentation (Fin 5) (e a).2.val (c u).2) := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  obtain ⟨p,hp,hpk,c,hc⟩ := s.orthogonal_orbit_projection
  obtain ⟨hg,hspan,_,_⟩ := s.completion
  obtain ⟨x,_,hpair,hdis,_⟩ := hg
  exact Representation.simple_pair_coordinates F.terminalRepresentation
    s.hypothesis.faithful H
    (invariantSubspace F.terminalRepresentation H I s.selected.invariant)
    (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5))
    p hp hpk c hc x hdis (hpair.symm.trans hspan)

/-- The original paired action violates the source 12.8.13(8) point rank
bound. All ambient, form and constituent hypotheses come from the source. -/
theorem false_of_source : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  obtain ⟨e,c,hc⟩ := s.paired_action_coordinates
  have hs := (Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    s.centralizer_quotient.some F s.nonabelian g s.parabolic_mem s.normalizer_not_mem
    s.hypothesis).1
  have hr := Representation.BinaryPermutationPair.two_le_point_rank
    F.terminalRepresentation H e c hc (pointSylow (F := F)) v
    (fun _ ha => hs ha)
    (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) (fun _ => Iff.rfl)
  exact (by omega : ¬ 2 ≤ 1) (hr.trans s.point_three_rank_le_one)

end ExchangedPairedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
