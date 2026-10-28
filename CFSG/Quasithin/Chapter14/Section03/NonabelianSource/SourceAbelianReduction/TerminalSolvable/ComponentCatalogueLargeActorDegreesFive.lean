module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesOuter
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesInput
public import CFSG.Quasithin.Chapter12.Section08.Terminal.OrthogonalModels.Assembly
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import CFSG.Quasithin.Chapter12.Section08.Terminal.ThreeRank
public import Theory.Alternating.Aut

/-!
# The split six-space row when the center is the point

The literal G.11.2(5) marking identifies a normal A₈ acting on the binary
six-dimensional fully deleted permutation module. Restricting the source
point-fixing Sylow gives three-rank at least two in its point stabilizer.
On the other hand, 12.8.13(8) bounds the original tilded-plane centralizer
by one. If Z(U)=V₁, the dotted point-centralizer lifts into this centralizer
with a two-group kernel, giving a contradiction.

The final application supplies the degree premise of the existing component
consumer in this branch. The catalogue hypothesis is still explicit:
this module does not prove exhaustive recognition or the larger-center
exclusion for row (5).

Source: Aschbacher--Smith, 12.8.13(5),(8), printed pp.855--856;
G.11.2(5), printed p.364; 14.3.13--14, printed pp.993--994
(combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private def splitPermutationEquiv : Equiv.Perm (Fin 8) ≃*
    Theory.AlgebraicGroup.quadraticIsometrySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
  MulEquiv.ofBijective Atlas.Order20160A8.DeletedEight.orthogonalHom
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨Atlas.Order20160A8.DeletedEight.orthogonalHom_injective,
        Nat.card_congr ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.toEquiv⟩)

private def splitCoordinates :
    (ClassicalOrthogonal.formD 3 (ZMod 2)).IsometryEquiv Eight.form :=
  Atlas.Order20160A8.DeletedEight.splitIsometry.trans
    { __ := Eight.naturalEquiv, map_app' := Eight.form_naturalEquiv }

private theorem split_equivariant
    (a : Theory.AlgebraicGroup.quadraticIsometrySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)))
    (w : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
    splitCoordinates (a.val w) = BinaryPermutation.naturalRepresentation (Fin 8)
      (splitPermutationEquiv.symm a) (splitCoordinates w) := by
  obtain ⟨σ,rfl⟩ := splitPermutationEquiv.surjective a
  rw [MulEquiv.symm_apply_apply]
  change Eight.naturalEquiv
    (Atlas.Order20160A8.DeletedEight.splitEquiv
      ((Atlas.Order20160A8.DeletedEight.orthogonalHom σ).val w)) = _
  change Eight.naturalEquiv (Atlas.Order20160A8.DeletedEight.splitEquiv
    (Atlas.Order20160A8.DeletedEight.splitEquiv.symm
      (Atlas.Order20160A8.DeletedEight.quotientPerm σ
        (Atlas.Order20160A8.DeletedEight.splitEquiv w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Eight.naturalEquiv_equivariant σ _

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)

omit [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] in
/-- The literal split-orthogonal row yields a normal A₈ with its original
action on the fully deleted eight-point module. -/
theorem caseFive_selfcentralizing_marking
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ q : QuadraticForm (ZMod 2) (Additive F.Uhat),
      ∃ c : q.IsometryEquiv Eight.form,
      ∃ K : Subgroup F.TerminalHdot, K.Normal ∧ centralizer (K : Set F.TerminalHdot) = ⊥ ∧
      ∃ e : K ≃* alternatingGroup (Fin 8),
        ∀ (k : K) (u : F.Uhat),
          c (Additive.ofMul (F.terminalFaithfulHatAction k u)) =
            BinaryPermutation.naturalRepresentation (Fin 8) (e k).val (c (Additive.ofMul u)) := by
  obtain ⟨_,q,_,f,hq,H,hH,e,he⟩ := h5
  let a := splitPermutationEquiv.symm
  let J := H.map a.toMonoidHom
  have hJ : J.index ≤ 2 := by
    rw [show J.index = H.index from Subgroup.index_map_equiv H a]
    exact hH
  have hAJ : alternatingGroup (Fin 8) ≤ J :=
    Equiv.Perm.alternatingGroup_le_of_index_le_two hJ
  let j : F.TerminalHdot →* Equiv.Perm (Fin 8) :=
    a.toMonoidHom.comp (H.subtype.comp e.toMonoidHom)
  have hj : Function.Injective j := a.injective.comp (H.subtype_injective.comp e.injective)
  have hr : j.range = J := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact mem_map_of_mem a.toMonoidHom (e t).property
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨r,hr⟩ := e.surjective ⟨t,ht⟩
      exact ⟨r, congrArg (fun z : H => a z.val) hr⟩
  let K := (alternatingGroup (Fin 8)).comap j
  let kmap : K →* alternatingGroup (Fin 8) :=
    (j.comp K.subtype).codRestrict _ (fun k => k.property)
  have hk : Function.Bijective kmap := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hj (congrArg Subtype.val hxy))
    · intro x
      obtain ⟨t,ht⟩ := (hr.symm ▸ hAJ x.property : x.val ∈ j.range)
      exact ⟨⟨t,show j t ∈ alternatingGroup (Fin 8) from ht.symm ▸ x.property⟩,Subtype.ext ht⟩
  have hcent : centralizer (K : Set F.TerminalHdot) = ⊥ := by
    apply bot_unique
    intro x hx
    have hfix : j x ∈ centralizer (alternatingGroup (Fin 8) : Set (Equiv.Perm (Fin 8))) := by
      intro σ hσ
      obtain ⟨k,hσk⟩ := hk.surjective ⟨σ,hσ⟩
      have he := congrArg j (hx k k.property)
      simpa only [map_mul,show j (k : F.TerminalHdot) = σ from congrArg Subtype.val hσk] using he
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 8 (by decide)] at hfix
    exact mem_bot.mpr (hj ((mem_bot.mp hfix).trans j.map_one.symm))
  let c₀ : q.IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)) :=
    { __ := f, map_app' := fun w => (hq w).symm }
  let c := c₀.trans splitCoordinates
  refine ⟨q,c,K,inferInstance,hcent,MulEquiv.ofBijective kmap hk,?_⟩
  intro k u
  change splitCoordinates (f (F.terminalRepresentation k (Additive.ofMul u))) = _
  rw [he]
  exact split_equivariant (e k).val (f (Additive.ofMul u))

omit [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] in
/-- The literal split-orthogonal row yields a normal A₈ with its original
action on the fully deleted eight-point module. -/
theorem caseFive_alternating_marking
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ q : QuadraticForm (ZMod 2) (Additive F.Uhat),
      ∃ c : q.IsometryEquiv Eight.form,
      ∃ K : Subgroup F.TerminalHdot, K.Normal ∧
      ∃ e : K ≃* alternatingGroup (Fin 8),
        ∀ (k : K) (u : F.Uhat),
          c (Additive.ofMul (F.terminalFaithfulHatAction k u)) =
            BinaryPermutation.naturalRepresentation (Fin 8) (e k).val (c (Additive.ofMul u)) := by
  obtain ⟨q,c,K,hK,_,e,he⟩ := caseFive_selfcentralizing_marking (F := F) h5
  exact ⟨q,c,K,hK,e,he⟩

include s

/-- The original point-fixing Sylow puts the row (5) point stabilizer
in the four-block orbit, whose three-rank is at least two. -/
theorem caseFive_point_rank
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    2 ≤ primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) := by
  obtain ⟨q,c,K,hK,e,he⟩ := caseFive_alternating_marking (F := F) h5
  let := hK
  obtain ⟨P,hPv,_,_⟩ := s.normal_sylow
  have hfix : ∀ h ∈ (P : Subgroup F.TerminalHdot),
      F.terminalFaithfulHatAction h v.toMul = v.toMul := by
    intro h hh
    exact hPv hh
  have hv : v.toMul ≠ 1 := s.hypothesis.point_ne_zero
  obtain ⟨_,_,_,_,_,_,_,hr⟩ :=
    F.terminal_alternating_eight_residual_structure q c K e he P v.toMul hv hfix
  exact hr
/-- Source 12.8.13(8) for the original tilded plane. -/
theorem tilde_plane_three_rank_le_one :
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
theorem marked_line : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} := by
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
theorem point_preimage_le_tilde_plane (hZ : F.ZU = F.Vi 1) :
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
theorem point_three_rank_le_one_of_center_point (hZ : F.ZU = F.Vi 1) :
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

/-- The split six-space row cannot occur when the original center is the point. -/
theorem not_caseFive_of_center_point (hZ : F.ZU = F.Vi 1) :
    ¬ ChapterG.Section11.CaseFive F.terminalRepresentation B := by
  intro h5
  have hl := s.caseFive_point_rank h5
  have hu := s.point_three_rank_le_one_of_center_point hZ
  omega

/-- The catalogue gives the requested numerical alternatives in the original
center-equals-point branch. Exhaustive recognition remains explicit. -/
theorem degree_cases_of_catalogue_of_center_point
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) (hZ : F.ZU = F.Vi 1) :
    (finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
      2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
    (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))) :=
  (s.degree_cases_or_caseFive hc).resolve_right (s.not_caseFive_of_center_point hZ)

/-- The degree alternatives above discharge the numerical premise of the
actual component consumer. Catalogue recognition and the independent
component recognition and exclusion inputs remain explicit. -/
theorem component_of_catalogue_of_center_point
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) (hZ : F.ZU = F.Vi 1)
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    (∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
      ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
    (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H)) :=
  source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis
    (s.degree_cases_of_catalogue_of_center_point hc hZ) hfour hsix

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
