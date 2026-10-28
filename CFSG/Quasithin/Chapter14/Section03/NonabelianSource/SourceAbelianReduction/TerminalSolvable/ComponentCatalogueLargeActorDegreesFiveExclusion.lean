module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesCenter
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# Excluding the split six-space row for the original larger actor

The remaining G.11.2(5) branch has Z(U)>V₁. The original center-conjugate
residual then has nontrivial normal dotted image and centralizes Z(U).
The row's self-centralizing normal A₈ lies in this image. Its point stabilizer
has three-rank two by the actual deleted permutation action and the
point-fixing Sylow condition.

To contradict this, lift an elementary three-subgroup of the dotted point
centralizer inside the image of C_H(Z(U)). A cube-one lift fixing the dotted
point centralizes the original plane: its central displacement is fixed by
the lift and is killed by both an odd power and a power of two. Thus the
source 12.8.13(8) tilded-plane bound gives three-rank at most one. The
restricted action kernel is a two-group, so this bound survives the quotient.

Together with the earlier exclusions, this removes every exceptional row
of the source catalogue. The final theorem applies these degree alternatives
to the literal component consumer. Exhaustive G.11.2 recognition is still
an explicit premise; the full dotted-group equivalence in degree six is retained.

Source: Aschbacher--Smith, 12.8.10--13, printed pp.853--856;
G.11.2(5), printed p.364; 14.3.13--14, printed pp.993--994
(combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s


/-- A cube-one point lift centralizing the original center centralizes the
original plane: its displacement is central and has both two-power and odd order. -/
theorem point_preimage_centralizes_plane_of_cube_one (a : F.H)
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
theorem center_centralizing_point_lift_three_rank_le_one :
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
theorem center_centralizing_point_image_three_rank_le_one :
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

/-- Row (5) cannot occur for the original larger actor. -/
theorem not_caseFive : ¬ ChapterG.Section11.CaseFive F.terminalRepresentation B := by
  intro h5
  have hZ := (s.caseFive_center_and_low_rank h5).1
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
  obtain ⟨q,c,K,hKn,hKc,e,he⟩ := caseFive_selfcentralizing_marking (F := F) h5
  let := hKn
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 8))
  let : IsSimpleGroup K := e.isSimpleGroup
  have hKa : ¬ IsMulCommutative K := by
    intro hcomm
    let := hcomm
    let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hKN : K ≤ F.terminalDot N :=
    simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K hKa hKc _ hN
  have hKC : K ≤ F.terminalDot (centralizer (F.ZU : Set G)) :=
    hKN.trans (map_mono (comap_mono hNC))
  obtain ⟨P,hPv,_,_⟩ := s.normal_sylow
  have hfix : ∀ a ∈ (P : Subgroup F.TerminalHdot),
      F.terminalFaithfulHatAction a v.toMul = v.toMul := by
    intro a ha
    exact hPv ha
  obtain ⟨_,_,_,_,_,_,hr,_⟩ :=
    F.terminal_alternating_eight_residual_structure q c K e he P v.toMul
      s.hypothesis.point_ne_zero hfix
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  let f : C.subgroupOf K →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hKC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := s.center_centralizing_point_image_three_rank_le_one
  change primeRank 3 (C.subgroupOf K) = 2 at hr
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega


/-- The catalogue gives the requested numerical alternatives for the original actor. Exhaustive recognition remains explicit. -/
theorem degree_cases_of_catalogue
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) :
    (finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
      2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
    (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))) :=
  (s.degree_cases_or_caseFive hc).resolve_right s.not_caseFive

/-- The degree alternatives above discharge the numerical premise of the
actual component consumer. Catalogue recognition and the independent
component recognition and exclusion inputs remain explicit. -/
theorem component_of_catalogue
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g)))
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
    (s.degree_cases_of_catalogue hc) hfour hsix

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
