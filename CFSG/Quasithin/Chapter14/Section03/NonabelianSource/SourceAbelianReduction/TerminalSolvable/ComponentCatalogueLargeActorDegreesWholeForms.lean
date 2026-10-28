module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesWholeModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
public import Theory.Representation.G2BinaryDerivedRatios
public import Theory.SpecificGroups.G2.BinaryElementaryRank
public import Theory.Representation.BinaryPermutation.EightCentralizer
public import Theory.Representation.Mathieu.SmallModules.M22SymplecticExclusion
/-!
# Whole-component form exclusions for the original larger actor

Odd-order averaging rules out an invariant alternating form on either native
M₂₂ ten-space. Genuine small-module recognition therefore excludes the M₂₂
whole component. For A₈, self-duality recognizes the natural deleted module;
its trivial invertible commutant and the original rank-two residual geometry
contradict the point-centralizer three-rank calculation.

A whole G₂(2)′ component forces degree six and actor rank three. Natural-module
recognition embeds the full dotted group in G₂(2). The image contains its
derived group, while the original actor is too large to lie in that derived
group, so the embedding is surjective. This identifies the full dotted group.

The refined numerical alternatives feed the actual component consumer. They
retain the exceptional marked S₈ action, nonbinary symplectic components and
literal two-component whole orbits; their exclusion is still required for
14.3.14.

Source: Aschbacher–Smith G.7.3, G.9.3, G.11.7 and H.13.1–2,
printed pp.348,354–357,367–368,395–396; 12.8.13 and 14.3.13–14,
pp.855–856,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11 ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic
open Chapter1.Section02.LocalModels
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

variable {L : Subgroup F.TerminalHdot}
  (h9 : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
    (F.terminalDot (F.X g)) L L
    (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
include h9


/-- The actual G.9 degree window puts a whole M₂₂ component among its
native ten-spaces, neither of which admits the original alternating form. -/
theorem not_single_mathieu_twenty_two (e : L ≃* Sporadic.Mathieu.M22) : False := by
  have hb := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hb
  have hr := Sporadic.Mathieu.m22_automorphism_twoRank_le_five
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  exact Representation.MathieuSmall.M22Recognition.not_alternating_of_small_degree σ
    (h9.faithful.comp (L.subtype_injective.comp e.symm.injective)) (by omega)
    B s.hypothesis.alternating s.hypothesis.nondegenerate
    (fun a u w => s.hypothesis.preserves (e.symm a) u w)

/-- The natural whole A₈ action contradicts the original E point-centralizer
bounds, both when the center is the marked point and when it is larger. -/
theorem not_single_alternating_eight (e₀ : L ≃* alternatingGroup (Fin 8)) : False := by
  let : L.Normal := h9.normal_H
  obtain ⟨e,c,hc⟩ := BinaryLinearRecognition.four_alternating_natural_of_selfDual h9
    (s.whole_restriction_selfDual L) (e₀.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hLc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation s.hypothesis.faithful L e c hc
  let q := BinaryPermutation.TerminalOrthogonal.Eight.form.comp c.toLinearMap
  let c' : q.IsometryEquiv BinaryPermutation.TerminalOrthogonal.Eight.form :=
    { __ := c, map_app' := fun _ => rfl }
  obtain ⟨P,hPv,_,_⟩ := s.normal_sylow
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

/-- A whole binary G₂′ component gives degree six, actor rank three and an
isomorphism of the full dotted group with G₂(2). -/
theorem single_binary_g2_degree_cases
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
      Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)) := by
  let : L.Normal := h9.normal_H
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  have hr := h9.toSetup.rank_le_automorphisms (L := L) (by
    rw [normalizer_eq_top_iff.mpr h9.normal_H]
    exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e),
    ← primeRank_equiv 2 Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv] at hr
  have hb : primeRank 2 (Atlas.G2.Model (ZMod 2)) ≤ 3 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro A hA
    let := hA
    exact Atlas.G2.binary_elementary_card_le_eight A
  have hl := s.half_degree_le_actor
  have hd6 : finrank (ZMod 2) (Additive F.Uhat) = 6 := by
    obtain ⟨n,hn⟩ := s.even_degree
    omega
  have hm3 : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 := by omega
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  obtain ⟨a,c,hc⟩ := G2Recognition.BinarySix.quasiequivalent_of_finrank_eq_six σ hd6
  let E := e.trans a
  let c' : Additive F.Uhat ≃ₗ[ZMod 2] Atlas.G2.Natural.BinaryNormalizer.N :=
    LinearEquiv.ofBijective (c.toAddMonoidHom.toZModLinearMap 2) c.bijective
  have hE (l : L) (w : Additive F.Uhat) :
      c' (F.terminalRepresentation l w) =
        Atlas.G2.Natural.derivedAction (ZMod 2) (E l) (c' w) := by
    change c (F.terminalRepresentation l w) =
      Atlas.G2.Natural.action (ZMod 2) (a (e l)).val (c w)
    have he := hc (e l) w
    simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,
      Subgroup.coe_subtype,G2Recognition.derivedNaturalBinary_apply,
      G2Recognition.naturalBinary_apply] using he
  obtain ⟨f,hf,hfL,_⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    F.terminalRepresentation L E c' hE s.hypothesis.faithful
  have hder : commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range := by
    intro x hx
    obtain ⟨l,hl⟩ := E.surjective ⟨x,hx⟩
    exact ⟨l,(hfL l).trans (congrArg Subtype.val hl)⟩
  let A := (F.terminalDot (F.X g)).map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hcard : Nat.card A = 8 := by
    rw [Subgroup.card_map_of_injective hf,h9.card_actor,hm3]
    norm_num
  have hnot : ¬ A ≤ commutator (Atlas.G2.Model (ZMod 2)) := by
    intro hA
    let D := commutator (Atlas.G2.Model (ZMod 2))
    let E := A.subgroupOf D
    have hcardE : Nat.card E = 8 :=
      (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans hcard
    have he : IsElementaryTwo E := by
      refine ⟨?_,IsElementaryAbelian.subgroupOf hA⟩
      intro hz
      rw [hz,card_bot] at hcardE
      omega
    have hh := Atlas.G2.Natural.BinaryNormalizer.derived_rank_le_two E he
    rw [Representation.BinaryOffender.rank,hcardE] at hh
    norm_num at hh
  obtain ⟨x,hx,hxd⟩ := SetLike.not_le_iff_exists.mp hnot
  have htop : f.range = ⊤ := Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le
    hder ((Subgroup.map_le_range f _ ) hx) hxd
  exact ⟨hd6,hm3,⟨MulEquiv.ofBijective f ⟨hf,MonoidHom.range_eq_top.mp htop⟩⟩⟩

/-- The remaining whole action has either a simple nonbinary symplectic
component or the literal pair with its original action comparison. -/
@[expose] def RemainingWholeSymplecticOrbit {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop :=
  (componentOrbit L ⊤ = L ∧ IsSimpleGroup L ∧
    ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSp L 2 (2^n)) ∨
    ∃ L₂ : Subgroup D, IsComponent D L₂ ∧ L₂ ≠ L ∧ componentOrbit L ⊤ = L ⊔ L₂ ∧
      TwoComponents.FactorReduction.ModelRestrictions.QuotientModel (L ⧸ center L) ∧
      (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
        Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))

omit h9 in
/-- The actual A₈ and M₂₂ whole actions are excluded, and the binary G₂′
branch gives the full G₂(2). Only nonbinary symplectic whole components,
paired whole orbits and the exceptional marked S₈ action remain. -/
theorem degree_cases_or_full_four_or_symplectic_or_pair :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          RemainingWholeSymplecticOrbit F.terminalRepresentation L) := by
  rcases s.degree_cases_or_full_four_or_whole_models with good | full | ⟨hd,L,hL,hm,ho,h9,hr⟩
  · exact Or.inl good
  · exact Or.inr (Or.inl full)
  · rcases hr with ⟨he,hi,hmodel⟩ | hpair
    · have h : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
          (F.terminalDot (F.X g)) L L
          (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
        simpa only [he] using h9
      cases hmodel with
      | alternating_eight e => exact (s.not_single_alternating_eight h e.some).elim
      | symplectic n hn model =>
        exact Or.inr (Or.inr ⟨hd,L,hL,hm,ho,h9,Or.inl ⟨he,hi,n,hn,model⟩⟩)
      | binary_g2 e => exact Or.inl (Or.inr (s.single_binary_g2_degree_cases h hd e.some))
      | mathieu e => exact (s.not_single_mathieu_twenty_two h e.some).elim
    · exact Or.inr (Or.inr ⟨hd,L,hL,hm,ho,h9,Or.inr hpair⟩)

omit h9 in
/-- Apply the refined numerical alternatives to the actual component consumer.
The successful degree-six branch still identifies the full dotted G₂(2). -/
theorem component_or_full_four_or_symplectic_or_pair
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
          RemainingWholeSymplecticOrbit F.terminalRepresentation L) := by
  rcases s.degree_cases_or_full_four_or_symplectic_or_pair with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
