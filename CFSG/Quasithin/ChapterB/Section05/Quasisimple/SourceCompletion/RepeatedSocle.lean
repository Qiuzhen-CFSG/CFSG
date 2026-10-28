module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryThreeReconstruction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryWhole
/-!
# Sylow-stable natural socles and the binary whole group

A nonzero coordinate of an irreducible submodule of a repeated-natural action
is an isomorphism to the same marked natural action. Thus all simple submodules
are isomorphic. A.1.42 then supplies a submodule fixed by the specified two-group.

For a binary natural action every linear automorphism already comes from SL.
Inside the actual local group LT, its generalized Fitting subgroup is L and
has trivial center. The natural submodule stabilizer is consequently L itself,
so the whole Sylow subgroup lies in L. Original offender generation gives G=L.
The final consumer applies this to the proved doubled SL3(2) moved module.

Source: Aschbacher--Smith B.5.1, printed p.101, case (I), and A.1.42.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every simple constituent uses the same actual natural actor mark. -/
theorem repeated_natural_submodule_equiv (F : BinaryField) {d r : ℕ} (hd : 2 ≤ d)
    (a : ActionEquiv ρ (repeated (linearNatural F d) r))
    (N : Subrepresentation ρ) (hN : IsIrreducible N.toRepresentation) :
    Nonempty (N.toRepresentation.Equiv ((linearNatural F d).comp a.groupEquiv.toMonoidHom)) := by
  let π := (linearNatural F d).comp a.groupEquiv.toMonoidHom
  let b : ActionEquiv π (linearNatural F d) := ⟨a.groupEquiv,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  let : IsIrreducible π := ExtensionConsequences.irreducible_of_equiv b
    (ExtensionConsequences.linearNatural_irreducible F hd)
  let := hN
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  obtain ⟨v,hv⟩ := exists_ne (0 : N.toSubmodule)
  have hne : a.linearEquiv v.val ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact a.linearEquiv.injective (hz.trans a.linearEquiv.map_zero.symm)
  obtain ⟨i,hi⟩ : ∃ i : Fin r, a.linearEquiv v.val i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  let p : N.toRepresentation.IntertwiningMap π :=
    ((LinearMap.proj i).comp (a.linearEquiv.toLinearMap.comp N.toSubmodule.subtype)).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      exact congrFun (a.intertwines g v.val) i)
  have hp : p ≠ 0 := by
    intro he
    exact hi (congrArg (fun q : N.toRepresentation.IntertwiningMap π => q v) he)
  exact ⟨p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hp)⟩

private theorem irrPlus_irreducible_of_fixed_bot (C : Subgroup G)
    (hz : fixedSpace ρ C = ⊥) (I : Submodule (ZMod 2) V)
    (hs : C ≤ subspaceStabilizer ρ I) (hI : IsIrrPlus ρ C I) :
    IsIrreducible (invariantSubspace ρ C I hs).toRepresentation := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mpr
  refine ⟨fun he => hI.ne_bot ρ (congrArg Subrepresentation.toSubmodule he), ?_⟩
  intro J hJ
  have hstab : C ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    intro c hc v hv
    exact J.apply_mem_toSubmodule ⟨c,hc⟩ hv
  rcases hI.eq_or_le_fixedSpace ρ hstab hJ.le with he | he
  · exact (hJ.ne (Subrepresentation.toSubmodule_injective he)).elim
  · apply Subrepresentation.toSubmodule_injective
    exact bot_unique (he.trans_eq hz)

private def quotientImageEquivOfFixedBot (C : Subgroup G)
    (hz : fixedSpace ρ C = ⊥) (I : Submodule (ZMod 2) V)
    (hs : C ≤ subspaceStabilizer ρ I) :
    (invariantSubspace ρ C I hs).toRepresentation.Equiv
      (Homogeneous.quotientImage ρ C I hs).toRepresentation := by
  let f : I →ₗ[ZMod 2] I.map (fixedSpace ρ C).mkQ :=
    (((fixedSpace ρ C).mkQ).comp I.subtype).codRestrict _ (fun v => ⟨v, v.property, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      apply Subtype.ext
      have hm : v.val - w.val ∈ fixedSpace ρ C := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        change (fixedSpace ρ C).mkQ (v.val - w.val) = 0
        rw [map_sub, show (fixedSpace ρ C).mkQ v.val = (fixedSpace ρ C).mkQ w.val from
          congrArg Subtype.val he, sub_self]
      rw [hz] at hm
      exact sub_eq_zero.mp hm
    · rintro ⟨q, v, hv, rfl⟩
      exact ⟨⟨v,hv⟩, rfl⟩
  exact .mk (LinearEquiv.ofBijective f hf) (by intro g; apply LinearMap.ext; intro v; rfl)

/-- A normalizing two-group fixes an actual natural submodule of a repeated action. -/
theorem repeated_natural_stable_submodule [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (C T : Subgroup G) [C.Normal] [Group.IsPerfect C]
    (hC : C ≠ ⊥) (hT : IsPGroup 2 T) (F : BinaryField) {d r : ℕ} (hd : 2 ≤ d)
    (hn : IsRepeatedLinearNatural (ρ.comp C.subtype) F d r) :
    ∃ I : Subrepresentation (ρ.comp C.subtype), IsLinearNatural I.toRepresentation F d ∧
      T ≤ subspaceStabilizer ρ I.toSubmodule := by
  obtain ⟨a⟩ := hn
  have hz : fixedSpace ρ C = ⊥ := ExtensionConsequences.invariants_of_equiv a
    (ExtensionConsequences.repeated_invariants r (ExtensionConsequences.linearNatural_invariants F hd))
  obtain ⟨J,hJ⟩ := Homogeneous.exists_isIrrPlusWith_of_faithful ρ hf C T hC le_normalizer_of_normal hT
  let I := invariantSubspace ρ C J hJ.invariant
  have hI := irrPlus_irreducible_of_fixed_bot ρ C hz J hJ.invariant hJ.isIrrPlus
  obtain ⟨eI⟩ := repeated_natural_submodule_equiv (ρ.comp C.subtype) F hd a I hI
  refine ⟨I,⟨⟨a.groupEquiv,eI.toLinearEquiv,?_⟩⟩,?_⟩
  · intro g v
    exact LinearMap.congr_fun (eI.isIntertwining' g) v
  · intro t ht
    apply (subspace_map_eq_iff ρ J t).mp
    apply hJ.eq_of_isomorphic_conjugate ρ ⟨t,ht⟩
    have hK := hJ.isIrrPlus.map_normalizer ρ (hJ.normalizes ht)
    let N := invariantSubspace ρ C (J.map (ρ t)) hK.choose
    have hiN := irrPlus_irreducible_of_fixed_bot ρ C hz (J.map (ρ t)) hK.choose hK
    obtain ⟨eN⟩ := repeated_natural_submodule_equiv (ρ.comp C.subtype) F hd a N hiN
    let ei := quotientImageEquivOfFixedBot ρ C hz J hJ.invariant
    let en := quotientImageEquivOfFixedBot ρ C hz (J.map (ρ t)) hK.choose
    let e := ei.symm.trans (eI.trans (eN.symm.trans en))
    exact ⟨e.toLinearEquiv,fun g v => LinearMap.congr_fun (e.isIntertwining' g) v⟩

/-- Original offender generation and repeated binary coordinates force G=L. -/
theorem whole_of_repeated_binary_source [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    {d r : ℕ} (hd : 2 ≤ d)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two d r) :
    L = ⊤ := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let T : Sylow 2 G := Classical.choice inferInstance
  let H := L ⊔ (T : Subgroup G)
  let C := L.subgroupOf H
  let μ := s.space.toRepresentation
  let δ := μ.comp H.subtype
  let c : C ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv c.symm
  have hfit : generalizedFitting H = C :=
    IrreducibleBranch.local_generalizedFitting L T h.fitting h.twoCore T.isPGroup'
  have hfL : Function.Injective (μ.comp L.subtype) := by
    intro x y hxy
    apply IrreducibleBranch.component_faithful h s
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun hxy v)
  have hfC : Function.Injective (δ.comp C.subtype) := by
    intro x y hxy
    apply c.injective
    exact hfL hxy
  have hfδ : Function.Injective δ := by
    apply IrreducibleBranch.faithful_of_fitting_restriction
    rwa [hfit]
  obtain ⟨a⟩ := hn
  have hnC : IsRepeatedLinearNatural (δ.comp C.subtype) BinaryField.two d r :=
    ⟨⟨c.trans a.groupEquiv,a.linearEquiv,fun g v => a.intertwines (c g) v⟩⟩
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  obtain ⟨I,hI,hsI⟩ := repeated_natural_stable_submodule δ hfδ C ((T : Subgroup G).subgroupOf H)
    ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance) T.isPGroup'.comap_subtype
    BinaryField.two hd hnC
  have hz : center C = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr (c.trans a.groupEquiv)).toEquiv]
    change Nat.card (center SL(d,ZMod 2)) = 1
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega : 0 < d)]
    exact Subgroup.card_bot
  have hc : centralizer (C : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxC : x ∈ C := by
      rw [← hfit]
      exact QuasisimpleSections.centralizer_generalizedFitting_le (hfit.symm ▸ hx)
    have hxc : (⟨x,hxC⟩ : C) ∈ center C := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hx l l.property)
    have he : (⟨x,hxC⟩ : C) = 1 := by
      rw [hz] at hxc
      exact hxc
    exact congrArg Subtype.val he
  have hTC := hsI.trans (binary_natural_stabilizer_le δ C hc I hI)
  have hTL : (T : Subgroup G) ≤ L := by
    intro t ht
    exact hTC (show (⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩ : H) ∈
      (T : Subgroup G).subgroupOf H from ht)
  apply IrreducibleBranch.whole_of_sylow_offenders_le ρ L T h.generated
  unfold generatedBy
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  exact hA.2.trans hTL

/-- The original reducible SL3(2) source action has G=L. -/
theorem binaryThree_reducible_whole [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    (mark : L ≃* SL(3,ZMod 2)) : L = ⊤ := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let s := MovedSection.ofNormal ρ L
  exact whole_of_repeated_binary_source ρ h s (by decide : 2 ≤ 3)
    (binaryThree_source_moved_double ρ hK hsemisimple h36 earlier h hnot s mark)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
