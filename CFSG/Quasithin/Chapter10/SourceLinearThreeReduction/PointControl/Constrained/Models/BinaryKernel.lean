module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryCover
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.CoveringPGroupDescent

/-!
# The binary containing action and its original two-core kernel

A surjection onto SL₄(2) or SL₅(2) forces cubic rank at least two in the
original C-component: a group of cubic rank at most one has cyclic Sylow
three-subgroups, as do its quotients. The SQTK structure theorem therefore
makes the original two-core quotient quasisimple. The binary Schur multipliers
are two-primary, so the induced map on that quotient is injective. Since the
reduced orbit action kills the component two-core, this identifies its exact
kernel and retains the original quotient map.

The same marking identifies I with the prime-to-three residual of C_G(v).
In the original natural-three row, an opposite cubic then belongs to I and
fixes the original eight-subgroup. If the orbit has order sixteen, counting
fixed points modulo three forces that cubic to act trivially, contradicting
the two-core kernel. This excludes the degree-four natural containing section.
The degree-five natural and ten-dimensional sections supply the complete
linear-five data and are excluded by the proved parabolic endgame.

These are applications to the literal orbit and action, with no kernel,
whole-orbit dimension or preparation callback in the section exclusions.
General quiet preparation, original-row recognition, the retained four-natural
copy row and the other containing actions remain with the final source owner
qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith, 10.2.9, printed pp.751--753, and I.1.3,
printed p.407, for the Schur-multiplier calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open PerfectCentralCovering

private theorem binary_kernel {H : Type*} [Group H] [Finite H]
    [IsQuasisimple (H ⧸ pCore 2 H)] {d : ℕ} (hd : d = 4 ∨ d = 5)
    (f : H →* SL(d,ZMod 2)) (hf : Function.Surjective f)
    (hk : pCore 2 H ≤ f.ker) : f.ker = pCore 2 H := by
  let Q := H ⧸ pCore 2 H
  let e := (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d)).symm
  let g := e.toMonoidHom.comp (QuotientGroup.lift (pCore 2 H) f hk)
  have hg : Function.Surjective g := e.surjective.comp
    (QuotientGroup.lift_surjective_of_surjective _ f hf _)
  let : IsSimpleGroup PSL(d,ZMod 2) := Atlas.psl_simple_high_rank d (by omega)
  let : IsQuasisimple PSL(d,ZMod 2) := IsQuasisimple.of_surjective g hg
  let c : Covering Q PSL(d,ZMod 2) := ⟨g,hg⟩
  have hu : IsPGroup 2 (universalProjection PSL(d,ZMod 2)).ker := by
    rcases hd with rfl | rfl
    · let a := Matrix.PSL4Two.schurMultiplierEquivTwo (ZMod 2) (by simp)
        (MulEquiv.refl PSL(4,ZMod 2))
      apply IsPGroup.of_card (n := 1)
      exact (Nat.card_congr a.toEquiv).trans (by simp)
    · rw [Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot]
      exact IsPGroup.of_card (n := 0) (by simp)
  have hi : Function.Injective g :=
    (universalQuasisimpleCover_isUniversal PSL(d,ZMod 2)).injective_of_pGroup_kernel
      hu c (pCore_quotient_pCore_eq_bot 2)
  apply le_antisymm _ hk
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change e (f x) = g 1
  rw [show f x = 1 from hx,map_one,map_one]

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- A binary containing actor forces the original component head to be quasisimple. -/
theorem Context.component_head_quasisimple_of_binary_actor (c : Context D t v I)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) :
    IsQuasisimple (I ⧸ pCore 2 I) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let f := e.toMonoidHom.comp ((actionMk (internalModule D v I)).subgroupMap K)
  have hf : Function.Surjective f := e.surjective.comp
    ((actionMk (internalModule D v I)).subgroupMap_surjective K)
  have hr : 2 ≤ primeRank 3 K := by
    by_contra hn
    have hle : primeRank 3 K ≤ 1 := by omega
    let P : Sylow 3 K := Classical.choice inferInstance
    have hu := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hle) f hf
    have hl := BinaryLinear.SmallCubicRank.four_or_five hd
    omega
  have hK : K.IsCComponent := c.escaping.component.subgroupOf_of_le
    le_sup_left (sup_le c.escaping.le_centralizer inf_le_right)
  let := ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank c.join_sqtk hK hr
  let a : K ≃* I := subgroupOfEquivOfLe le_sup_left
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))

/-- The literal component action has kernel exactly its intrinsic two-core. -/
theorem Context.action_kernel_eq_twoCore_of_binary_actor (c : Context D t v I)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) :
    letI := c.reduced.normal
    ((actionMk (internalModule D v I)).subgroupMap
      (I.subgroupOf (pointJoin T v I))).ker =
        pCore 2 (I.subgroupOf (pointJoin T v I)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let U := internalModule D v I
  let := c.reduced.normal
  let f := (actionMk U).subgroupMap K
  let a : K ≃* I := subgroupOfEquivOfLe le_sup_left
  let := c.component_head_quasisimple_of_binary_actor hd e
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  have hK : K.IsCComponent := c.escaping.component.subgroupOf_of_le
    le_sup_left (sup_le c.escaping.le_centralizer inf_le_right)
  have hk : pCore 2 K ≤ f.ker := by
    intro k hk
    have hcore : (k : H) ∈ pCore 2 H :=
      pCoreIn_le_of_subnormal 2 hK.subnormal (mem_map_of_mem K.subtype hk)
    have hc : (k : H) ∈ centralizer (U : Set H) :=
      le_centralizer_iff.mp c.reduced.le_centralizer_pCore hcore
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hc)
  have he := binary_kernel hd (e.toMonoidHom.comp f)
    (e.surjective.comp ((actionMk U).subgroupMap_surjective K)) (by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact hk)
  rwa [MonoidHom.ker_comp_of_injective _ _ e.injective] at he

/-- The quotient marking is induced by the original action map. -/
def Context.binaryActorQuotient (c : Context D t v I)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) : (I ⧸ pCore 2 I) ≃* SL(d,ZMod 2) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let f := (actionMk (internalModule D v I)).subgroupMap K
  let a : I ≃* K := (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (((QuotientGroup.quotientMulEquivOfEq
      (c.action_kernel_eq_twoCore_of_binary_actor hd e).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f
          ((actionMk (internalModule D v I)).subgroupMap_surjective K))).trans e)

/-- The actual binary actor identifies I with the cubic residual of the point centralizer. -/
theorem Context.component_eq_point_residual_of_binary_actor (c : Context D t v I)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) :
    (primeToResidual 3 (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype = I := by
  let X := centralizer ({v} : Set G)
  let K := I.subgroupOf X
  let E : (K ⧸ pCore 2 K) ≃* SL(d,ZMod 2) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe c.escaping.le_centralizer)
      (pCore_map_iso 2 _)).trans (c.binaryActorQuotient hd e)
  let := c.component_head_quasisimple_of_binary_actor hd e
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe c.escaping.le_centralizer)
      (pCore_map_iso 2 _)).symm
  have hf := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv E
    (Theory.SpecificGroups.BinaryComponentResidual.linear hd)
  have hX := D.simpleQTKE.involution_centralizer_sqtk c.point_involution
  have he := c.escaping.component.eq_primeToResidual_three_of_rank_outer_two hf.1 hf.2.1
    (hX.stronglyQuasithin 3 (by decide) (by decide)) hf.2.2
  rw [←he,map_subgroupOf_eq_of_le c.escaping.le_centralizer]

/-- The ten-dimensional section is impossible on the original natural-three row;
the actual two-core kernel premise is discharged here. -/
theorem Context.no_exterior_five_section_of_natural_three
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : (A.subgroupOf N) ≃* SL(5,ZMod 2)),
      IsIrreducible (s.action.comp (A.subgroupOf N).subtype) →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10 → False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  dsimp only
  intro N hAN s E hi hd
  exact c.no_exterior_five_section_of_natural_three_of_kernel e r
    (c.action_kernel_eq_twoCore_of_binary_actor (Or.inr rfl)
      ((subgroupOfEquivOfLe hAN).symm.trans E)) N hAN s E hi hd

/-- The natural-five section supplies the complete terminal data and is impossible. -/
theorem Context.no_natural_five_section_of_natural_three
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : ActionEquiv (s.action.comp (A.subgroupOf N).subtype)
        (linearNatural BinaryField.two 5)), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  dsimp only
  intro N hAN s E
  have hspan := c.moved_le_of_natural_three e r
  obtain ⟨_,f,_⟩ := c.binary_natural_section_full hspan (by decide : 4 ≤ 5) N hAN s E
  let m : LinearFiveData c := {
    quotient := e
    natural := r
    sylow_eq := c.pointSylow_eq_of_natural_three e r
    moved_le := hspan
    actor := f.groupEquiv
    actor_eq_top := c.actor_eq_top_of_binary_natural_section hspan (by decide : 4 ≤ 5) N hAN s E
    kernel_eq := c.action_kernel_eq_twoCore_of_binary_actor (Or.inr rfl) f.groupEquiv
    irreducible := ExtensionConsequences.irreducible_of_equiv f
      (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide))
    dimension := Or.inl (f.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))) }
  exact m.impossible

private theorem cubic_aut_eq_one_of_fixed_eight
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 16)
    (a : MulAut E) (ha : a ^ 3 = 1)
    (hfix : 8 ≤ Nat.card (FixedPoints.subgroup (zpowers a) E)) : a = 1 := by
  let P := zpowers a
  let F := FixedPoints.subgroup P E
  have hp : IsPGroup 3 P := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr ha)
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % 3 = Nat.card F % 3 at hmod
  rw [hE] at hmod
  have hdiv : Nat.card F ∣ 16 := hE ▸ F.card_subgroup_dvd_card
  have hmem := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
  have hdivs : (16 : ℕ).divisors = {1,2,4,8,16} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  change 8 ≤ Nat.card F at hfix
  have hcard : Nat.card F = 16 := by omega
  have htop := F.eq_top_of_card_eq (hcard.trans hE.symm)
  apply MulEquiv.ext
  intro x
  exact (show x ∈ F from htop ▸ mem_top x) ⟨a,mem_zpowers a⟩

/-- A binary-four actor cannot contain the original natural-three row.
The opposite cubic fixes an eight-subgroup of the literal sixteen-element
orbit, forcing it into the two-core action kernel. -/
theorem Context.no_four_dimensional_binary_actor_of_natural_three
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (E : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(4,ZMod 2))
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 4) : False := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let U := internalModule D v I
  let W := ⁅D.fullModule,L⁆
  let := c.reduced.normal
  let := c.reduced.elementary
  have hspan := c.moved_le_of_natural_three e r
  obtain ⟨y,hy3,hyv,_,hyc⟩ := c.exists_opposite_cubic_of_natural_three e r
  have hyI : y ∈ I := by
    rw [←c.component_eq_point_residual_of_binary_actor (Or.inl rfl) E]
    apply mem_map_of_mem (centralizer ({v} : Set G)).subtype (x := ⟨y,hyv⟩)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change y ^ (3 ^ 1) = 1
    simpa only [pow_one,hy3] using pow_orderOf_eq_one y
  let yH : H := ⟨y,(le_sup_left : I ≤ H) hyI⟩
  let a : MulAut U := MulAut.conjNormal yH
  have ha : a ^ 3 = 1 := by
    rw [←map_pow]
    have hy : yH ^ 3 = 1 := Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
    rw [hy,map_one]
  have hU : Nat.card U = 16 := by
    change Nat.card (Additive U) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    rfl
  have hW : Nat.card W = 8 := by
    have hc := r.card_section
    rw [card_bot,mul_one] at hc
    exact hc.trans (by simp)
  let F := FixedPoints.subgroup (zpowers a) U
  let j : W → F := fun w =>
    ⟨⟨⟨w,c.orbit_le_join (hspan w.property)⟩,hspan w.property⟩,by
      let wU : U := ⟨⟨w,c.orbit_le_join (hspan w.property)⟩,hspan w.property⟩
      have haw : a wU = wU := by
        apply Subtype.ext
        apply Subtype.ext
        change y * (w : G) * y⁻¹ = w
        rw [←hyc w w.property,mul_inv_cancel_right]
      have hle : zpowers a ≤ MulAction.stabilizer (MulAut U) wU := zpowers_le.mpr haw
      intro b
      exact hle b.property⟩
  have hj : Function.Injective j := by
    intro w z he
    apply Subtype.ext
    exact congrArg (fun x : F => (((x : U) : H) : G)) he
  have hone : a = 1 := cubic_aut_eq_one_of_fixed_eight hU a ha
    (hW ▸ Nat.card_le_card_of_injective j hj)
  have hyC : yH ∈ centralizer (U : Set H) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hone
  let yK : K := ⟨yH,hyI⟩
  have hyker : yK ∈ ((actionMk U).subgroupMap K).ker :=
    Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hyC)
  rw [c.action_kernel_eq_twoCore_of_binary_actor (Or.inl rfl) E] at hyker
  let z : pCore 2 K := ⟨yK,hyker⟩
  have hz3 : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans
    ((Subgroup.orderOf_coe yK).symm.trans ((Subgroup.orderOf_coe yH).symm.trans hy3))
  have hzne : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz3; omega
  have htwo := (pCore_isPGroup (p := 2) (G := K)).dvd_orderOf hzne
  rw [hz3] at htwo
  norm_num at htwo

/-- The whole binary natural containing family is excluded on the marked
original natural-three row, with no action-kernel or whole-orbit premise. -/
theorem Context.no_binary_natural_section_of_natural_three
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {d : ℕ} (hd : d = 4 ∨ d = 5) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : ActionEquiv (s.action.comp (A.subgroupOf N).subtype)
        (linearNatural BinaryField.two d)), False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  dsimp only
  intro N hAN s E
  rcases hd with rfl | rfl
  · obtain ⟨_,f,_⟩ := c.binary_natural_section_full
      (c.moved_le_of_natural_three e r) (by decide : 4 ≤ 4) N hAN s E
    exact c.no_four_dimensional_binary_actor_of_natural_three e r f.groupEquiv
      (f.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2)))
  · exact c.no_natural_five_section_of_natural_three e r N hAN s E

end CFSG.Quasithin.Chapter10.PointControl.Constrained
