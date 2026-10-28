module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.OmegaCenter
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeActor
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Strict whole-center containment in the SL₃ point-image branch

The full B.5.1 conclusion supplies an actual natural submodule of VK.
In the irreducible row, larger-field H¹ vanishing splits the literal moved
central cover. In the doubled-natural row, a diagonal natural copy suffices.
The other reducible rows have incompatible actor groups. The actual SL₃
isomorphism recovers the original field degree, including central covers.

Every two-subgroup has a nonzero fixed natural vector, and hence fixes its
whole field line. This line embeds in C_VK(R₁) and has zero intersection
with C_VK(Kz). The original nonidentity z belongs to the latter subgroup.
Their direct sum therefore has more than q elements. Characteristic two
identifies C_VK(R₁) with the whole Ω₁Z(R₁), giving strict containment of the
original flag line. This proves the source center step directly in the SL₃
image branch, without an action-order assumption or a supplied splitting.

The chosen-flag theorem constructs FF and inner radical placement from the
original inputs. LinearThreeOmegaComparison uses strict containment in the
literal 11.1.5 alternative and applies the proved normalizer-contained equality.
The Sp₄ and G₂ point-image center calculations remain with this comparison
owner. Earlier-source discharge remains with qt-d-1222-shadow-components.
Source: Aschbacher–Smith 11.4.2, printed p.777, B.5.1 and I.1.6.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open ChapterB.QuasisimpleSource

private theorem linearThree_submodule_of_source
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (C : Subgroup A)
    (d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (F : BinaryField) (hF : 1 < F.degree) (m : C ≃* SL(3,F.Carrier)) :
    ∃ (K : BinaryField) (e : C ≃* SL(3,K.Carrier))
      (i : (Fin 3 → K.Carrier) →ₗ[ZMod 2] W),
      K.degree = F.degree ∧ Function.Injective i ∧
      ∀ (g : C) v, i (linearNatural K 3 (e g) v) = ρ g (i v) := by
  cases d.clause_one with
  | irreducible hi hfaith hiri hc hext =>
    obtain ⟨K,⟨a⟩⟩ := SourceCompletion.linearThree_natural_of_irreducible_source
      d.sectionData.action hc F hF m
    have hKF := SourceCompletion.linearThree_degree_eq K F (a.groupEquiv.symm.trans m)
    have hsplit := ExtensionConsequences.linearThree_large_isCompl d.sectionData hi K
      (hKF.symm ▸ hF) a
    let p := d.sectionData.coverProjection a
    have hp : Function.Injective p := by
      apply (LinearMap.ker_eq_bot).mp
      apply bot_unique
      intro w hw
      have hz : d.sectionData.central.toSubmodule.mkQ w = 0 := by
        apply a.linearEquiv.injective
        exact hw.trans a.linearEquiv.map_zero.symm
      have hc := (Submodule.Quotient.mk_eq_zero _).mp hz
      rw [d.sectionData.central_eq] at hc
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp hsplit.1) w w.property
        (fun g => congrArg Subtype.val (hc g))
    let a₀ := LinearEquiv.ofBijective p.toLinearMap
      ⟨hp,(d.sectionData.coverProjection_isCover hi a).1⟩
    let i := d.sectionData.space.toSubmodule.subtype.comp a₀.symm.toLinearMap
    refine ⟨K,a.groupEquiv,i,hKF,
      d.sectionData.space.toSubmodule.subtype_injective.comp a₀.symm.injective,?_⟩
    intro g v
    have hh : a₀.symm (linearNatural K 3 (a.groupEquiv g) v) =
        d.sectionData.space.toRepresentation g (a₀.symm v) := by
      apply a₀.injective
      rw [a₀.apply_symm_apply]
      have he := LinearMap.congr_fun (p.isIntertwining' (a.groupEquiv g)) (a₀.symm v)
      change a₀ (d.sectionData.space.toRepresentation (a.groupEquiv.symm (a.groupEquiv g))
        (a₀.symm v)) = _ at he
      rw [a.groupEquiv.symm_apply_apply] at he
      exact (he.trans (congrArg (linearNatural K 3 (a.groupEquiv g))
        (a₀.apply_symm_apply v))).symm
    exact congrArg Subtype.val hh
  | doubleThree K hwhole a hoff hratio =>
    let j : (Fin 3 → K.Carrier) →ₗ[ZMod 2] (Fin 2 → Fin 3 → K.Carrier) :=
      LinearMap.pi fun _ => LinearMap.id
    have hj : Function.Injective j := by
      intro v w hvw
      exact congrFun hvw 0
    let i := d.sectionData.space.toSubmodule.subtype.comp (a.linearEquiv.symm.toLinearMap.comp j)
    refine ⟨K,a.groupEquiv,i,
      SourceCompletion.linearThree_degree_eq K F (a.groupEquiv.symm.trans m),
      d.sectionData.space.toSubmodule.subtype_injective.comp (a.linearEquiv.symm.injective.comp hj),?_⟩
    intro g v
    have hh : a.linearEquiv.symm (j (linearNatural K 3 (a.groupEquiv g) v)) =
        d.sectionData.space.toRepresentation g (a.linearEquiv.symm (j v)) := by
      apply a.linearEquiv.injective
      rw [a.linearEquiv.apply_symm_apply]
      change _ = a.linearEquiv ((d.sectionData.space.toRepresentation.comp C.subtype) g _)
      rw [a.intertwines,a.linearEquiv.apply_symm_apply]
      rfl
    exact congrArg Subtype.val hh
  | naturalDual n hn _ a =>
    exact (SourceCompletion.no_linearThree_binary_equiv F hn
      (m.symm.trans a.some.groupEquiv)).elim
  | repeatedNatural n r hn _ _ _ a =>
    exact (SourceCompletion.no_linearThree_binary_equiv F hn
      (m.symm.trans a.some.groupEquiv)).elim


private theorem linearThree_fixed_card_lt
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]
    (ρ : Representation (ZMod 2) A W) (C R : Subgroup A) (hRC : R ≤ C)
    (hR : IsPGroup 2 R) (hc : fixedSpace ρ C ≠ ⊥)
    (F : BinaryField) (e : C ≃* SL(3,F.Carrier))
    (i : (Fin 3 → F.Carrier) →ₗ[ZMod 2] W) (hi : Function.Injective i)
    (he : ∀ (g : C) v, i (linearNatural F 3 (e g) v) = ρ g (i v)) :
    Nat.card F.Carrier < Nat.card (fixedSpace ρ R) := by
  let S := (R.subgroupOf C).map e.toMonoidHom
  obtain ⟨v,_,hv,hvf⟩ := PermutedSupports.exists_nonzero_fixed (linearNatural F 3) S
    (hR.comap_subtype.map _) ⊤ top_ne_bot
    (le_subspaceStabilizer _ ⊤ (fun _ _ _ _ => Submodule.mem_top))
  have hscalar (t : F.Carrier) : i (t • v) ∈ fixedSpace ρ R := by
    intro r
    let g : C := ⟨r,hRC r.property⟩
    have hm : e g ∈ S := mem_map_of_mem _ r.property
    have hf : linearNatural F 3 (e g) v = v := hvf ⟨e g,hm⟩
    change ρ g (i (t • v)) = i (t • v)
    rw [←he]
    apply congrArg i
    change specialLinearNatural 3 (e g) (t • v) = t • v
    rw [map_smul]
    exact congrArg (fun w => t • w) hf
  let φ : F.Carrier × fixedSpace ρ C → fixedSpace ρ R := fun a =>
    ⟨i (a.1 • v) + a.2, (fixedSpace ρ R).add_mem (hscalar a.1)
      (fun r => a.2.property ⟨r,hRC r.property⟩)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have hh : i (a.1 • v) + a.2.val = i (b.1 • v) + b.2.val := congrArg Subtype.val hab
    have hd : i ((a.1-b.1) • v) = b.2.val-a.2.val := by
      rw [sub_smul,map_sub]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using hh)
    have hfix : (a.1-b.1) • v ∈ Representation.OneCohomology.fixed
        (specialLinearNatural (k := F.Carrier) 3) := by
      intro g
      apply hi
      change i (linearNatural F 3 g ((a.1-b.1) • v)) = _
      rw [←e.apply_symm_apply g,he,hd,map_sub]
      exact congrArg₂ (fun x y : W => x-y) (b.2.property (e.symm g)) (a.2.property (e.symm g))
    have hz : (a.1-b.1) • v = 0 := by
      simpa only [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3),
        Submodule.mem_bot] using hfix
    have ht : a.1 = b.1 := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)
    apply Prod.ext ht
    apply Subtype.ext
    rw [ht] at hh
    exact add_left_cancel hh
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod] at hcard
  let : Nontrivial (fixedSpace ρ C) := Submodule.nontrivial_iff_ne_bot.mpr hc
  have htwo : 1 < Nat.card (fixedSpace ρ C) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hpos : 0 < Nat.card F.Carrier := Nat.card_pos
  nlinarith

open Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The original nonidentity point survives in the component-fixed space
of the actual action quotient. -/
theorem component_fixedSpace_ne_bot
    (h : EarlierGeometry E) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    fixedSpace (action E) (componentImage E) ≠ ⊥ := by
  obtain ⟨w,hw,hwz⟩ := line_le_module E hstar hcent h.point_mem
  change (w : G) = E.z at hwz
  let v : Additive (moduleSubgroup E) := Additive.ofMul ⟨w,hw⟩
  have hv : v ∈ fixedSpace (action E) (componentImage E) := by
    apply (AlternatingSeven.mem_fixedSpace_image_iff E E.Kz le_sup_left v).mpr
    intro k hk
    change k * (w : G) = (w : G) * k
    rw [hwz]
    exact mem_centralizer_singleton_iff.mp (h.point_component.1 hk)
  intro he
  have hz : v = 0 := he.le hv
  have hh := congrArg (fun u : Additive (moduleSubgroup E) => ((u.toMul : localGroup E) : G)) hz
  exact h.point_ne_one (hwz.symm.trans hh)

/-- The fixed-space computation is on the whole omega-center, with the
original ambient subgroup and quotient action retained. -/
theorem radical_fixedSpace_card_le_omega
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G)) :
    Nat.card (fixedSpace (action E) ((radical E).map (projection E))) ≤
      Nat.card (radicalOmega E) := by
  let φ : fixedSpace (action E) ((radical E).map (projection E)) → radicalOmega E :=
    fun v => ⟨((v.val.toMul : localGroup E) : G), by
      rw [radicalOmega_eq_module_centralizer E hstar]
      refine ⟨mem_map_of_mem _ v.val.toMul.property,?_⟩
      exact (AlternatingSeven.mem_fixedSpace_image_iff E E.R₁
        ((radical_le_sylow E).trans le_sup_right) v.val).mp v.property⟩
  apply Nat.card_le_card_of_injective φ
  intro v w hvw
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : radicalOmega E => (u : G)) hvw

/-- In the SL₃ image row, B.5.1 supplies an embedded natural module,
including the doubled row. Its radical-fixed field line and the original
component-fixed point force the whole omega-center to have order greater
than the original field. No splitting or representation premise is assumed. -/
theorem linearThree_field_lt_radicalOmega
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E))
    (hinner : (radical E).map (projection E) ≤ componentImage E)
    (hsl : Source.IsSL (componentImage E) 3 (2^E.input.field.degree)) :
    2^E.input.field.degree < Nat.card (radicalOmega E) := by
  obtain ⟨hC,⟨d⟩⟩ := source_classification E h hf hne hstar hcent hff
  obtain ⟨F,inst,fin,hF,⟨m⟩⟩ := hsl
  let : Field F := inst
  let : Finite F := fin
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let F₀ : BinaryField := {
    Carrier := F
    degree := E.input.field.degree
    degree_pos := E.input.field.degree_pos
    card_eq := hF }
  let m₀ : offenderComponent E ≃* SL(3,F₀.Carrier) :=
    (subgroupOfEquivOfLe hC).trans m
  obtain ⟨K,e,i,hKF,hi,he⟩ := linearThree_submodule_of_source
    (offenderAction E) (offenderComponent E) d F₀ E.input.nonbinary m₀
  let R := ((radical E).map (projection E)).subgroupOf (offenderGroup E)
  have hRC : R ≤ offenderComponent E := comap_mono hinner
  have hR : IsPGroup 2 R :=
    (((isPGroup_pCoreIn 2 (E.L₁ ⊔ (T : Subgroup G))).comap_subtype).map (projection E)).comap_subtype
  have hfix : fixedSpace (offenderAction E) (offenderComponent E) ≠ ⊥ := by
    rw [offenderComponent,offenderAction,fixedSpace_comp_map,map_subgroupOf_eq_of_le hC]
    exact component_fixedSpace_ne_bot E h hstar hcent
  have hh := linearThree_fixed_card_lt (offenderAction E) (offenderComponent E) R hRC hR hfix K e i hi he
  have hKcard : Nat.card K.Carrier = 2^E.input.field.degree := by
    rw [K.card_eq,hKF]
  rw [hKcard] at hh
  have hRf : fixedSpace (offenderAction E) R =
      fixedSpace (action E) ((radical E).map (projection E)) := by
    rw [offenderAction,fixedSpace_comp_map,map_subgroupOf_eq_of_le (hinner.trans hC)]
  rw [hRf] at hh
  exact hh.trans_le (radical_fixedSpace_card_le_omega E hstar)

variable {E}

/-- The actual chosen-flag SL₃ image has strict omega-center containment;
FF, natural submodule selection and inner radical placement are internal. -/
theorem ofFlag_linearThree_line_lt_radicalOmega
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e₁ : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hsl : Source.IsSL (componentImage (ofFlag S f X z H)) 3 (2^S.field.degree)) :
    (ofFlag S f X z H).V₁ < radicalOmega (ofFlag S f X z H) := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  have hi := rankTwo_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e₁ (.inl hsl)
  have hc := linearThree_field_lt_radicalOmega (ofFlag S f X z H)
    h hf hne hstar hcent hff hi hsl
  apply lt_of_le_of_ne (line_le_radicalOmega _ hstar hcent)
  intro he
  rw [←he,ofFlag_line_card S f X z H hf] at hc
  exact lt_irrefl _ hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
