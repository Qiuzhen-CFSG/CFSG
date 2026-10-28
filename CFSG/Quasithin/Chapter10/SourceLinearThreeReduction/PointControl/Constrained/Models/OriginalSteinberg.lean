module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalSemisimple
public import Theory.Representation.SL5ExteriorSquare.SmallCorank
public import Theory.Representation.BinaryConjugationSection.SmallRepeated

/-!
# Excluding large irreducible original moved modules

The exclusion first applies to any irreducible subsection of the original
moved subgroup contained in the literal reduced orbit VI. Preparation supplies
full-module Thompson fixedness. Apply the complete binary moved-action
alternatives on VI; the original irreducible-cover theorem then follows by
its proved full moved-span containment. Natural and orthogonal rows
are too small for an eight-dimensional submodule. In repeated-natural and
natural–dual rows, each coordinate projection from an irreducible submodule
of dimension at least eight vanishes, since every factor has dimension at
most five.

For the ten-dimensional exterior row, the original containing image is the
whole action quotient. Its exterior-square coordinates identify every element
fixing at least eight dimensions with the identity: the small-corank theorem
makes it an involution, and both nonidentity involution classes move at least
three dimensions. Thus the Thompson subgroup fixes VI, contradicting its
proved movement. The original point, action kernel and full/local module
comparisons are retained throughout.

In particular the original Steinberg marking is impossible. Together with
OriginalSemisimple, this excludes the entire original binary branch below
dimension nine. Source applies this to the literal point-control contract;
larger binary modules and the Suzuki marking remain with this owner.

Source: Aschbacher–Smith H.6.1, B.5.1 and 10.2.9, printed pp.386,99–103,
751–753; the intrinsic exterior involution ranks also occur in 12.5.5,
printed p.819. No later generation or small-offender result is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem orbitSection (c : Context D t v I)
    {Q X : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) Q X) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ _E : ActionEquiv ((action (internalModule D v I)).comp A.subtype) σ,
      ∃ φ : I →* Q, Nonempty (BinaryConjugationSection I (orbitModule D v I) ⊥ (σ.comp φ)) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let R := orbitModule D v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := K.map (actionMk U)
  dsimp only
  intro E
  let f : I →* A := ((actionMk U).subgroupMap K).comp
    (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm.toMonoidHom
  let φ := E.groupEquiv.toMonoidHom.comp f
  let j : R ≃* U := (subgroupOfEquivOfLe c.orbit_le_join).symm
  refine ⟨φ,⟨{
    section_le := c.orbit_le_component
    kernel_le := bot_le
    normalized := le_normalizer_conjugateSpanBy _ _
    coordinates := {
      toFun w := Multiplicative.ofAdd (E.linearEquiv (Additive.ofMul (j w)))
      map_one' := by change E.linearEquiv (Additive.ofMul (j 1)) = 0; rw [map_one]; exact E.linearEquiv.map_zero
      map_mul' x y := by
        change E.linearEquiv (Additive.ofMul (j (x*y))) =
          E.linearEquiv (Additive.ofMul (j x)) + E.linearEquiv (Additive.ofMul (j y))
        rw [map_mul]; exact E.linearEquiv.map_add _ _ }
    onto := by
      intro w
      refine ⟨j.symm (E.linearEquiv.symm w.toAdd).toMul,?_⟩
      change E.linearEquiv (Additive.ofMul (j (j.symm _))) = w.toAdd
      rw [j.apply_symm_apply]
      exact E.linearEquiv.apply_symm_apply _
    kernel_eq := by
      ext w
      change E.linearEquiv (Additive.ofMul (j w)) = 0 ↔ (w:G) = 1
      rw [E.linearEquiv.map_eq_zero_iff]
      change j w = 1 ↔ (w:G) = 1
      rw [j.map_eq_one_iff]
      exact Subtype.val_inj.symm
    equivariant := ?_ }⟩⟩
  intro i w
  have ha : action U (f i).val (Additive.ofMul (j w)) =
      Additive.ofMul (j ⟨(i:G)*w*(i:G)⁻¹,
        (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _ i.property) w).mp w.property⟩) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg H.subtype
      (action_apply U ⟨i,(show I ≤ H from le_sup_left) i.property⟩ (Additive.ofMul (j w)))
  exact (congrArg E.linearEquiv ha.symm).trans (E.intertwines (f i) _)

private theorem small_map_zero
    {Q X Y : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) Y]
    {ρ : Representation (ZMod 2) Q X} [IsIrreducible ρ]
    {σ : Representation (ZMod 2) Q Y} (f : ρ.IntertwiningMap σ)
    (hd : Module.finrank (ZMod 2) Y < Module.finrank (ZMod 2) X) : f = 0 := by
  rcases IsIrreducible.injective_or_eq_zero f with hi | hz
  · have h := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hi
    omega
  · exact hz

private theorem exterior_large_fixed_identity (g : SL5TenDimensional.Group)
    (hd : 8 ≤ Module.finrank (ZMod 2) (SL5ExteriorSquare.fixedSpace g)) : g = 1 := by
  by_contra hn
  have hg := SL5ExteriorSquare.SmallActors.square_eq_one_of_large_fixedSpace g (by omega)
  have h := LinearMap.finrank_range_add_finrank_ker (SL5ExteriorSquare.displacement g)
  change _ + Module.finrank (ZMod 2) (SL5ExteriorSquare.fixedSpace g) = _ at h
  rw [SL5TenDimensional.finrank_exteriorModule_two] at h
  rcases SL5ExteriorSquare.involution_displacement_ranks g hn hg with hh | hh <;> omega

private def wholeMovedEquiv (c : Context D t v I)
    {Q X : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) Q X) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      s.space.toSubmodule = ⊤ →
      ActionEquiv (s.space.toRepresentation.comp (A.subgroupOf N).subtype) σ →
      ActionEquiv ((action (internalModule D v I)).comp A.subtype) σ := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  dsimp only
  intro N hAN s hs E
  let j : Additive U ≃ₗ[ZMod 2] s.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict s.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ he => congrArg Subtype.val he,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  exact {
    groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
    linearEquiv := j.trans E.linearEquiv
    intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }

/-- No irreducible submodule of dimension at least eight lies both in the
original moved subgroup and in the literal reduced orbit VI. -/
theorem Context.no_large_irreducible_moved_subsection (c : Context D t v I)
    (a : ActionFacts c) (B : Subgroup G)
    (hBW : B ≤ ⁅D.fullModule,L⁆) (hspan : B ≤ orbitModule D v I)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] [Nontrivial X]
    {ρ : Representation (ZMod 2) L X} [IsIrreducible ρ]
    (r₀ : BinaryConjugationSection L B ⊥ ρ)
    (hdim : 8 ≤ Module.finrank (ZMod 2) X) : False := by
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBW
  let := c.reduced.normal
  let := c.reduced.elementary
  let H := pointJoin T v I
  let U := internalModule D v I
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  have hAN : A ≤ N := a.classification.2.1
  have hi : Function.Injective r₀.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r₀.kernel_eq,bot_subgroupOf])
  let eW : Additive B ≃ₗ[ZMod 2] X :=
    LinearEquiv.ofBijective (r₀.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hi,r₀.onto⟩
  let j : B →* U :=
    (subgroupOfEquivOfLe c.orbit_le_join).symm.toMonoidHom.comp (inclusion hspan)
  let jl := j.toAdditive.toZModLinearMap 2
  have hji : Function.Injective jl :=
    (subgroupOfEquivOfLe c.orbit_le_join).symm.injective.comp (inclusion_injective hspan)
  have hWU : Module.finrank (ZMod 2) X ≤ Module.finrank (ZMod 2) (Additive U) := by
    rw [←eW.finrank_eq]
    exact LinearMap.finrank_le_finrank_of_injective hji
  obtain ⟨d,hd,h,hs,hm⟩ := c.original_binary_moved_rows a
  cases hm with
  | natural E =>
    let E' := wholeMovedEquiv c _ N hAN h.sectionData hs E
    have he := E'.linearEquiv.finrank_eq
    change Module.finrank (ZMod 2) (Additive U) = Module.finrank (ZMod 2) (Fin d → ZMod 2) at he
    rw [Module.finrank_fin_fun] at he
    omega
  | orthogonal _ _ _ hdim' =>
    have he : Module.finrank (ZMod 2) h.sectionData.space.toSubmodule =
        Module.finrank (ZMod 2) (Additive U) := by rw [hs,finrank_top]
    omega
  | naturalDual hn =>
    let E := wholeMovedEquiv c _ N hAN h.sectionData hs hn.some
    obtain ⟨φ,⟨s⟩⟩ := orbitSection c _ E
    obtain ⟨f,hf⟩ := r₀.exists_injective_intertwiner s c.escaping.strict.le hspan
    let ψ := φ.comp (inclusion c.escaping.strict.le)
    let f₁ : ρ.IntertwiningMap ((linearNatural BinaryField.two d).comp ψ) := {
      toLinearMap := (LinearMap.fst _ _ _).comp f.toLinearMap
      isIntertwining' := fun l => LinearMap.ext fun w =>
        congrArg Prod.fst (LinearMap.congr_fun (f.isIntertwining' l) w) }
    let f₂ : ρ.IntertwiningMap (((linearNatural BinaryField.two d).dual).comp ψ) := {
      toLinearMap := (LinearMap.snd _ _ _).comp f.toLinearMap
      isIntertwining' := fun l => LinearMap.ext fun w =>
        congrArg Prod.snd (LinearMap.congr_fun (f.isIntertwining' l) w) }
    have hz₁ := small_map_zero f₁ (by
      change Module.finrank (ZMod 2) (Fin d → ZMod 2) < _
      rw [Module.finrank_fin_fun]; omega)
    have hz₂ := small_map_zero f₂ (by
      rw [Subspace.dual_finrank_eq]
      change Module.finrank (ZMod 2) (Fin d → ZMod 2) < _
      rw [Module.finrank_fin_fun]; omega)
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    apply hx
    apply hf
    rw [map_zero]
    apply Prod.ext
    · exact congrArg (fun z : ρ.IntertwiningMap _ => z x) hz₁
    · exact congrArg (fun z : ρ.IntertwiningMap _ => z x) hz₂
  | repeatedNatural n _ _ hn =>
    let E := wholeMovedEquiv c _ N hAN h.sectionData hs hn.some
    obtain ⟨φ,⟨s⟩⟩ := orbitSection c _ E
    obtain ⟨f,hf⟩ := r₀.exists_injective_intertwiner s c.escaping.strict.le hspan
    let ψ := φ.comp (inclusion c.escaping.strict.le)
    have hz (i : Fin n) : ∀ x, f x i = 0 := by
      let fᵢ : ρ.IntertwiningMap ((linearNatural BinaryField.two d).comp ψ) := {
        toLinearMap := (LinearMap.proj i).comp f.toLinearMap
        isIntertwining' := fun l => LinearMap.ext fun w =>
          congrFun (LinearMap.congr_fun (f.isIntertwining' l) w) i }
      have hz := small_map_zero fᵢ (by
        change Module.finrank (ZMod 2) (Fin d → ZMod 2) < _
        rw [Module.finrank_fin_fun]; omega)
      exact fun x => congrArg (fun z : ρ.IntertwiningMap _ => z x) hz
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    exact hx (hf (by rw [map_zero]; exact funext fun i => hz i x))
  | exterior hd E hir hten =>
    let eA : A ≃* SL(5,ZMod 2) := (subgroupOfEquivOfLe hAN).symm.trans E
    let f : Representation.Equiv ((action U).comp A.subtype)
        (h.sectionData.space.toRepresentation.comp (A.subgroupOf N).subtype |>.comp
          (subgroupOfEquivOfLe hAN).symm.toMonoidHom) := {
      toLinearEquiv := LinearEquiv.ofBijective
        ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict h.sectionData.space.toSubmodule
          (fun _ => hs.symm ▸ Submodule.mem_top))
        ⟨fun _ _ he => congrArg Subtype.val he,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
      isIntertwining' := fun _ => rfl }
    have hi' : IsIrreducible ((action U).comp A.subtype) :=
      ExtensionConsequences.irreducible_of_equiv {
        groupEquiv := (subgroupOfEquivOfLe hAN).symm
        linearEquiv := f.toLinearEquiv
        intertwines := fun g w => LinearMap.congr_fun (f.isIntertwining' g) w } hir
    have hten' : Module.finrank (ZMod 2) (Additive U) = 10 := f.toLinearEquiv.finrank_eq.trans hten
    let := hi'
    let K := I.subgroupOf H
    let : K.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
    let : A.Normal := Normal.map inferInstance (actionMk U) (QuotientGroup.mk'_surjective _)
    have hAt : A = ⊤ := BinaryLinearNormalActors.normal_ten_dimensional_eq_top
      (action U) (action_faithful U) A eA hten'
    obtain ⟨e,F,_,hF⟩ := SL5ExteriorSquare.square_coordinates_of_finrank_ten
      ((action U).comp A.subtype) eA hten'
    have hquiet := c.full_thompson_fixed_of_three (c.three_dvd_of_prepared a.prepared)
    apply a.prepared.thompson_moves
    intro z hz w hw
    have hJS : Stellmacher.elementaryAbelianMaxJ (pointSylow T v) ≤ pointSylow T v :=
      sSup_le fun _ hB => hB.1
    have hzH : z ∈ H := (show pointSylow T v ≤ H from le_sup_right)
      (hJS hz)
    let zH : H := ⟨z,hzH⟩
    let zA : A := ⟨actionMk U zH,hAt.symm ▸ mem_top _⟩
    have hfix (u : Additive B) :
        action U (zA : ActionQuotient U) (jl u) = jl u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg H.subtype (action_apply U zH (jl u))
      rw [a.prepared.thompson_eq] at hz
      have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
        (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
          D.maximalLocal_normalizes_fullModule)
      exact ha.trans (by
        change z * (u.toMul : G) * z⁻¹ = (u.toMul : G)
        rw [←hquiet hz u.toMul (hWV (hBW u.toMul.property)),mul_inv_cancel_right])
    let k := F.toLinearMap.comp jl
    have hk : ∀ u, k u ∈ SL5ExteriorSquare.fixedSpace (e zA) := by
      intro u
      apply (SL5ExteriorSquare.mem_fixedSpace _ _).mpr
      exact (hF zA (jl u)).symm.trans (congrArg F (hfix u))
    let k' := k.codRestrict (SL5ExteriorSquare.fixedSpace (e zA)) hk
    have hki : Function.Injective k' := fun x y he =>
      hji (F.injective (congrArg Subtype.val he))
    have he := exterior_large_fixed_identity (e zA) (by
      have hh := LinearMap.finrank_le_finrank_of_injective hki
      rw [eW.finrank_eq] at hh
      omega)
    have hzq : actionMk U zH = 1 := congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
    have hzk : zH ∈ centralizer (U : Set H) := (QuotientGroup.eq_one_iff zH).mp hzq
    exact congrArg H.subtype (hzk ⟨w,c.orbit_le_join hw⟩ hw)

/-- An original irreducible moved cover of dimension at least eight is incompatible
with every binary containing row on the literal reduced orbit. -/
theorem Context.no_large_irreducible_original_cover (c : Context D t v I)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] [Nontrivial X]
    {ρ : Representation (ZMod 2) L X} [IsIrreducible ρ]
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ)
    (hdim : 8 ≤ Module.finrank (ZMod 2) X) : False :=
  c.no_large_irreducible_moved_subsection (c.actionFacts_of_irreducible_cover r)
    ⁅D.fullModule,L⁆ le_rfl (c.moved_le_of_irreducible_cover r)
    (c.moved_fixed_eq_bot ▸ r) hdim

/-- The literal Steinberg marking is excluded without any later generation bound. -/
theorem Context.no_original_steinberg (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.S.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsIrreducible (BinaryLinearThree.S.comp q) :=
    (irreducible_comp_surjective_iff q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  let : Nontrivial BinaryLinearThree.Steinberg := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) BinaryLinearThree.Steinberg by
      rw [BinaryLinearThree.finrank_steinberg]; decide)
  exact c.no_large_irreducible_original_cover s (by
    rw [BinaryLinearThree.finrank_steinberg])

/-- The entire original binary branch below dimension nine is impossible. -/
theorem Context.no_original_binary_below_nine (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (hd : letI := source_original_full_moved_elementary D
      Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) < 9) : False :=
  c.no_original_steinberg e (c.original_small_binary_steinberg e hd).some

/-- Every remaining original binary moved subgroup has dimension at least nine. -/
theorem Context.original_binary_finrank_ge_nine (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    letI := source_original_full_moved_elementary D
    9 ≤ Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := by
  let := source_original_full_moved_elementary D
  by_contra hn
  exact c.no_original_binary_below_nine e (by omega)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
