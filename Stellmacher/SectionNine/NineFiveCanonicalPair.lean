module

public import Stellmacher.SectionOne.OneSevenGlobalProduct
public import Theory.Representation.FourGroupMatrixCoordinates

namespace Stellmacher.SectionNine

open SectionOne

universe u

public theorem nine_five_canonical_factor_eq_of_support_span
    {Actor Module : Type u} [Group Actor] [Group Module]
    [Finite Actor] [Finite Module] [IsElementaryAbelian 2 Module]
    [MulDistribMulAction Actor Module]
    (hyp : Hypotheses Actor Module) (first second factor : Subgroup Actor)
    (hfirst : IsOneSevenFactor (V := Module) first)
    (hsecond : IsOneSevenFactor (V := Module) second)
    (hfactor : IsOneSevenFactor (V := Module) factor)
    (hspan : commutatorAction first Module ⊔ commutatorAction second Module = ⊤) :
    factor = first ∨ factor = second := by
  by_contra hne
  have hneFirst : factor ≠ first := fun heq => hne (Or.inl heq)
  have hneSecond : factor ≠ second := fun heq => hne (Or.inr heq)
  have hfix : (⊤ : Subgroup Module) ≤ FixedPoints.subgroup factor Module := by
    rw [← hspan]
    exact sup_le
      (oneSevenFactor_commutatorAction_le_fixedPoints hyp factor first hfactor hfirst hneFirst)
      (oneSevenFactor_commutatorAction_le_fixedPoints hyp factor second hfactor hsecond hneSecond)
  have hbot : factor = ⊥ := by
    apply le_bot_iff.mp
    intro element helement
    have hkernel : element ∈ fixingSubgroup Actor (Set.univ : Set Module) := by
      rw [mem_fixingSubgroup_iff]
      intro vector _
      exact ((FixedPoints.mem_subgroup (M := factor) (a := vector)).mp
        (hfix (Subgroup.mem_top vector)))
        ⟨element, helement⟩
    rwa [hyp.action_faithful] at hkernel
  have hcard := RankOneThreeGroupAssembly.isSL2Two_card hfactor.1
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

public theorem nine_five_canonical_pair_of_support_span
    {Actor Module : Type u} [Group Actor] [Group Module]
    [Finite Actor] [Finite Module] [IsElementaryAbelian 2 Module]
    [MulDistribMulAction Actor Module]
    (hyp : Hypotheses Actor Module) (first second : Subgroup Actor)
    (hfirst : IsOneSevenFactor (V := Module) first)
    (hsecond : IsOneSevenFactor (V := Module) second)
    (hne : first ≠ second)
    (hspan : commutatorAction first Module ⊔ commutatorAction second Module = ⊤) :
    first ≤ Subgroup.centralizer (second : Set Actor) ∧
      Disjoint first second ∧ (first ⊔ second).Normal ∧
      (∀ element : Actor,
        (first.conjBy element = first ∧ second.conjBy element = second) ∨
        (first.conjBy element = second ∧ second.conjBy element = first)) ∧
      oneSevenGenerated (G := Actor) (V := Module) = first ⊔ second := by
  classical
  let sylow : Sylow 2 Actor := default
  obtain ⟨hnormal, hproduct, _⟩ := oneSeven_global_product hyp sylow
  have hfirstMem := (mem_oneSevenFactors_iff first).mpr hfirst
  have hsecondMem := (mem_oneSevenFactors_iff second).mpr hsecond
  have hgenerated : oneSevenGenerated (G := Actor) (V := Module) = first ⊔ second := by
    apply le_antisymm
    · apply sSup_le
      intro factor hfactor
      rcases nine_five_canonical_factor_eq_of_support_span hyp first second factor
        hfirst hsecond hfactor hspan with heq | heq
      · rw [heq]
        exact le_sup_left
      · rw [heq]
        exact le_sup_right
    · exact sup_le (le_sSup hfirst) (le_sSup hsecond)
  refine ⟨?_, hproduct.2.2.1 first hfirstMem second hsecondMem hne,
    hgenerated ▸ hnormal, ?_, hgenerated⟩
  · intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    exact (hproduct.2.2.2 first hfirstMem second hsecondMem hne
      element helement other hother).symm
  · intro element
    have hfirstOptions := nine_five_canonical_factor_eq_of_support_span hyp first second
      (first.conjBy element) hfirst hsecond (hfirst.conjBy first element) hspan
    have hsecondOptions := nine_five_canonical_factor_eq_of_support_span hyp first second
      (second.conjBy element) hfirst hsecond (hsecond.conjBy second element) hspan
    have hconjNe : first.conjBy element ≠ second.conjBy element :=
      fun heq => hne (Subgroup.map_injective (MulAut.conj element).injective heq)
    rcases hfirstOptions with hfirstEq | hfirstEq <;>
      rcases hsecondOptions with hsecondEq | hsecondEq
    · exact (hconjNe (hfirstEq.trans hsecondEq.symm)).elim
    · exact Or.inl ⟨hfirstEq, hsecondEq⟩
    · exact Or.inr ⟨hfirstEq, hsecondEq⟩
    · exact (hconjNe (hfirstEq.trans hsecondEq.symm)).elim

private theorem canonical_centralizer_fixes_support
    {Actor Module : Type u} [Group Actor] [Group Module]
    [Finite Actor] [Finite Module] [IsElementaryAbelian 2 Module]
    [MulDistribMulAction Actor Module]
    (hyp : Hypotheses Actor Module) (first second : Subgroup Actor)
    (hfirst : IsOneSevenFactor (V := Module) first)
    (hsecond : IsOneSevenFactor (V := Module) second)
    (hne : first ≠ second)
    (hspan : commutatorAction first Module ⊔ commutatorAction second Module = ⊤)
    (element : Actor)
    (helement : element ∈ Subgroup.centralizer (first : Set Actor))
    (vector : Module) (hvector : vector ∈ commutatorAction first Module) :
    element • vector = vector := by
  let support := commutatorAction first Module
  let other := commutatorAction second Module
  let centralizer := Subgroup.centralizer (first : Set Actor)
  let _ : IsInvariant first Module support :=
    commutatorAction_isInvariant_of_normalizing_actor first first first.le_normalizer
  let _ : IsInvariant centralizer Module support :=
    commutatorAction_isInvariant_of_normalizing_actor centralizer first
      (Subgroup.centralizer_le_normalizer _)
  let _ : IsElementaryAbelian 2 support :=
    RankOneThreeGroupAssembly.isElementaryAbelian_subgroup support
  let representation : first →* MulAut support := MulDistribMulAction.toMulAut first support
  let centralizerRepresentation : centralizer →* MulAut support :=
    MulDistribMulAction.toMulAut centralizer support
  have hinjective : Function.Injective representation := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_bot_iff.mp
    intro point hpoint
    have hsupportFix (value : Module) (hvalue : value ∈ support) :
        (point : Actor) • value = value := by
      exact congrArg Subtype.val
        (MulEquiv.congr_fun (MonoidHom.mem_ker.mp hpoint) ⟨value, hvalue⟩)
    have hotherFix (value : Module) (hvalue : value ∈ other) :
        (point : Actor) • value = value := by
      exact ((FixedPoints.mem_subgroup (M := first) (a := value)).mp
        (oneSevenFactor_commutatorAction_le_fixedPoints hyp first second
          hfirst hsecond hne hvalue)) point
    have hkernel : (point : Actor) ∈ fixingSubgroup Actor (Set.univ : Set Module) := by
      rw [mem_fixingSubgroup_iff]
      intro value _
      have hvalue : value ∈ support ⊔ other := hspan.symm ▸ Subgroup.mem_top value
      let _ : support.Normal := Subgroup.normal_of_isMulCommutative support
      obtain ⟨left, hleft, right, hright, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hvalue
      rw [smul_mul', hsupportFix left hleft, hotherFix right hright]
    rw [hyp.action_faithful] at hkernel
    exact Subtype.ext hkernel
  have hautFaithful : fixingSubgroup (MulAut support) (Set.univ : Set support) = ⊥ := by
    apply le_bot_iff.mp
    intro automorphism hautomorphism
    rw [mem_fixingSubgroup_iff] at hautomorphism
    apply Subgroup.mem_bot.mpr
    ext value
    exact congrArg Subtype.val (hautomorphism value (Set.mem_univ value))
  obtain ⟨coordinates, hcoordinates, _⟩ :=
    FourGroupMatrixCoordinates.faithful_card_four_embedding hautFaithful hfirst.2.2.1
  let matrixRepresentation := coordinates.comp representation
  have hsurjective : Function.Surjective matrixRepresentation := by
    apply ((Nat.bijective_iff_injective_and_card matrixRepresentation).mpr
      ⟨hcoordinates.comp hinjective, ?_⟩).2
    exact (RankOneThreeGroupAssembly.isSL2Two_card hfirst.1).trans
      (RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩).symm
  let centralActor : centralizer := ⟨element, helement⟩
  have hcommute (point : first) :
      Commute (representation point) (centralizerRepresentation centralActor) := by
    ext value
    change (point : Actor) • (element • (value : Module)) =
      element • ((point : Actor) • (value : Module))
    rw [← mul_smul, ← mul_smul,
      Subgroup.mem_centralizer_iff.mp helement point point.property]
  have hcenter : coordinates (centralizerRepresentation centralActor) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro matrix
    obtain ⟨point, rfl⟩ := hsurjective matrix
    exact (hcommute point).map coordinates
  have hidentity : coordinates (centralizerRepresentation centralActor) = 1 := by
    rwa [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two ⟨MulEquiv.refl _⟩] at hcenter
  have htrivial : centralizerRepresentation centralActor = 1 :=
    hcoordinates (hidentity.trans (map_one coordinates).symm)
  exact congrArg Subtype.val (MulEquiv.congr_fun htrivial ⟨vector, hvector⟩)

public theorem nine_five_canonical_pair_centralizer_of_support_span
    {Actor Module : Type u} [Group Actor] [Group Module]
    [Finite Actor] [Finite Module] [IsElementaryAbelian 2 Module]
    [MulDistribMulAction Actor Module]
    (hyp : Hypotheses Actor Module) (first second : Subgroup Actor)
    (hfirst : IsOneSevenFactor (V := Module) first)
    (hsecond : IsOneSevenFactor (V := Module) second)
    (hne : first ≠ second)
    (hspan : commutatorAction first Module ⊔ commutatorAction second Module = ⊤) :
    Subgroup.centralizer ((first ⊔ second : Subgroup Actor) : Set Actor) = ⊥ := by
  apply le_bot_iff.mp
  intro element helement
  have hfirstCent : element ∈ Subgroup.centralizer (first : Set Actor) :=
    Subgroup.centralizer_le (show (first : Set Actor) ⊆ (first ⊔ second : Subgroup Actor)
      from fun _ hmem => Subgroup.mem_sup_left hmem) helement
  have hsecondCent : element ∈ Subgroup.centralizer (second : Set Actor) :=
    Subgroup.centralizer_le (show (second : Set Actor) ⊆ (first ⊔ second : Subgroup Actor)
      from fun _ hmem => Subgroup.mem_sup_right hmem) helement
  have hkernel : element ∈ fixingSubgroup Actor (Set.univ : Set Module) := by
    rw [mem_fixingSubgroup_iff]
    intro vector _
    have hvector : vector ∈ commutatorAction first Module ⊔ commutatorAction second Module :=
      hspan.symm ▸ Subgroup.mem_top vector
    let _ : (commutatorAction first Module).Normal :=
      Subgroup.normal_of_isMulCommutative _
    obtain ⟨left, hleft, right, hright, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hvector
    rw [smul_mul',
      canonical_centralizer_fixes_support hyp first second hfirst hsecond hne hspan
        element hfirstCent left hleft,
      canonical_centralizer_fixes_support hyp second first hsecond hfirst hne.symm
        (by rwa [sup_comm]) element hsecondCent right hright]
  rwa [hyp.action_faithful] at hkernel

public theorem nine_five_two_factors_of_canonical_support
    {Actor Module : Type u} [Group Actor] [Group Module]
    [Finite Actor] [Finite Module] [IsElementaryAbelian 2 Module]
    [MulDistribMulAction Actor Module]
    (hyp : Hypotheses Actor Module) (factor : Subgroup Actor)
    (hfactor : IsOneSevenFactor (V := Module) factor) (conjugator : Actor)
    (hmove : commutatorAction factor Module ≠
      (commutatorAction factor Module).map
        (MulDistribMulAction.toMulAut Actor Module conjugator).toMonoidHom)
    (hspan : commutatorAction factor Module ⊔
      (commutatorAction factor Module).map
        (MulDistribMulAction.toMulAut Actor Module conjugator).toMonoidHom = ⊤) :
    ∃ first second : Subgroup Actor,
      IsSL2Two first ∧ IsSL2Two second ∧
      first ≤ Subgroup.centralizer (second : Set Actor) ∧
      Disjoint first second ∧ (first ⊔ second).Normal ∧
      Subgroup.centralizer ((first ⊔ second : Subgroup Actor) : Set Actor) = ⊥ ∧
      (∀ element : Actor,
        (first.conjBy element = first ∧ second.conjBy element = second) ∨
        (first.conjBy element = second ∧ second.conjBy element = first)) ∧
      (∃ element : Actor, first.conjBy element = second) := by
  rw [RankOneThreeGroupAssembly.commutatorAction_conjBy] at hmove hspan
  have hne : factor ≠ factor.conjBy conjugator :=
    fun heq => hmove (congrArg
      (fun subgroup : Subgroup Actor => commutatorAction subgroup Module) heq)
  have hsecond := hfactor.conjBy factor conjugator
  obtain ⟨hcommute, hdisjoint, hnormal, hpermute, _⟩ :=
    nine_five_canonical_pair_of_support_span hyp factor (factor.conjBy conjugator)
      hfactor hsecond hne hspan
  exact ⟨factor, factor.conjBy conjugator, hfactor.1, hsecond.1,
    hcommute, hdisjoint, hnormal,
    nine_five_canonical_pair_centralizer_of_support_span hyp factor
      (factor.conjBy conjugator) hfactor hsecond hne hspan,
    hpermute, conjugator, rfl⟩

end Stellmacher.SectionNine
