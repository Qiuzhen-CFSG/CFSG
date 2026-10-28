module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RealizedCharacters
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.Parametrizations
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusAction
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport

/-!
# The conditional genuine Spin D4 root realization

Given a closed maximal torus and an algebraic isomorphism from the split
four-dimensional torus with the prescribed simple-coroot point formula,
`rootData_isRealization` identifies all its actual roots with the 24 D4 roots.
The forward inclusion comes from the explicit Clifford curves; the reverse
inclusion comes from regular natural-matrix coefficients of arbitrary root
curves. Integral Laurent characters and coroot coordinates supply the full
character--cocharacter pairing.

The base is the standard numbered D4 base, rather than an arbitrary chosen
base: vertex 1 is central and 0, 2, 3 are its arms. The based, root-system,
and root-addition comparisons are proved, including completeness of addition
on actual characters. Every root cocharacter is identified with the source
coroot word. The geometric torus inputs remain explicit for independent
construction by the torus owner; no root realization, regular inverse to the
Spin cover, or general classical-group identification is assumed.

Source: GLS3, 1.9.1–6, 1.12.1(e,g), and 1.14.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
local instance realizedRootsTorusAlgebraicGroup (T : ClosedSubgroup (groupVariety k)) : AlgebraicGroup T.carrierVariety :=
  T.carrierAlgebraicGroup

theorem coordinateRootWeight_equation (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) (r : RootIndex) :
    RootWeightEquation T (rootClosedSubgroup k r) (coordinateRootWeight k T e r) :=
  coordinateRootWeight_equation_of_morphism k T e he r _
    (cliffordRootMorphism_kPlusPoint k r)

theorem coordinateRootWeight_range (T : ClosedSubgroup (groupVariety k))
    (hT : IsMaximalTorus T) (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) :
    Set.range (coordinateRootWeight k T e) = TorusRootSet T := by
  apply Set.Subset.antisymm
  · rintro χ ⟨r, rfl⟩
    exact coordinateRootWeight_mem_torusRootSet_of_morphism k T e he r _
      (cliffordRootMorphism_kPlusPoint k r)
  · exact torusRootSet_subset_coordinateRootWeight k T hT e he

/-- Spin root geometry in the prescribed simple-coroot coordinates and standard D4 base. -/
def rootData (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) : RootGroupData (groupVariety k) T where
  Root := ULift.{u,0} RootIndex
  rootWeight := fun r => coordinateRootWeight k T e r.down
  rootSubgroup := fun r => rootClosedSubgroup k r.down
  neg := fun r => ULift.up ((evenOrthogonalSeed 2).neg r.down)
  add := fun r s => ((evenOrthogonalSeed 2).add r.down s.down).map ULift.up
  pairing := fun r s => evenOrthogonalRootPairingInt 2 r.down s.down
  weightPairing := fun χ s => characterCocharacterPairing T
    (coordinateRootCocharacter k T e s.down) (Additive.ofMul χ)
  rootCocharacter := fun r => coordinateRootCocharacter k T e r.down
  reflect := fun r s => ULift.up ((typeDRootPairing 2).reflectionPerm r.down s.down)
  positive := fun r => (typeDRootPairing_base 2).IsPos r.down
  simple := fun r => r.down ∈ (typeDRootPairing_base 2).support
  height := fun r => (typeDRootPairing_base 2).height r.down

omit [CharP k 2] in
theorem rootData_add_eq_some_iff (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety)
    (r s t : (rootData k T e).Root) :
    (rootData k T e).add r s = some t ↔
      (evenOrthogonalSeed 2).add r.down s.down = some t.down := by
  exact evenOrthogonalRootData_add_eq_some_iff (k := k) 2 (le_refl 2) r s t

private theorem standardBase_simple_iff (r : RootIndex) :
    r ∈ (typeDRootPairing_base 2).support ↔
      (typeDRootPairing_base 2).IsPos r ∧
      ∀ s t, (evenOrthogonalSeed 2).add s t = some r →
        ¬ ((typeDRootPairing_base 2).IsPos s ∧ (typeDRootPairing_base 2).IsPos t) := by
  let b := typeDRootPairing_base 2
  constructor
  · intro hr
    refine ⟨b.isPos_of_mem_support hr, ?_⟩
    intro s t h ⟨hs, ht⟩
    have hh := b.height_add ((evenOrthogonalSeed 2).add_eq_some_iff.mp h)
    have hh1 := b.height_one_of_mem_support hr
    change 0 < b.height s at hs
    change 0 < b.height t at ht
    omega
  · rintro ⟨hr, hind⟩
    let pred : RootIndex → Prop := fun z => b.IsPos z → z ∈ b.support ∨
        ∃ s t, b.IsPos s ∧ b.IsPos t ∧
          (typeDRootPairing 2).root z =
            (typeDRootPairing 2).root s + (typeDRootPairing 2).root t
    have hp : pred r := hr.induction_on_add (p := pred) (fun s hs _ => Or.inl hs)
        (fun s t z hz _ ht hzpos => by
          have hs : b.IsPos s := by
            change 0 < b.height s
            have hh := b.height_add hz
            have ht1 := b.height_one_of_mem_support ht
            have hs0 := b.height_ne_zero s
            change 0 < b.height z at hzpos
            omega
          exact Or.inr ⟨s, t, hs, b.isPos_of_mem_support ht, hz⟩)
    rcases hp hr with hr | ⟨s, t, hs, ht, h⟩
    · exact hr
    · exact False.elim (hind s t ((evenOrthogonalSeed 2).add_eq_some_iff.mpr h) ⟨hs, ht⟩)

/-- The only geometric premises are a maximal torus and its actual coroot-coordinate isomorphism. -/
theorem rootData_isRealization (T : ClosedSubgroup (groupVariety k))
    (hT : IsMaximalTorus T) (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) : (rootData k T e).IsRealization := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s h
    exact ULift.ext _ _ (coordinateRootWeight_injective k T e h)
  · rw [← coordinateRootWeight_range k T hT e he]
    ext χ
    constructor
    · rintro ⟨r, rfl⟩; exact ⟨r.down, rfl⟩
    · rintro ⟨r, rfl⟩; exact ⟨ULift.up r, rfl⟩
  · intro r
    exact ⟨⟨rootClosedSubgroup_invariant k T e he r.down,
      rootClosedSubgroup_isOneParameter k r.down⟩,
      coordinateRootWeight_equation k T e he r.down⟩
  · intro r
    apply Additive.ofMul.injective
    change corootCharacterMap k T e
        (simpleCorootPairingMap (evenOrthogonalRootExponent 4 ((evenOrthogonalSeed 2).neg r.down))) =
      -(corootCharacterMap k T e
        (simpleCorootPairingMap (evenOrthogonalRootExponent 4 r.down)))
    rw [evenOrthogonalRootExponent_neg 2 (le_refl 2), map_neg, map_neg]
  · intro r s t h
    have ha := (rootData_add_eq_some_iff k T e r s t).mp h
    apply Additive.ofMul.injective
    change corootCharacterMap k T e
        (simpleCorootPairingMap (evenOrthogonalRootExponent 4 t.down)) =
      corootCharacterMap k T e (simpleCorootPairingMap (evenOrthogonalRootExponent 4 r.down)) +
        corootCharacterMap k T e (simpleCorootPairingMap (evenOrthogonalRootExponent 4 s.down))
    rw [evenOrthogonalRootExponent_add (le_refl 2) _ _ _ ha, map_add, map_add]
  · intro r s
    apply Additive.ofMul.injective
    change corootCharacterMap k T e
        (simpleCorootPairingMap (evenOrthogonalRootExponent 4
          ((evenOrthogonalSeed 2).reflectionPerm r.down s.down))) =
      corootCharacterMap k T e (simpleCorootPairingMap (evenOrthogonalRootExponent 4 s.down)) +
        (-evenOrthogonalRootPairingInt 2 s.down r.down) •
          corootCharacterMap k T e (simpleCorootPairingMap (evenOrthogonalRootExponent 4 r.down))
    rw [evenOrthogonalRootExponent_reflect 2 (le_refl 2), map_sub, map_sub]
    simp only [map_zsmul, sub_eq_add_neg, neg_smul]
  · intro r
    exact (evenOrthogonalSeed 2).cartan_self r.down
  · intro r s
    exact coordinateRootCocharacter_pairing k T e r.down s.down
  · intro r
    let _ := (typeDRootPairing 2).indexNeg
    exact (typeDRootPairing_base 2).height_reflectionPerm_self r.down
  · intro r s t h
    exact (typeDRootPairing_base 2).height_add
      ((evenOrthogonalSeed 2).add_eq_some_iff.mp
        ((rootData_add_eq_some_iff k T e r s t).mp h))
  · rfl
  · intro r
    change r.down ∈ (typeDRootPairing_base 2).support ↔ _
    rw [standardBase_simple_iff]
    constructor
    · rintro ⟨hr, h⟩
      exact ⟨hr, fun s t hst => h s.down t.down
        ((rootData_add_eq_some_iff k T e s t r).mp hst)⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, fun s t hst => h (ULift.up s) (ULift.up t)
        ((rootData_add_eq_some_iff k T e (ULift.up s) (ULift.up t) r).mpr hst)⟩
  · intro χ r
    exact characterCocharacterPairing_spec T χ (coordinateRootCocharacter k T e r.down)

omit [CharP k 2] in
/-- The realized pairing, reflections, opposites and numbered simple roots are the standard D4 ones. -/
theorem rootData_isActualBasedRootPairing (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    IsActualBasedRootPairing (rootData k T e) (typeDRootPairing 2)
      (typeDRootPairing_base 2) Equiv.ulift := by
  exact ⟨fun r s => evenOrthogonalRootPairingInt_cast 2 r.down s.down,
    fun _ _ => rfl, fun _ => rfl, fun _ => Iff.rfl⟩

omit [CharP k 2] in
/-- The height and positive system use the same standard base. -/
theorem rootData_isRootSystemRealization (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    IsRootSystemRealization (rootData k T e) (typeDRootPairing 2)
      Equiv.ulift (typeDRootPairing_base 2) := by
  obtain ⟨hp, hr, hn, hs⟩ := rootData_isActualBasedRootPairing k T e
  exact ⟨hp, hr, hn, hs, fun _ => rfl⟩

omit [CharP k 2] in
/-- Partial addition in the actual root datum is exactly vector addition in D4. -/
theorem rootData_isRootAdditionRealization (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    IsRootAdditionRealization (rootData k T e) (typeDRootPairing 2) Equiv.ulift := by
  intro r s t
  rw [rootData_add_eq_some_iff]
  exact (evenOrthogonalSeed 2).add_eq_some_iff

omit [CharP k 2] in
/-- The simple roots are exactly the published source indices. -/
theorem rootData_simple_eq_range (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    (rootData k T e).simple = Set.range (fun i => ULift.up (simpleRoot i)) := by
  ext r
  change r.down ∈ (typeDRootPairing_base 2).support ↔ _
  change r.down ∈ ((typeDRootPairing_base 2).support : Set RootIndex) ↔ _
  rw [typeDRootPairing_base_support]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, ULift.ext _ _ hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- Every constructed root cocharacter is the source's normalized coroot word. -/
theorem coordinateRootCocharacter_inclusion (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) (he : HasCorootCoordinates k T e)
    (r : RootIndex) (t : Variety.Point (KMult k)) :
    T.includePoint ((coordinateRootCocharacter k T e r).onPoints t) =
      corootWord k r (dPointEquiv 1 t 0) := by
  change T.inclusion.onPoints (e.hom.onPoints
    ((dCharacterTupleMorphism 4 1 (fun i _ => rootCorootCoefficients r i)).onPoints t)) = _
  rw [he]
  have hd : dPointEquiv 4
      ((dCharacterTupleMorphism (k := k) 4 1 (fun i _ => rootCorootCoefficients r i)).onPoints t) =
      fun i => (dPointEquiv 1 t 0) ^ rootCorootCoefficients r i := by
    funext i
    rw [dCharacterTupleMorphism_apply]
    simp
  rw [hd]
  apply naturalAction_injective k
  change naturalAction k (CorootTorus.parameter k _) = _
  rw [CorootTorus.naturalAction_parameter, naturalAction_corootWord]
  congr 1
  funext p
  rw [corootDiagonal_eq_zpow]
  calc
    CorootTorus.diagonal k (fun i => (dPointEquiv 1 t 0) ^ rootCorootCoefficients r i) p =
        ∏ i, ((dPointEquiv 1 t 0) ^ rootCorootCoefficients r i) ^
          evenOrthogonalRootExponent 4 (simpleRoot i) p := by
      simpa only [NaturalCoefficients.entryCorootExponent_inl, NaturalCoefficients.diagonalEntry] using
        (NaturalCoefficients.entryCorootExponent_laurent k
          (fun i => (dPointEquiv 1 t 0) ^ rootCorootCoefficients r i) (.inl p)).symm
    _ = (dPointEquiv 1 t 0) ^ evenOrthogonalRootExponent 4 r p := by
      rw [← rootCorootCoefficients_expansion r p]
      simp only [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add, zpow_mul]

/-- In particular, the standard simple cocharacters are precisely the published simple coroots. -/
theorem coordinateRootCocharacter_simple_inclusion (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) (he : HasCorootCoordinates k T e)
    (i : Fin 4) (t : Variety.Point (KMult k)) :
    T.includePoint ((coordinateRootCocharacter k T e (simpleRoot i)).onPoints t) =
      simpleCoroot k i (dPointEquiv 1 t 0) :=
  coordinateRootCocharacter_inclusion k T e he (simpleRoot i) t

omit [CharP k 2] in
/-- No sum of actual root characters is missed by the partial addition operation. -/
theorem rootData_isRootAdditionComplete (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) :
    (rootData k T e).IsRootAdditionComplete := by
  intro r s t h
  rw [rootData_add_eq_some_iff]
  apply (rootCorootExponent_add_iff r.down s.down t.down).mp
  apply corootCharacterMap_injective k T e
  rw [map_add]
  exact congrArg Additive.ofMul h

omit [CharP k 2] in
/-- The numbered simple pairings have central vertex 1 and arms 0, 2, 3. -/
theorem rootData_pairing_simple (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) (i j : Fin 4) :
    (rootData k T e).pairing (ULift.up (simpleRoot i)) (ULift.up (simpleRoot j)) =
      typeDCartanMatrix 2 i j := by
  change evenOrthogonalRootPairingInt 2 (simpleRoot i) (simpleRoot j) = _
  rw [← rootCorootCoefficients_pairing, rootCorootCoefficients_simple]
  classical
  simp only [Pi.single_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact rootCorootExponent_simple i j

omit [CharP k 2] in
/-- Opposite roots agree with the fixed signed root-point convention. -/
theorem rootData_neg (T : ClosedSubgroup (groupVariety k))
    (e : Iso (dVariety k 4) T.carrierVariety) (r : RootIndex) :
    (rootData k T e).neg (ULift.up r) = ULift.up (negativeRoot r) := by
  apply ULift.ext
  apply typeDRootEmbedding_injective 4
  apply Subtype.ext
  change typeDRootVector 4 ((evenOrthogonalSeed 2).neg r) =
    typeDRootVector 4 (negativeRoot r)
  rw [negativeRoot_vector]
  have h := congrArg (fun z : typeDRootSpan 4 => (z : Vec 4))
    ((evenOrthogonalSeed 2).root_neg r)
  simpa only [evenOrthogonalSeed, typeDRootPairing_root, typeDRootInSpan_val,
    typeDRootEmbedding, Submodule.coe_neg] using h

/-- The canonical positive roots form an actual positive system. -/
theorem rootData_positive_isPositiveSystem (T : ClosedSubgroup (groupVariety k))
    (hT : IsMaximalTorus T) (e : Iso (dVariety k 4) T.carrierVariety)
    (he : HasCorootCoordinates k T e) :
    IsPositiveSystem (rootData k T e) (rootData k T e).positive :=
  (rootData_isRealization k T hT e he).positive_isPositiveSystem_of_height_ne_zero
    (fun r => (typeDRootPairing_base 2).height_ne_zero r.down)

end Triality.SimplyConnected.Pinning
