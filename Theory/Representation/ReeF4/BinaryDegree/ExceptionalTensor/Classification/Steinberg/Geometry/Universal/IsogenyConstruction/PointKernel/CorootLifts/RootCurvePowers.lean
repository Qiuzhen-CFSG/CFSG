module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.TorusLift
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.CentralIsogenyRootLifting
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator
public import Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers.FlatOpen
public import Theory.AlgebraicGroup.Morphism.FrobeniusPowerDescent

/-!
# Regular binary-power lifts of root curves

For an isogeny with connected source, each root curve with nontrivial torus
weight lifts to a regular curve after a sufficiently high power of Frobenius.
The parametrization of the target root subgroup is arbitrary. The F4 model
specialization covers both signs of every simple root, and in fact every root.

The identity component of the root preimage is connected and unipotent. Lift
a torus element whose root weight is not one. Its fixed subgroup in this
preimage is connected, but maps trivially into the target root subgroup and
therefore is finite. It is consequently trivial. Centrality of the isogeny
kernel now makes the restricted root map injective. Bijective coordinate
power descent, composed with the chosen target parameter, supplies the regular
lift without recognizing the source as a one-parameter group.

Sources: GLS3, Sections 1.3 and 1.9--1.12
(`refs/KGroup/GLS3/Chapter1.tex`); Borel, *Linear Algebraic Groups*,
Proposition 9.3(2), for connectedness of the fixed unipotent subgroup.
-/

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma root_fixed_eq_one
    {G : Variety k} [AlgebraicGroup G] (T Y : ClosedSubgroup G)
    (χ : TorusWeight T) (hχ : RootWeightEquation T Y χ)
    (xp : OneParameterParametrization Y.carrierVariety)
    (t : Variety.Point T.carrierVariety) (ht : χ.pointCharacter t ≠ 1)
    (y : Variety.Point Y.carrierVariety)
    (hy : Y.inclusion.onPoints y * T.inclusion.onPoints t =
      T.inclusion.onPoints t * Y.inclusion.onPoints y) : y = 1 := by
  let a : k := Multiplicative.toAdd (additiveGroupPointEquiv k (xp.inv.onPoints y))
  have hva : xp.value a = y := by
    change xp.hom.onPoints (kPlusPoint a) = y
    rw [show kPlusPoint a = xp.inv.onPoints y from kPlusPoint_coordinate _]
    exact xp.inv_hom_id y
  have heq := hχ xp a t
  change (T.inclusion.onPoints t)⁻¹ * Y.inclusion.onPoints (xp.value a) *
    T.inclusion.onPoints t = Y.inclusion.onPoints (xp.value (χ.pointCharacter t * a)) at heq
  rw [hva, mul_assoc, hy, inv_mul_cancel_left] at heq
  have hval : xp.value a = xp.value (χ.pointCharacter t * a) :=
    Y.inclusion_injective ((congrArg Y.inclusion.onPoints hva).trans heq)
  have ha : a = χ.pointCharacter t * a := by
    have h := congrArg xp.inv.onPoints hval
    simp only [OneParameterParametrization.value, xp.hom_inv_id] at h
    exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) h
  have ha0 : a = 0 := by
    by_contra hn
    apply ht
    exact (mul_right_cancel₀ hn (ha.symm.trans (one_mul a).symm))
  rw [← hva, ha0]
  exact xp.hom.onPoints.map_one

private lemma rootLift_carrier_connected
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (Y : ClosedSubgroup G) :
    Variety.IsConnected (centralIsogenyRootLift φ Y).carrierVariety := by
  let X := centralIsogenyRootLift φ Y
  let e := Variety.closedSubvarietyPointHomeomorph X.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point H // x ∈ (X : Set (Variety.Point H))} :=
    Subtype.connectedSpace (centralIsogenyRootLift_isConnected φ Y)
  let : ConnectedSpace (Variety.Point X.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem exists_rootLift_bijective
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (T Y : ClosedSubgroup G) (hT : IsSubtorus T)
    (χ : TorusWeight T) (hY : IsTorusRootSubgroup T Y)
    (hχ : RootWeightEquation T Y χ) (hχne : χ ≠ 1) :
    ∃ q : Morphism (centralIsogenyRootLift φ Y).carrierVariety Y.carrierVariety,
      Function.Bijective q.onPoints ∧
      ∀ x, Y.inclusion.onPoints (q.onPoints x) =
        φ.onPoints ((centralIsogenyRootLift φ Y).inclusion.onPoints x) := by
  classical
  let X := centralIsogenyRootLift φ Y
  have hprojection := (φ.comp X.inclusion).closedImageProjection_exists
  rw [centralIsogenyRootLift_image_eq φ hφ.1 Y hY.2] at hprojection
  obtain ⟨q, hqsurj, hqker, hqapply⟩ := hprojection
  change ∀ x, Y.inclusion.onPoints (q.onPoints x) =
    φ.onPoints (X.inclusion.onPoints x) at hqapply
  have hqfinite : Finite q.kernel := by
    rw [hqker]
    let embed : (φ.comp X.inclusion).kernel → φ.kernel := fun z =>
      ⟨X.inclusion.onPoints z.val, z.property⟩
    let : Finite φ.kernel := hφ.2
    exact Finite.of_injective embed (fun x y h => Subtype.ext
      (X.inclusion_injective (congrArg (fun z : φ.kernel => z.val) h)))
  let S := isogenyTorusLift φ T
  have hS := isogenyTorusLift_isSubtorus φ hφ.2 T hT
  have htExists : ∃ t, χ.pointCharacter t ≠ 1 := by
    by_contra hn
    push Not at hn
    apply hχne
    apply TorusCharacter.pointCharacter_injective
    ext t
    exact hn t
  obtain ⟨t, ht⟩ := htExists
  obtain ⟨s0, hs0⟩ := isogenyTorusLiftMap_surjective φ hφ.1 T hT t
  let s := S.inclusion.onPoints s0
  have hsS : s ∈ S := (S.pointEquiv s0).property
  have hsMap : φ.onPoints s = T.inclusion.onPoints t := by
    rw [← isogenyTorusLiftMap_apply, hs0]
  have hsSemi : IsSemisimpleElement H s :=
    morphism_preserves_semisimpleElement S.inclusion s0 (hS.all_semisimple s0)
  have hInv : IsClosedSubgroupInvariant S X :=
    centralIsogenyRootLift_invariant φ S T Y hY.1 (fun z hz =>
      (φ.closedSubgroupPreimage T).identityComponentAmbient_le hz)
  have hsNorm : s ∈ Subgroup.normalizer (X.toSubgroup : Set (Variety.Point H)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h := hInv s⁻¹ (S.inv_mem hsS) x hx
      change s * x * s⁻¹ ∈ X
      simpa only [inv_inv] using h
    · intro hx
      have h := hInv s hsS (s * x * s⁻¹) hx
      change x ∈ X
      simpa [mul_assoc] using h
  let C := semisimpleCommutatorFixedSubgroup X s
  let : AlgebraicGroup C.carrierVariety := C.carrierAlgebraicGroup
  have hCconn : Variety.IsConnected C.carrierVariety :=
    semisimpleCommutatorFixedSubgroup_isConnected X (rootLift_carrier_connected φ Y)
      (centralIsogenyRootLift_isUnipotent φ hφ Y hY.2) s hsSemi hsNorm
  have hCker (x : Variety.Point X.carrierVariety) (hx : x ∈ C) : q.onPoints x = 1 := by
    have hcomm := (semisimpleCommutatorFixedSubgroup_mem_iff X s x).mp hx
    have hmap := congrArg φ.onPoints hcomm
    simp only [map_mul, hsMap] at hmap
    rw [← hqapply x] at hmap
    exact root_fixed_eq_one T Y χ hχ (Classical.choice hY.2) t ht (q.onPoints x) hmap
  have hCfinite : (Set.range C.inclusion.toVariety.toFun).Finite := by
    let : Finite q.kernel := hqfinite
    apply (Set.toFinite (q.kernel : Set (Variety.Point X.carrierVariety))).subset
    rintro x ⟨z, rfl⟩
    exact hCker _ (C.pointEquiv z).property
  have hCone (x : Variety.Point X.carrierVariety) (hx : x ∈ C) : x = 1 := by
    have hsub := connected_finite_morphism_range_subsingleton C.inclusion.toVariety hCconn hCfinite
    have hxrange : x ∈ Set.range C.inclusion.toVariety.toFun := by
      refine ⟨C.pointEquiv.symm ⟨x, hx⟩, ?_⟩
      change (C.pointEquiv (C.pointEquiv.symm ⟨x, hx⟩)).val = x
      rw [C.pointEquiv.apply_symm_apply]
    exact hsub hxrange ⟨1, C.inclusion.onPoints.map_one⟩
  refine ⟨q, ⟨?_, hqsurj⟩, hqapply⟩
  apply (MonoidHom.ker_eq_bot_iff q.onPoints).mp
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply hCone x
  apply (semisimpleCommutatorFixedSubgroup_mem_iff X s x).mpr
  have hxKer : X.inclusion.onPoints x ∈ φ.kernel := by
    change φ.onPoints (X.inclusion.onPoints x) = 1
    rw [← hqapply x, show q.onPoints x = 1 from hx, map_one]
  exact (Subgroup.mem_center_iff.mp (isogeny_kernel_le_center_of_connected φ hφ hH _ hxKer) s).symm


private theorem bijective_to_additive_has_power_lift [CharP k 2]
    {X : Variety k} [AlgebraicGroup X]
    (q : Morphism X (KPlus k)) (hX : Variety.IsConnected X)
    (hq : Function.Bijective q.onPoints) :
    ∃ a : ℕ, ∃ f : Morphism (KPlus k) X,
      ∀ s : k, q.onPoints (f.onPoints (kPlusPoint s)) = kPlusPoint (s ^ (2 ^ a)) := by
  have hp := q.exists_coordinate_frobenius_powers_of_bijective_of_flat_localization hq
    (q.exists_flat_localization_of_bijective_of_connected hX hq) 2
  obtain ⟨a, ha⟩ := q.toVariety.exists_uniform_coordinate_frobenius_power 2 hp
  let Fr : Monoid.End (Variety.Point (KPlus k)) :=
    { toFun := fun x => kPlusPoint (x.val PUnit.unit ^ (2 ^ a))
      map_one' := by
        change kPlusPoint ((0 : k) ^ (2 ^ a)) = 1
        rw [zero_pow (by positivity)]
        rfl
      map_mul' := by
        intro x y
        rw [kPlusPoint_coordinate_mul, add_pow_char_pow, kPlusPoint_mul] }
  have hFr : Function.Bijective Fr := by
    constructor
    · intro x y h
      apply Variety.Point.ext
      funext i
      cases i
      apply (iterateFrobeniusEquiv k 2 a).injective
      exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) h
    · intro y
      refine ⟨kPlusPoint ((iterateFrobeniusEquiv k 2 a).symm (y.val PUnit.unit)), ?_⟩
      apply Variety.Point.ext
      funext i
      cases i
      exact (iterateFrobeniusEquiv k 2 a).apply_symm_apply _
  have hFrcoord (x : Variety.Point (KPlus k)) (i : (KPlus k).Coordinates) :
      (Fr x).val i = x.val i ^ (2 ^ a) := by
    cases i
    rfl
  obtain ⟨f, _, hf⟩ := q.exists_reverse_isogeny_of_coordinate_frobenius_powers
    2 a hq.2 Fr hFr hFrcoord ha
  refine ⟨a, f, fun s => ?_⟩
  exact DFunLike.congr_fun hf (kPlusPoint s)

/-- A root curve with nontrivial torus weight lifts regularly after a binary
power through every isogeny with connected source. -/
public theorem exists_root_curve_binary_power_lift [CharP k 2]
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (T Y : ClosedSubgroup G) (hT : IsSubtorus T)
    (χ : TorusWeight T) (hY : IsTorusRootSubgroup T Y)
    (hχ : RootWeightEquation T Y χ) (hχne : χ ≠ 1)
    (xp : OneParameterParametrization Y.carrierVariety) :
    ∃ a : ℕ, ∃ f : Variety.Morphism (KPlus k) H,
      ∀ s : k, φ.onPoints (f.toFun (kPlusPoint s)) =
        Y.inclusion.onPoints (xp.value (s ^ (2 ^ a))) := by
  let X := centralIsogenyRootLift φ Y
  obtain ⟨q, hq, hqapply⟩ := exists_rootLift_bijective φ hφ hH T Y hT χ hY hχ hχne
  let q0 := xp.inv.comp q
  have hq0 : Function.Bijective q0.onPoints := xp.toMulEquiv.symm.bijective.comp hq
  obtain ⟨a, f, hf⟩ := bijective_to_additive_has_power_lift q0
    (rootLift_carrier_connected φ Y) hq0
  refine ⟨a, X.inclusion.toVariety.comp f.toVariety, fun s => ?_⟩
  change φ.onPoints (X.inclusion.onPoints (f.onPoints (kPlusPoint s))) = _
  rw [← hqapply]
  apply congrArg Y.inclusion.onPoints
  have h := congrArg xp.hom.onPoints (hf s)
  change xp.hom.onPoints (xp.inv.onPoints (q.onPoints (f.onPoints (kPlusPoint s)))) = _ at h
  rw [xp.inv_hom_id] at h
  exact h

/-- Every root in an F4 model, with any chosen parametrization, admits the
regular binary-power lift used by incoming coroot words. -/
public theorem RootSystemModel.exists_root_curve_binary_power_lift [CharP k 2]
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift G)
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (α : M.rootData.Root)
    (xp : OneParameterParametrization (M.rootData.rootSubgroup α).carrierVariety) :
    ∃ a : ℕ, ∃ f : Variety.Morphism (KPlus k) H,
      ∀ s : k, φ.onPoints (f.toFun (kPlusPoint s)) =
        (M.rootData.rootSubgroup α).inclusion.onPoints (xp.value (s ^ (2 ^ a))) := by
  have hχ : M.rootData.rootWeight α ≠ 1 := by
    intro h
    have hp := M.realization.weightPairing_rootWeight α α
    rw [h, M.realization.weightPairing_one,
      M.realization.2.2.2.2.2.2.1 α] at hp
    norm_num at hp
  exact Theory.AlgebraicGroup.exists_root_curve_binary_power_lift φ hφ hH
    M.torus (M.rootData.rootSubgroup α) M.maximalTorus.1 (M.rootData.rootWeight α)
    (M.realization.2.2.1 α).1 (M.realization.2.2.1 α).2 hχ xp

end Theory.AlgebraicGroup
