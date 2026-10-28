module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.CharacterLattice
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.RootCurvePowers
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootCoordinates
public import Theory.AlgebraicGroup.Tori.IsogenyPreimage

/-!
# Incoming isogenies have trivial point kernel on Spin D4

Let `φ : H → Spin₈` be an isogeny with connected source over an algebraically
closed field of characteristic two. The pinned regular root curves lift after
binary powers. Opposite curves give normalized regular coroot words; their
multiplicative defects have connected finite image, so the words are actual
cocharacters of the connected torus preimage.

The product of the four lifted cocharacters, followed by the torus map, is the
algebraic simple-coroot coordinate isomorphism composed with coordinatewise
binary powers. It is bijective on points. A finite-kernel torus argument then
makes the torus map injective. The full character lattice identifies the
nontrivial root characters used in the root-curve lifting step.

The sole extra geometric premise in the final theorem says that the source
center lies in every maximal torus. Centrality of the isogeny kernel and
maximality of the connected torus preimage then give the claimed injectivity.
This premise is left for the semisimple-center theorem in the universality
assembly. No regular inverse to an inseparable isogeny is asserted.

The conventions are `nα(t) = xα(t)x−α(−t⁻¹)xα(t)` and
`hα(t) = nα(1)⁻¹nα(t)`. Source: GLS3, §§1.9–1.12, especially
Proposition 1.10.3(a) and Theorem 1.12.5(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

namespace IncomingPointKernel

private theorem rootWeight_ne_one (r : (pinnedRootData k).Root) :
    (pinnedRootData k).rootWeight r ≠ 1 := by
  intro h
  have hz : rootCorootExponent r.down = 0 := by
    apply (characterLatticeEquiv k).injective
    rw [map_zero, characterLatticeEquiv_apply, ← pinnedRootData_rootWeight k r, h]
    rfl
  have hp := rootCorootCoefficients_pairing r.down r.down
  have hself : evenOrthogonalRootPairingInt 2 r.down r.down = 2 :=
    (pinnedRootData_isRealization k).2.2.2.2.2.2.1 r
  rw [hz, hself] at hp
  norm_num at hp

/-- The pinned Clifford root curve admits a regular binary-power lift. -/
theorem exists_root_curve_lift
    {H : Variety k} [AlgebraicGroup H]
    (φ : Morphism H (groupVariety k)) (hφ : IsIsogeny φ)
    (hH : IsConnected (Set.univ : Set (Variety.Point H))) (r : RootIndex) :
    ∃ a : ℕ, ∃ f : Variety.Morphism (KPlus k) H,
      ∀ s : k, φ.onPoints (f.toFun (kPlusPoint s)) =
        (cliffordRootMorphism k r).onPoints (kPlusPoint (s ^ (2 ^ a))) := by
  let α := pinnedRootIndex k r
  have hD := pinnedRootData_isRealization k
  obtain ⟨a, f, hf⟩ := Theory.AlgebraicGroup.exists_root_curve_binary_power_lift
    φ hφ hH (CorootTorus.closedSubgroup k) ((pinnedRootData k).rootSubgroup α)
    (CorootTorus.isSubtorus k) ((pinnedRootData k).rootWeight α)
    (hD.2.2.1 α).1 (hD.2.2.1 α).2 (rootWeight_ne_one k α)
    (pinnedRootParametrization k α)
  refine ⟨a, f, fun s => ?_⟩
  rw [hf, cliffordRootMorphism_kPlusPoint]
  exact pinnedRootParametrization_inclusion k α _

private theorem target_coroot_word (i : Fin 4) (t : Variety.Point (KMult k)) :
    (binaryCorootWord (cliffordRootMorphism k (simpleRoot i)).toVariety
      (cliffordRootMorphism k (negativeSimpleRoot i)).toVariety).toFun t =
    (CorootTorus.closedSubgroup k).inclusion.onPoints
      (((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t) := by
  change _ = (CorootTorus.closedSubgroup k).includePoint _
  rw [binaryCorootWord_apply, pinnedRootData_rootCocharacter]
  have hc (r : RootIndex) (s : k) :
      (cliffordRootMorphism k r).toVariety.toFun (kPlusPoint s) = rootPoint k r s :=
    cliffordRootMorphism_kPlusPoint k r s
  simp only [hc, corootWord, normalizerWord, Units.val_one, inv_one, CharTwo.neg_eq,
    pinnedRootIndex]

/-- The four source-normalized simple coroots lift through characteristic powers. -/
theorem exists_coroot_power_lifts
    {H : Variety k} [AlgebraicGroup H]
    (φ : Morphism H (groupVariety k)) (hφ : IsIsogeny φ)
    (hH : IsConnected (Set.univ : Set (Variety.Point H))) :
    ∃ a : Fin 4 → ℕ,
      ∃ μ : Fin 4 → Morphism (KMult k)
        (isogenyTorusLift φ (CorootTorus.closedSubgroup k)).carrierVariety,
      ∀ i t, (isogenyTorusLiftMap φ (CorootTorus.closedSubgroup k)).onPoints
        ((μ i).onPoints t) =
        ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints
          (t ^ (2 ^ a i)) := by
  choose a xH yH hxH hyH using fun i : Fin 4 =>
    exists_common_binary_parameter_lifts φ (cliffordRootMorphism k (simpleRoot i)).toVariety
      (cliffordRootMorphism k (negativeSimpleRoot i)).toVariety
      (exists_root_curve_lift k φ hφ hH (simpleRoot i))
      (exists_root_curve_lift k φ hφ hH (negativeSimpleRoot i))
  choose μ hμ using fun i =>
    exists_isogenyTorusLift_cocharacter_of_binary_root_words φ hφ.2
      (CorootTorus.closedSubgroup k)
      ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i)))
      (cliffordRootMorphism k (simpleRoot i)).toVariety
      (cliffordRootMorphism k (negativeSimpleRoot i)).toVariety
      (target_coroot_word k i) (xH i) (yH i) (2 ^ a i) (hxH i) (hyH i)
  exact ⟨a, μ, hμ⟩

private theorem coroot_product_coordinates (x : Variety.Point (dVariety k 4)) :
    (List.ofFn fun i : Fin 4 =>
      ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints
        ((dCoordinateCharacter 4 i).onPoints x)).prod =
      (CorootTorus.coordinateIso k).hom.onPoints x := by
  apply (CorootTorus.closedSubgroup k).inclusion_injective
  rw [map_list_prod, List.map_ofFn, CorootTorus.coordinateIso_inclusion]
  congr 1
  apply congrArg List.ofFn
  funext i
  change (CorootTorus.closedSubgroup k).includePoint _ = _
  rw [pinnedRootData_rootCocharacter]
  congr 1

/-- The connected source torus has trivial point kernel. -/
theorem torusMap_injective
    {H : Variety k} [AlgebraicGroup H]
    (φ : Morphism H (groupVariety k)) (hφ : IsIsogeny φ)
    (hH : IsConnected (Set.univ : Set (Variety.Point H))) :
    Function.Injective (isogenyTorusLiftMap φ (CorootTorus.closedSubgroup k)).onPoints := by
  let T := CorootTorus.closedSubgroup k
  let S := isogenyTorusLift φ T
  let q := isogenyTorusLiftMap φ T
  have hS : IsTorus S.carrierVariety :=
    isogenyTorusLift_isSubtorus φ hφ.2 T (CorootTorus.isSubtorus k)
  obtain ⟨a, μ, hμ⟩ := exists_coroot_power_lifts k φ hφ hH
  let p := cocharacterTupleProduct hS μ
  let δ : Variety.Point (dVariety k 4) → Variety.Point (dVariety k 4) :=
    fun x => (dPointEquiv 4).symm (fun i => dPointEquiv 4 x i ^ (2 ^ a i))
  have hδ : Function.Bijective δ := diagonal_primePower_bijective 2 a
  have hcoordinate (i : Fin 4) (x : Variety.Point (dVariety k 4)) :
      (dCoordinateCharacter 4 i).onPoints (δ x) =
        ((dCoordinateCharacter 4 i).onPoints x) ^ (2 ^ a i) := by
    apply (dPointEquiv 1).injective
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [dCoordinateCharacter_apply, dPointEquiv_pow, Pi.pow_apply]
    exact congrFun ((dPointEquiv 4).apply_symm_apply _) i
  have hcomp (x : Variety.Point (dVariety k 4)) :
      q.onPoints (p.onPoints x) = (CorootTorus.coordinateIso k).hom.onPoints (δ x) := by
    rw [show p = cocharacterTupleProduct hS μ from rfl,
      cocharacterTupleProduct_apply, map_list_prod, List.map_ofFn,
      ← coroot_product_coordinates]
    congr 1
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [hμ, hcoordinate]
  apply torus_injective_of_bijective_composite (dVariety_isTorus 4) hS p q
    (isogenyTorusLiftMap_kernel_finite φ hφ.2 T)
  have hpoint : (q.comp p).onPoints =
      (fun x => (CorootTorus.coordinateIso k).toMulEquiv (δ x)) := funext hcomp
  rw [hpoint]
  exact (CorootTorus.coordinateIso k).toMulEquiv.bijective.comp hδ

end IncomingPointKernel

/-- An incoming connected isogeny has trivial point kernel, provided the
source center lies in each maximal torus. -/
theorem incoming_isogeny_injective_of_center_le_maximalTorus
    {H : Variety k} [AlgebraicGroup H]
    (hH : IsConnected (Set.univ : Set (Variety.Point H)))
    (φ : Morphism H (groupVariety k)) (hφ : IsIsogeny φ)
    (hcenter : ∀ S : ClosedSubgroup H, IsMaximalTorus S →
      Subgroup.center (Variety.Point H) ≤ S.toSubgroup) :
    Function.Injective φ.onPoints := by
  let T := CorootTorus.closedSubgroup k
  let S := isogenyTorusLift φ T
  let q := isogenyTorusLiftMap φ T
  have hS : IsMaximalTorus S :=
    φ.closedSubgroupPreimage_identityComponent_isMaximalTorus hφ T (CorootTorus.isMaximal k)
  have hkernel : φ.kernel ≤ S.toSubgroup :=
    fun x hx => hcenter S hS (isogeny_kernel_le_center_of_connected φ hφ hH x hx)
  have hq : Function.Injective q.onPoints := IncomingPointKernel.torusMap_injective k φ hφ hH
  apply φ.onPoints.ker_eq_bot_iff.mp
  apply le_antisymm
  · intro x hx
    let s : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hkernel hx⟩
    have hs : S.inclusion.onPoints s = x :=
      congrArg Subtype.val (S.pointEquiv.apply_symm_apply _)
    have hqs : q.onPoints s = 1 := by
      apply T.inclusion_injective
      rw [map_one, isogenyTorusLiftMap_apply, hs]
      exact hx
    have hsone : s = 1 := hq (hqs.trans q.onPoints.map_one.symm)
    apply Subgroup.mem_bot.mpr
    rw [← hs, hsone, map_one]
  · exact bot_le

end Triality.SimplyConnected
