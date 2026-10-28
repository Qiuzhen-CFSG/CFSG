module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Inputs
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.RootSubgroups.TorusGeneratedNormalizer
public import Theory.AlgebraicGroup.Simple.Basic
public import Theory.AlgebraicGroup.Morphism.CodRestrict
public import Theory.AlgebraicGroup.Morphism.Power

/-!
# Restrictions of the actual pinned D4 maps to the torus

The supplied diagram automorphism and Frobenius preserve the actual maximal
torus and act on its simple coroots by the numbered diagram permutation and
squaring, respectively. Thus every `Geometry` supplies `PinnedTorusMaps`.

First the realized root groups generate the ambient simple group: their
connected closed generated subgroup is normal by the big-cell generation
statement and torus invariance, and it is nontrivial. Two morphisms from a
connected group having the same conjugation action on these root groups then
coincide. Their regular pointwise quotient lands in the finite center and is
constant, with value one at the identity.

Apply this comparison to the actual ambient images of each coroot, using
`diagram_root`, `frobenius_root`, and the realized Cartan equations. Throughout
we retain the inverse-conjugation convention of `RootWeightEquation`. Finally,
character duality and the supplied weight coordinates express every torus point
as a product of the four simple-coroot points. This proves preservation and
allows regular codomain restriction of both ambient maps.

Sources: GLS3, Chapter 1, §§1.9--1.10, especially Remarks 1.9.6;
Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§6 and 11.2.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual root subgroups generate the supplied simple ambient group. -/
theorem rootSubgroupGenerated_eq_top (S : Geometry K) : RootSubgroupGenerated S.roots Set.univ = ⊤ := by
  have hc (a : S.roots.Root) : IsConnected (S.roots.rootSubgroup a : Set K.Point) := by
    let : ConnectedSpace (S.roots.rootSubgroup a).carrierVariety.Point :=
      connectedSpace_iff_univ.mpr (S.realized.2.2.1 a).1.2.isConnected
    change IsConnected ((S.roots.rootSubgroup a).toSubgroup : Set K.Point)
    rw [← (S.roots.rootSubgroup a).range_inclusion]
    exact isConnected_range (S.roots.rootSubgroup a).inclusion.toVariety.continuous
  have he : RootSubgroupGenerated S.roots Set.univ =
      Subgroup.closure (⋃ a, (S.roots.rootSubgroup a : Set K.Point)) := by
    simp only [RootSubgroupGenerated, Set.mem_univ, Set.iUnion_true]
  let R : ClosedSubgroup K := ClosedSubgroup.ofSubgroup
    (RootSubgroupGenerated S.roots Set.univ) (by
      rw [he]
      exact closure_iUnion_connected_closedSubgroup_isZariskiClosed _ hc)
  have hconn : IsConnected (R : Set K.Point) := by
    change IsConnected (RootSubgroupGenerated S.roots Set.univ : Set K.Point)
    rw [he]
    exact closure_iUnion_connected_closedSubgroup_isConnected _ hc
  let : PreirreducibleSpace K.Point :=
    ⟨(connectedAlgebraicGroup_irreducible K S.simple.1).2⟩
  have hgen := S.bigCell.generated_eq_top_of_dense S.simple.1
  have hnorm : R.toSubgroup.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (Subgroup.le_normalizer) (torus_le_rootSubgroupGenerated_normalizer
      S.roots S.realized Set.univ)
  rcases S.simple.normal_subgroup_dichotomy R hnorm hconn with hbot | htop
  · have hr := rootSubgroup_le_RootSubgroupGenerated S.roots
      (A := Set.univ) (α := (S.simpleRoot 0).val) (Set.mem_univ _)
    change (S.roots.rootSubgroup (S.simpleRoot 0).val).toSubgroup ≤ R.toSubgroup at hr
    rw [hbot] at hr
    exact False.elim ((S.realized.2.2.1 (S.simpleRoot 0).val).1.invariant_unipotent_ne_bot.2.2
      (le_bot_iff.mp hr))
  · exact htop

private def rootPoint (S : Geometry K) (a : S.roots.Root) (t : k) : K.Point :=
  (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value t)

omit [IsAlgClosed k] in
private theorem rootPoint_surjective (S : Geometry K) (a : S.roots.Root)
    (x : K.Point) (hx : x ∈ S.roots.rootSubgroup a) : ∃ t, rootPoint S a t = x := by
  obtain ⟨z, hz⟩ := (S.rootParameter a).toMulEquiv.surjective
    ((S.roots.rootSubgroup a).pointEquiv.symm ⟨x, hx⟩)
  refine ⟨Multiplicative.toAdd (additiveGroupPointEquiv k z), ?_⟩
  unfold rootPoint OneParameterParametrization.value kPlusPoint
  change (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).hom.onPoints
    ((additiveGroupPointEquiv k).symm (additiveGroupPointEquiv k z))) = x
  rw [Equiv.symm_apply_apply]
  change (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).toMulEquiv z) = x
  rw [hz]
  exact congrArg Subtype.val ((S.roots.rootSubgroup a).pointEquiv.apply_symm_apply ⟨x, hx⟩)

private theorem morphism_eq_of_root_conjugation (S : Geometry K)
    {H : Variety k} [AlgebraicGroup H] (hH : H.IsConnected)
    (f g : Theory.AlgebraicGroup.Morphism H K)
    (h : ∀ z a t, (f.onPoints z)⁻¹ * rootPoint S a t * f.onPoints z =
      (g.onPoints z)⁻¹ * rootPoint S a t * g.onPoints z) : f = g := by
  let δ : Variety.Morphism H K := (mulMorphism K).comp
    (f.toVariety.pair ((invMorphism K).comp g.toVariety))
  have hδ (z : H.Point) : δ.toFun z = f.onPoints z * (g.onPoints z)⁻¹ := rfl
  have hc (z : H.Point) : δ.toFun z ∈ Subgroup.center K.Point := by
    have hle : RootSubgroupGenerated S.roots Set.univ ≤
        Subgroup.centralizer ({δ.toFun z} : Set K.Point) := by
      apply (RootSubgroupGenerated_le_iff _ _ _).mpr
      intro a _ x hx
      obtain ⟨t, rfl⟩ := rootPoint_surjective S a x hx
      rw [Subgroup.mem_centralizer_singleton_iff, hδ]
      calc
        rootPoint S a t * (f.onPoints z * (g.onPoints z)⁻¹) =
            f.onPoints z * ((f.onPoints z)⁻¹ * rootPoint S a t * f.onPoints z) *
              (g.onPoints z)⁻¹ := by group
        _ = f.onPoints z * ((g.onPoints z)⁻¹ * rootPoint S a t * g.onPoints z) *
              (g.onPoints z)⁻¹ := by rw [h]
        _ = _ := by group
    rw [rootSubgroupGenerated_eq_top S] at hle
    exact Subgroup.mem_center_iff.mpr fun x =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle (by trivial)))
  let : Finite (Subgroup.center K.Point) := simple_center_finite S.simple
  have hfin : (Set.range δ.toFun).Finite :=
    (Set.toFinite (Subgroup.center K.Point : Set K.Point)).subset (by
      rintro x ⟨z, rfl⟩
      exact hc z)
  have hsub := connected_finite_morphism_range_subsingleton δ hH hfin
  apply Theory.AlgebraicGroup.Morphism.ext
  funext z
  have hz := hsub ⟨z, rfl⟩ ⟨1, rfl⟩
  rw [hδ, hδ, map_one, map_one, inv_one, mul_one, mul_inv_eq_one] at hz
  exact hz

omit [IsAlgClosed k] in
private theorem root_conjugation (S : Geometry K) (a b : S.roots.Root)
    (z : (KMult k).Point) (t : k) :
    (S.torus.includePoint ((S.roots.rootCocharacter b).onPoints z))⁻¹ *
      rootPoint S a t * S.torus.includePoint ((S.roots.rootCocharacter b).onPoints z) =
      rootPoint S a ((dPointEquiv 1 z 0 : k) ^ S.roots.pairing a b * t) := by
  have h := (S.realized.2.2.1 a).2 (S.rootParameter a) t
    ((S.roots.rootCocharacter b).onPoints z)
  rw [S.realized.rootWeight_rootCocharacter a b z] at h
  exact h

private def diagramRoot (S : Geometry K) : S.roots.Root ≃ S.roots.Root :=
  S.rootIndex.trans (typeD4DiagramEquiv.indexEquiv.trans S.rootIndex.symm)

omit [IsAlgClosed k] in
private theorem diagramRoot_simple (S : Geometry K) (i : Fin 4) :
    diagramRoot S (S.simpleRoot i).val = (S.simpleRoot (typeD4DiagramPermutation i)).val := by
  apply S.rootIndex.injective
  change S.rootIndex (S.rootIndex.symm _) = _
  rw [S.rootIndex.apply_symm_apply, S.simpleRoot_index, typeD4DiagramEquiv_numbered,
    S.simpleRoot_index]

omit [IsAlgClosed k] in
private theorem diagramRoot_pairing (S : Geometry K) (a b : S.roots.Root) :
    S.roots.pairing (diagramRoot S a) (diagramRoot S b) = S.roots.pairing a b := by
  have he : (typeDRootPairing 2).pairing
      (typeD4DiagramEquiv.indexEquiv (S.rootIndex a))
      (typeD4DiagramEquiv.indexEquiv (S.rootIndex b)) =
      (typeDRootPairing 2).pairing (S.rootIndex a) (S.rootIndex b) := by
    let P := typeDRootPairing 2
    let e := typeD4DiagramEquiv
    rw [← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing]
    rw [← RootPairing.Hom.root_weightMap_apply P P (S.rootIndex a) e.toHom]
    have hc : e.coweightMap (P.coroot (e.indexEquiv (S.rootIndex b))) =
        P.coroot (S.rootIndex b) := by
      simpa using RootPairing.Hom.coroot_coweightMap_apply P P
        (e.indexEquiv (S.rootIndex b)) e.toHom
    rw [← hc]
    exact DFunLike.congr_fun
      (LinearMap.congr_fun e.weight_coweight_transpose
        (P.coroot (e.indexEquiv (S.rootIndex b)))) (P.root (S.rootIndex a))
  have hp := S.based.1 (diagramRoot S a) (diagramRoot S b)
  simp only [diagramRoot, Equiv.trans_apply, Equiv.apply_symm_apply] at hp
  rw [he, ← S.based.1 a b] at hp
  exact_mod_cast hp

/-- The ambient diagram automorphism carries each realized coroot to the
coroot indexed by its actual D4 root permutation. -/
theorem diagram_coroot_ambient (S : Geometry K) (b : S.roots.Root) (z : (KMult k).Point) :
    S.diagram.toMulEquiv (S.torus.includePoint ((S.roots.rootCocharacter b).onPoints z)) =
      S.torus.includePoint ((S.roots.rootCocharacter
        (S.rootIndex.symm (typeD4DiagramEquiv.indexEquiv (S.rootIndex b)))).onPoints z) := by
  let f := S.diagram.hom.comp (S.torus.inclusion.comp (S.roots.rootCocharacter b))
  let g := S.torus.inclusion.comp (S.roots.rootCocharacter (diagramRoot S b))
  have he : f = g := by
    apply morphism_eq_of_root_conjugation S ((dVariety_isTorus (k := k) 1).isConnected)
    intro w a t
    obtain ⟨a, rfl⟩ := (diagramRoot S).surjective a
    have h := congrArg S.diagram.toMulEquiv (root_conjugation S a b w t)
    simp only [map_mul, map_inv, rootPoint, S.diagram_root] at h
    change (f.onPoints w)⁻¹ * rootPoint S (diagramRoot S a) t * f.onPoints w = _ at h
    change (f.onPoints w)⁻¹ * rootPoint S (diagramRoot S a) t * f.onPoints w =
      (S.torus.includePoint ((S.roots.rootCocharacter (diagramRoot S b)).onPoints w))⁻¹ *
      rootPoint S (diagramRoot S a) t *
      S.torus.includePoint ((S.roots.rootCocharacter (diagramRoot S b)).onPoints w)
    rw [root_conjugation, diagramRoot_pairing]
    exact h
  exact congrArg (fun e : Theory.AlgebraicGroup.Morphism (KMult k) K => e.onPoints z) he

/-- The ambient Frobenius squares the parameter of every realized coroot. -/
theorem frobenius_coroot_ambient (S : Geometry K) (b : S.roots.Root)
    (z : (KMult k).Point) :
    S.frobenius.onPoints (S.torus.includePoint ((S.roots.rootCocharacter b).onPoints z)) =
      S.torus.includePoint ((S.roots.rootCocharacter b).onPoints (z ^ 2)) := by
  let f := S.frobenius.comp (S.torus.inclusion.comp (S.roots.rootCocharacter b))
  let sq := commutativeNpowMorphism (KMult k) (dVariety_isMulCommutative 1) 2
  let g := (S.torus.inclusion.comp (S.roots.rootCocharacter b)).comp sq
  have he : f = g := by
    apply morphism_eq_of_root_conjugation S ((dVariety_isTorus (k := k) 1).isConnected)
    intro w a t
    obtain ⟨s, rfl⟩ := IsAlgClosed.exists_pow_nat_eq t (by decide : 0 < 2)
    have h := congrArg S.frobenius.onPoints (root_conjugation S a b w s)
    simp only [map_mul, map_inv, rootPoint, S.frobenius_root] at h
    change (f.onPoints w)⁻¹ * rootPoint S a (s ^ 2) * f.onPoints w =
      rootPoint S a (((dPointEquiv 1 w 0 : k) ^ S.roots.pairing a b * s) ^ 2) at h
    have hsq : sq.onPoints w = w ^ 2 := by
      change (npowMorphism (KMult k) 2).toFun w = w ^ 2
      exact npowMorphism_apply _ _ _
    change (f.onPoints w)⁻¹ * rootPoint S a (s ^ 2) * f.onPoints w =
      (S.torus.includePoint ((S.roots.rootCocharacter b).onPoints (sq.onPoints w)))⁻¹ *
        rootPoint S a (s ^ 2) *
        S.torus.includePoint ((S.roots.rootCocharacter b).onPoints (sq.onPoints w))
    rw [hsq, root_conjugation, h, dPointEquiv_pow, mul_pow]
    congr 2
    change ((dPointEquiv 1 w 0 : k) ^ S.roots.pairing a b) ^ 2 =
      ((dPointEquiv 1 w 0 : k) ^ 2) ^ S.roots.pairing a b
    simp only [pow_two, mul_zpow]
  have hz := congrArg (fun e : Theory.AlgebraicGroup.Morphism (KMult k) K => e.onPoints z) he
  change S.frobenius.onPoints (S.torus.includePoint ((S.roots.rootCocharacter b).onPoints z)) =
    S.torus.includePoint ((S.roots.rootCocharacter b).onPoints
      ((npowMorphism (KMult k) 2).toFun z)) at hz
  rwa [npowMorphism_apply] at hz

private def fundamentalCharacter (S : Geometry K) (i : Fin 4) : TorusWeight S.torus :=
  S.weight (Multiplicative.ofAdd (Pi.single i 1))

omit [IsAlgClosed k] in
private theorem weight_expand (S : Geometry K) (a : Weight) :
    S.weight (Multiplicative.ofAdd a) =
      fundamentalCharacter S 0 ^ a 0 * fundamentalCharacter S 1 ^ a 1 *
      fundamentalCharacter S 2 ^ a 2 * fundamentalCharacter S 3 ^ a 3 := by
  unfold fundamentalCharacter
  simp only [← map_zpow S.weight, ← map_mul S.weight]
  congr 1
  change a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 +
    a 2 • Pi.single 2 1 + a 3 • Pi.single 3 1
  funext i
  fin_cases i <;> simp

private theorem torus_point_ext (S : Geometry K) (t u : S.torus.carrierVariety.Point)
    (h : ∀ i, (fundamentalCharacter S i).pointCharacter t =
      (fundamentalCharacter S i).pointCharacter u) : t = u := by
  apply (torusPointEval_bijective S.maximalTorus.1).injective
  apply MonoidHom.ext
  intro χ
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  change torusPointEval _ t (S.weight (Multiplicative.ofAdd a.toAdd)) =
    torusPointEval _ u (S.weight (Multiplicative.ofAdd a.toAdd))
  rw [weight_expand]
  have h' (i : Fin 4) : torusPointEval _ t (fundamentalCharacter S i) =
      torusPointEval _ u (fundamentalCharacter S i) := Units.ext (h i)
  simp only [map_mul, map_zpow, h']

private theorem simple_coroot_decomposition (S : Geometry K) (t : S.torus.carrierVariety.Point) :
    t = (S.roots.rootCocharacter (S.simpleRoot 0).val).onPoints
          ((fundamentalCharacter S 0).onPoints t) *
        (S.roots.rootCocharacter (S.simpleRoot 1).val).onPoints
          ((fundamentalCharacter S 1).onPoints t) *
        (S.roots.rootCocharacter (S.simpleRoot 2).val).onPoints
          ((fundamentalCharacter S 2).onPoints t) *
        (S.roots.rootCocharacter (S.simpleRoot 3).val).onPoints
          ((fundamentalCharacter S 3).onPoints t) := by
  apply torus_point_ext S
  intro i
  simp only [map_mul, fundamentalCharacter, weight_coroot]
  fin_cases i <;> simp [TorusCharacter.pointCharacter]

private theorem preserves_torus_of_coroots (S : Geometry K)
    (f : Theory.AlgebraicGroup.Morphism K K)
    (h : ∀ i : Fin 4, ∀ z : (KMult k).Point,
      f.onPoints (S.torus.includePoint
        ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)) ∈ S.torus) :
    ∀ t : S.torus.carrierVariety.Point, f.onPoints (S.torus.includePoint t) ∈ S.torus := by
  intro t
  rw [simple_coroot_decomposition S t]
  change f.onPoints (S.torus.inclusion.onPoints _) ∈ S.torus
  simp only [map_mul]
  exact S.torus.mul_mem (S.torus.mul_mem (S.torus.mul_mem (h 0 _) (h 1 _)) (h 2 _)) (h 3 _)

/-- The actual diagram automorphism preserves the actual torus. -/
theorem diagram_preserves_torus (S : Geometry K) :
    ∀ t : S.torus.carrierVariety.Point,
      S.diagram.hom.onPoints (S.torus.includePoint t) ∈ S.torus := by
  apply preserves_torus_of_coroots S
  intro i z
  change S.diagram.toMulEquiv _ ∈ S.torus
  rw [diagram_coroot_ambient]
  exact (S.torus.pointEquiv _).property

/-- The actual Frobenius preserves the actual torus. -/
theorem frobenius_preserves_torus (S : Geometry K) :
    ∀ t : S.torus.carrierVariety.Point,
      S.frobenius.onPoints (S.torus.includePoint t) ∈ S.torus := by
  apply preserves_torus_of_coroots S
  intro i z
  rw [frobenius_coroot_ambient]
  exact (S.torus.pointEquiv _).property

/-- Restrict the supplied ambient maps algebraically and recover their
numbered simple-coroot equations, without any additional geometric premise. -/
theorem nonempty_pinnedTorusMaps (S : Geometry K) : Nonempty (PinnedTorusMaps S) := by
  let d := (S.diagram.hom.comp S.torus.inclusion).codRestrictClosedSubgroup S.torus
    (diagram_preserves_torus S)
  let f := (S.frobenius.comp S.torus.inclusion).codRestrictClosedSubgroup S.torus
    (frobenius_preserves_torus S)
  have hd (t : S.torus.carrierVariety.Point) :
      S.torus.includePoint (d.onPoints t) = S.diagram.toMulEquiv (S.torus.includePoint t) :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hf (t : S.torus.carrierVariety.Point) :
      S.torus.includePoint (f.onPoints t) = S.frobenius.onPoints (S.torus.includePoint t) :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  refine ⟨⟨d, f, hd, hf, ?_, ?_⟩⟩
  · intro i z
    apply S.torus.inclusion_injective
    change S.torus.includePoint (d.onPoints _) = S.torus.includePoint _
    rw [hd, diagram_coroot_ambient]
    change S.torus.includePoint
      ((S.roots.rootCocharacter (diagramRoot S (S.simpleRoot i).val)).onPoints z) = _
    rw [diagramRoot_simple]
  · intro i z
    apply S.torus.inclusion_injective
    change S.torus.includePoint (f.onPoints _) = S.torus.includePoint _
    rw [hf, frobenius_coroot_ambient]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
