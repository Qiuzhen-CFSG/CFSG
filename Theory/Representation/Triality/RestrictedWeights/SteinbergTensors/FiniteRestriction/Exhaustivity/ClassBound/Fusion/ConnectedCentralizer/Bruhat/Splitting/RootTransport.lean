module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.Inputs
public import Theory.AlgebraicGroup.RootSubgroups.MultiplicityOne
public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-!
# Normalizer characters and actual D4 root-subgroup transport

The specified simple-reflection lifts determine the action of every actual
normalizer element on root characters: extend the point formula along a word
in the simple reflections. Pulling a parametrization back along conjugation
then proves the root-weight equation for the actual conjugated closed subgroup.
Root-subgroup uniqueness identifies it with the subgroup at the Weyl image.

The character and root-weight-equation results use only `Geometry` and the
explicit `NormalizerRealization`. The final subgroup equalities are conditional
on root-subgroup uniqueness or operational multiplicity one; this module does
not yet derive either condition from `Geometry`.

Source: GLS3 1.9.5(b),(f) and 1.11.5, `refs/KGroup/GLS3/Chapter1.tex`;
Steinberg 6.1--6.4, `refs/KGroup/GLS3/Chapter2St2.tex`. Conjugated subgroups here
use `n X n⁻¹`, while root characters use the raw inverse-conjugation equation.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open AmbientCount.TorusGeometry
namespace ConnectedCentralizer.Bruhat.Splitting
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- The identity Weyl element fixes every realized root. -/
theorem rootAction_one (S : Geometry K) (a : S.roots.Root) :
    rootAction S 1 a = a := by
  simp [rootAction]

/-- The root-index action has the same multiplication order as conjugation. -/
theorem rootAction_mul (S : Geometry K) (w v : AmbientCount.Weyl)
    (a : S.roots.Root) :
    rootAction S (w * v) a = rootAction S w (rootAction S v a) := by
  simp [rootAction]

/-- A numbered simple reflection acts by the realized root reflection. -/
theorem rootAction_simple (S : Geometry K) (i : Fin 4) (a : S.roots.Root) :
    rootAction S (RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
      (typeDSimpleRootIndex 2 i)) a = S.roots.reflect (S.simpleRoot i).val a := by
  apply S.rootIndex.injective
  rw [S.based.2.1, S.simpleRoot_index]
  simp only [rootAction, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- The actual simple-coroot point formula induces the realized root reflection
on inverse-conjugation characters. -/
theorem rootWeight_simpleReflection (S : Geometry K) (i : Fin 4)
    (a : S.roots.Root) (t : Variety.Point S.torus.carrierVariety) :
    (S.roots.rootWeight a).pointCharacter (simpleReflection S i t) =
      (S.roots.rootWeight (S.roots.reflect (S.simpleRoot i).val a)).pointCharacter t := by
  rw [simpleReflection, map_mul, map_inv,
    S.realized.rootWeight_rootCocharacter]
  rw [S.realized.2.2.2.2.2.1]
  change _ = ((torusPointEval S.torus.carrierVariety t
    (S.roots.rootWeight a * S.roots.rootWeight (S.simpleRoot i).val ^
      (-S.roots.pairing a (S.simpleRoot i).val))) : k)
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg]
  rfl

/-- The actual normalizer-induced Weyl action and the root-index action preserve
character evaluation. Simple-reflection formulas extend along a Weyl word. -/
theorem rootWeight_weyl (S : Geometry K) (R : NormalizerRealization S)
    (w : AmbientCount.Weyl) (a : S.roots.Root)
    (t : Variety.Point S.torus.carrierVariety) :
    (S.roots.rootWeight (rootAction S w a)).pointCharacter (R.perm w t) =
      (S.roots.rootWeight a).pointCharacter t := by
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l generalizing a t with
  | nil => simp [rootAction_one]
  | cons j l ih =>
    rw [RootPairing.Base.wordProd_cons, rootAction_mul, map_mul,
      Equiv.Perm.mul_apply]
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    let s := (typeDRootPairing_base 2).simpleReflection
      (typeDRootPairing_baseEquiv 2 i)
    have hperm (z : Variety.Point S.torus.carrierVariety) :
        R.perm s z = simpleReflection S i z := R.reflection_point i z
    rw [hperm, rootWeight_simpleReflection, ← rootAction_simple]
    have hs : s * s = 1 := RootPairing.Base.simpleReflection_mul_self _ _
    change (S.roots.rootWeight (rootAction S s (rootAction S s _))).pointCharacter _ = _
    rw [← rootAction_mul, hs, rootAction_one]
    exact ih a t

/-- Pulling a root character back along inverse normalizer conjugation gives
the character of the forward Weyl image. -/
theorem rootWeight_normalizer_inverse (S : Geometry K)
    (R : NormalizerRealization S) (n : TorusNormalizer S)
    (a : S.roots.Root) (t : Variety.Point S.torus.carrierVariety) :
    (S.roots.rootWeight a).pointCharacter (normalizerPerm S n⁻¹ t) =
      (S.roots.rootWeight (rootAction S (R.toWeyl n) a)).pointCharacter t := by
  have h := rootWeight_weyl S R (R.toWeyl n) a
    (R.perm ((R.toWeyl n)⁻¹) t)
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  rw [← map_inv R.toWeyl, R.perm_toWeyl] at h
  exact h.symm

/-- The actual conjugated closed root subgroup has the character prescribed by
the normalizer Weyl label. This conclusion does not yet identify the subgroup. -/
theorem conjugate_rootWeightEquation (S : Geometry K)
    (R : NormalizerRealization S) (n : TorusNormalizer S) (a : S.roots.Root) :
    RootWeightEquation S.torus
      ((S.roots.rootSubgroup a).conjugate (n : Variety.Point K))
      (S.roots.rootWeight (rootAction S (R.toWeyl n) a)) := by
  intro y t s
  let X := S.roots.rootSubgroup a
  let g : Variety.Point K := n
  let e := X.conjugateIso g
  let x : OneParameterParametrization X.carrierVariety :=
    { hom := e.inv.comp y.hom
      inv := y.inv.comp e.hom
      hom_inv_id := by
        intro z
        change y.inv.onPoints (e.hom.onPoints
          (e.inv.onPoints (y.hom.onPoints z))) = z
        rw [e.inv_hom_id, y.hom_inv_id]
      inv_hom_id := by
        intro z
        change e.inv.onPoints (y.hom.onPoints
          (y.inv.onPoints (e.hom.onPoints z))) = z
        rw [y.inv_hom_id, e.hom_inv_id] }
  let s₀ := normalizerPerm S n⁻¹ s
  have hs : S.torus.includePoint s₀ =
      g⁻¹ * S.torus.includePoint s * g := by
    simpa only [Subgroup.coe_inv, inv_inv] using normalizerPerm_include S n⁻¹ s
  have hy (c : k) : X.includePoint (x.value c) =
      g⁻¹ * (X.conjugate g).includePoint (y.value c) * g :=
    X.conjugateIso_inv_inclusion_apply g (y.value c)
  have hw : (S.roots.rootWeight a).pointCharacter s₀ =
      (S.roots.rootWeight (rootAction S (R.toWeyl n) a)).pointCharacter s :=
    rootWeight_normalizer_inverse S R n a s
  apply (MulAut.conj g⁻¹).injective
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  calc
    _ = (S.torus.includePoint s₀)⁻¹ * X.includePoint (x.value t) *
        S.torus.includePoint s₀ := by
      rw [hs, hy]
      dsimp only [X, g]
      group
    _ = X.includePoint (x.value ((S.roots.rootWeight a).pointCharacter s₀ * t)) :=
      (S.realized.2.2.1 a).2 x t s₀
    _ = _ := by rw [hy, hw]

/-- Root-subgroup uniqueness supplies the remaining geometric step from the
proved character comparison to equality of actual closed subgroups. -/
theorem rootTransport_of_unique (S : Geometry K) (R : NormalizerRealization S)
    (hunique : ∀ {X : ClosedSubgroup K} {a : S.roots.Root},
      IsTorusRootSubgroup S.torus X →
      RootWeightEquation S.torus X (S.roots.rootWeight a) →
      X = S.roots.rootSubgroup a) : RootTransport S R.toWeyl := by
  intro n a
  exact hunique (a := rootAction S (R.toWeyl n) a)
    (IsTorusRootSubgroup.conjugate_of_mem_normalizer
      (n : Variety.Point K) n.property (S.realized.2.2.1 a).1)
    (conjugate_rootWeightEquation S R n a)

/-- Operational root-weight multiplicity one is sufficient for subgroup
transport. Its derivation from `Geometry` remains a separate obligation. -/
theorem rootTransport_of_multiplicityOne (S : Geometry K) (R : NormalizerRealization S)
    (hmult : ∀ a : S.roots.Root,
      RootWeightSpaceMultiplicityOne S.torus (S.roots.rootWeight a)) :
    RootTransport S R.toWeyl := by
  apply rootTransport_of_unique S R
  intro X a hX hweight
  exact RootWeightSpaceMultiplicityOne.rootSubgroup_eq (hmult a) hX hweight
    (S.realized.2.2.1 a).1 (S.realized.2.2.1 a).2

end ConnectedCentralizer.Bruhat.Splitting
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
