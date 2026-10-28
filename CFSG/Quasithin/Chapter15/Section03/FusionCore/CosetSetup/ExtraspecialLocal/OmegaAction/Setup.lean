module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.Residual
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.GroupTheory.CommutatorPreimageTransport
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The actual local quotient centralizer in 15.3.49

The residual calculation identifies Y₀ with θ(M ∩ H). Since T lies in
M ∩ H, it normalizes Y₀ and its characteristic two-core. Thus the
commutator preimage really is the centralizer of Y₀/O₂(Y₀), computed in
the relative overgroup Y₀T. No ambient normality is required.

`centerFixingImage` records the image of the pointwise center stabilizer
for a specified automorphism action of an orthogonal Sylow image. It is
the common interface for constructing the actual extraspecial action and
computing its center stabilizer. Neither calculation is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 and the calculation after 15.3.49(b), printed pp.1122 and 1143.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

open Subgroup Stellmacher

variable {G : Type*} [Group G]

/-- The center-fixing part of a specified action, embedded in the actual
orthogonal actor. This definition includes the action homomorphism. -/
def centerFixingImage (P : Subgroup OrthogonalActor)
    {F : Type*} [Group F] (ρ : P →* MulAut F) : Subgroup OrthogonalActor :=
  ((fixingSubgroup (MulAut F) (center F : Set F)).comap ρ).map P.subtype

/-- The relative two-core is normalized by the residual and every actor
normalizing that residual. -/
theorem local_core_normalization (T Y₀ : Subgroup G)
    (hTY : T ≤ normalizer (Y₀ : Set G)) :
    Y₀ ⊔ T ≤ normalizer (Y₀.pCoreIn 2 : Set G) := by
  exact sup_le
    (Y₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y₀ (pCore 2 Y₀)))
    (hTY.trans (normalizer_le_normalizer_characteristic_image Y₀ (pCore 2 Y₀)))

/-- In the local overgroup, the commutator preimage is literally the
inverse image of the quotient centralizer. -/
theorem local_quotientCentralizer_eq (T Y₀ : Subgroup G)
    (hTY : T ≤ normalizer (Y₀ : Set G)) :
    let L := Y₀ ⊔ T
    let K := (Y₀.pCoreIn 2).subgroupOf L
    let _ : K.Normal := normal_subgroupOf_of_le_normalizer
      (local_core_normalization T Y₀ hTY)
    (commutatorPreimage T Y₀ (Y₀.pCoreIn 2)).subgroupOf L =
      T.subgroupOf L ⊓
        (centralizer ((Y₀.subgroupOf L).map (QuotientGroup.mk' K) :
          Set (L ⧸ K))).comap (QuotientGroup.mk' K) := by
  dsimp only
  let _ := normal_subgroupOf_of_le_normalizer (local_core_normalization T Y₀ hTY)
  rw [commutatorPreimage_subgroupOf T Y₀ (Y₀.pCoreIn 2) (Y₀ ⊔ T)
    le_sup_right le_sup_left (local_core_normalization T Y₀ hTY)]
  exact commutatorPreimage_eq_inf_comap_centralizer _ _ _

/-- The genuine 15.3.7 inputs and the already proved residual calculation
supply all normalization required for the quotient centralizer. -/
theorem extraspecial_local_normalization [Finite G]
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (h : ExtraspecialCase M Y V)
    (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    (T : Subgroup G) ≤ normalizer (Y₀ : Set G) ∧
      Y₀ ⊔ (T : Subgroup G) ≤ normalizer (Y₀.pCoreIn 2 : Set G) ∧
      (T : Subgroup G) ≤ normalizer
        (commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2) : Set G) := by
  let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
  have hY₀ := (extraspecial_local_algebra M Mc H Y V T hYM h hM hTM hTH hH hCH hfactor).2.1
  have hTY : (T : Subgroup G) ≤ normalizer (Y₀ : Set G) := by
    rw [show Y₀ = theta (M ⊓ H) from hY₀]
    exact (le_inf hTM hTH).trans
      ((M ⊓ H).le_normalizer.trans (normalizer_le_normalizer_theta _))
  have hL := local_core_normalization (T : Subgroup G) Y₀ hTY
  exact ⟨hTY, hL, commutatorPreimage_normalized _ _ _ _
    (le_sup_right.trans hL) T.le_normalizer hTY (le_sup_right.trans hL)⟩

/-- The image of the specified Sylow subgroup is Sylow in the specified
natural orthogonal action. -/
def orthogonalSylowImage [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) : Sylow 2 OrthogonalActor :=
  (T.subtype hTM).mapSurjective d.onto

theorem orthogonalSylowImage_coe [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) :
    (orthogonalSylowImage d T hTM : Subgroup OrthogonalActor) = d.image (T : Subgroup G) :=
  rfl

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
