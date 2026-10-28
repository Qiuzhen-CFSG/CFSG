module

public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.GroupTheory.SolvableResidual

/-!
# The marked covered long-root residual

An actual equivalence from the central quotient to the octonion G₂ model
fixes the marking. Pull back its highest-root group to Z₁, form
Z = [N_L(Z₁), Z₁], and take the solvable residual of N_L(Z).
Every normalizer and commutator here is internal to L.

The marking may absorb conjugation in the model, so it accommodates any
long-root group. These definitions make no local-structure assertion about
the cover. In particular they do not identify its Frattini subgroup.

Source: Aschbacher–Smith, Lemma 16.5.13, printed pp.1201–1202.
The highest-root normalizer is `parabolic₁` in the model conventions;
the files `LieShortParabolic` refer to its Weyl generator.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.CoverModel
open Subgroup
variable {L F : Type*} [Group L] [Field F]

/-- The literal central projection followed by the specified model equivalence. -/
def projection (e : (L ⧸ center L) ≃* Atlas.G2.Model F) : L →* Atlas.G2.Model F :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center L))

theorem projection_surjective (e : (L ⧸ center L) ≃* Atlas.G2.Model F) :
    Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem projection_ker (e : (L ⧸ center L) ≃* Atlas.G2.Model F) :
    (projection e).ker = center L := by
  ext x
  change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- Z₁ is the full inverse image of the marked highest-root group. -/
def rootPreimage (e : (L ⧸ center L) ≃* Atlas.G2.Model F) : Subgroup L :=
  (Atlas.G2.LieParabolicSetup.highestRoot (F := F)).comap (projection e)

/-- The source's modified root subgroup in the exceptional cover. -/
def root (e : (L ⧸ center L) ≃* Atlas.G2.Model F) : Subgroup L :=
  ⁅normalizer (rootPreimage e : Set L), rootPreimage e⁆

/-- The actual normalizer of the modified root subgroup. -/
def parabolic (e : (L ⧸ center L) ≃* Atlas.G2.Model F) : Subgroup L :=
  normalizer (root e : Set L)

/-- P∞, embedded in L through the actual subgroup inclusion. -/
def residual (e : (L ⧸ center L) ≃* Atlas.G2.Model F) : Subgroup L :=
  (solvableResidual (parabolic e)).map (parabolic e).subtype

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.CoverModel
