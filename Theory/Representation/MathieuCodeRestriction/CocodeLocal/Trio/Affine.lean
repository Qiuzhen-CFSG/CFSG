module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.Representation.BinaryPermutation

/-!
# The intrinsic two-core and quotient of the standard trio stabilizer

The proved native affine coverage and lifts give a surjection to S₃ × SL₃(2)
whose kernel is a two-group. Each quotient factor has trivial two-core, so
this translation kernel is the intrinsic two-core of the stabilizer. The
first isomorphism theorem and the checked SL₃(2)/PSL₃(2) comparison identify
the actual quotient with L₃(2) × S₃. The coordinate criterion identifies exactly
which native elements lie in this two-core.

The natural three-space, the even core on three letters, and their tensor
product specify concrete target actions for the cocode middle section. This
module does not assert an intertwining equivalence with that section.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.14.1(3),
printed p.396, and H.15.6(3), printed p.401; Aschbacher, *Sporadic Groups*,
Lemma 20.2. Existing native coordinate proofs and the licensed ATLAS matrix
comparison are reused; see `LICENSES/ATLAS.txt` for the latter's license.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open scoped MatrixGroups TensorProduct
namespace MathieuCode.TrioCalculation
noncomputable section

/-- The checked affine quotient on the actual standard-trio stabilizer. -/
def standardAffineHom : trioStabilizer standardTrio →* QuotientModel :=
  affineQuotient affineCoverage

lemma standardAffineHom_surjective : Function.Surjective standardAffineHom :=
  affineQuotient_surjective affineCoverage affineLifts

private lemma symmetricThree_twoCore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three
    (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
    (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
  simpa only [MonoidHom.ker_id] using h.symm

private lemma slThree_twoCore : pCore 2 SL(3, ZMod 2) = ⊥ := by
  let :=  Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : (pCore 2 SL(3, ZMod 2)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp := pCore_isPGroup (p := 2) (G := SL(3, ZMod 2))
    rw [h] at hp
    have hG : IsPGroup 2 SL(3, ZMod 2) := hp.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hn
    have hc := (by decide : Nat.Coprime 2 3).pow_left n
    rw [← hn] at hc
    norm_num at hc

lemma affineModel_twoCore : pCore 2 QuotientModel = ⊥ := by
  rw [Subgroup.pCore_prod, symmetricThree_twoCore, slThree_twoCore, Subgroup.bot_prod_bot]

/-- The affine translation kernel is precisely the intrinsic two-core. -/
lemma standardAffineHom_ker :
    standardAffineHom.ker = pCore 2 (trioStabilizer standardTrio) := by
  have h := standardAffineHom.comap_pCore_of_ker_isPGroup
    standardAffineHom_surjective (affineQuotient_kernel_isPGroup affineCoverage)
  simpa only [affineModel_twoCore, MonoidHom.comap_bot] using h

/-- Both factors are retained, with the literal quotient by the intrinsic two-core. -/
def standardQuotientEquiv :
    (trioStabilizer standardTrio ⧸ pCore 2 (trioStabilizer standardTrio)) ≃*
      QuotientModel :=
  (QuotientGroup.quotientMulEquivOfEq standardAffineHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective standardAffineHom standardAffineHom_surjective)

/-- The quotient in the source order, using the actual projective matrix factor. -/
def standardSourceQuotientEquiv :
    (trioStabilizer standardTrio ⧸ pCore 2 (trioStabilizer standardTrio)) ≃*
      (PSL(3, ZMod 2) × Equiv.Perm (Fin 3)) :=
  standardQuotientEquiv.trans ((MulEquiv.prodComm).trans
    (MulEquiv.prodCongr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two (MulEquiv.refl _)))

lemma standardQuotientEquiv_mk (g : trioStabilizer standardTrio) :
    standardQuotientEquiv (QuotientGroup.mk g) = standardAffineHom g := rfl

/-- Membership in the intrinsic two-core is the pure-translation condition. -/
lemma mem_standardTwoCore_iff (g : trioStabilizer standardTrio) :
    g ∈ pCore 2 (trioStabilizer standardTrio) ↔
      ∃ t : Fin 3 → Vector, ∀ i v, g.val.val (point (i,v)) = point (i, v + t i) := by
  rw [← standardAffineHom_ker]
  constructor
  · intro hg
    obtain ⟨t, ht⟩ := affineQuotient_spec affineCoverage g
    have hq : affineQuotient affineCoverage g = 1 := hg
    rw [hq] at ht
    exact ⟨t, by simpa [HasAffineForm] using ht⟩
  · rintro ⟨t, ht⟩
    change standardAffineHom g = 1
    exact affineQuotient_eq affineCoverage (show HasAffineForm g 1 t by
      simpa [HasAffineForm] using ht)

/-- The natural three-space of the linear quotient factor. -/
def quotientNaturalThree : Representation (ZMod 2) QuotientModel Vector where
  toFun q := (Matrix.SpecialLinearGroup.toLin' q.2).toLinearMap
  map_one' := by ext v i; simp
  map_mul' q r := by
    change (Matrix.SpecialLinearGroup.toLin' (q.2 * r.2)).toLinearMap = _
    rw [map_mul]
    rfl

/-- The natural two-space of S₃, realized as the even core on its three letters. -/
def quotientNaturalTwo :
    Representation (ZMod 2) QuotientModel (BinaryPermutation.core (Fin 3)) :=
  (BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.fst _ _)

/-- The source tensor module, with both quotient factors acting. -/
abbrev NaturalTensor := QuotientConstruction.Vector ⊗[ZMod 2] (BinaryPermutation.core (Fin 3))

def quotientTensorRepresentation : Representation (ZMod 2) QuotientModel NaturalTensor :=
  quotientNaturalThree.tprod quotientNaturalTwo

/-- The tensor action pulled back along the actual native quotient map. -/
def standardTensorRepresentation :
    Representation (ZMod 2) (trioStabilizer standardTrio) NaturalTensor :=
  quotientTensorRepresentation.comp standardAffineHom

end
end MathieuCode.TrioCalculation
