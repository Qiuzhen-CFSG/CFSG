module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Recognizing the actual quotient of the HS elementary-eight normalizer

The automorphism group of the characteristic elementary eight is identified
with `GL_3(2) = SL_3(2)` using its actual group law and cardinality. The kernel
of normalizer conjugation is its restricted ambient centralizer, already
proved to be a two-group. If the action is surjective, simplicity and order
168 of the target force the image of the normalizer two-core to be trivial.
Thus the action kernel is exactly the two-core, and the first isomorphism
theorem constructs the requested quotient equivalence.

This reduces the remaining model calculation to surjectivity of the actual
normalizer action; that surjectivity is not assumed to follow from a shape
label. Source: GLS3 Table 5.3m, printed p.274, and the faithful action on
`Omega_1(4^3)` on p.306; Aschbacher–Smith 2.3.9(7), printed p.526.
-/

public section

namespace Sporadic.LeechRelated.HS.BlockNormalizer
open Subgroup EvenLocalCandidates

/-- The full automorphism group of the actual elementary eight is the binary special linear group. -/
noncomputable def baseAutomorphismEquiv :
    MulAut baseElementary ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  let : IsElementaryAbelian 2 baseElementary := elementary_isElementaryAbelian 2
  exact (elementaryEight_mulAut_equiv_GL baseElementary baseElementary_card).some.trans
    Matrix.PSL3Two.equivGL.symm

/-- A full action on the elementary eight identifies the two-core with the actual action kernel. -/
theorem baseNormalizer_ker_eq_pCore_of_surjective
    (hact : Function.Surjective baseElementary.normalizerMonoidHom) :
    baseElementary.normalizerMonoidHom.ker = pCore 2 baseNormalizer := by
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (MulAut baseElementary) := baseAutomorphismEquiv.isSimpleGroup
  have hk : IsPGroup 2 baseElementary.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact (large_elementary_centralizer_isPGroup 2 (by decide)).comap_subtype
  have hk_le : baseElementary.normalizerMonoidHom.ker ≤ pCore 2 baseNormalizer :=
    le_sSup ⟨MonoidHom.normal_ker _, hk⟩
  let I := (pCore 2 baseNormalizer).map baseElementary.normalizerMonoidHom
  have hn : I.Normal := Subgroup.Normal.map (pCore_normal (p := 2) (G := baseNormalizer)) _ hact
  have hp : IsPGroup 2 I := pCore_isPGroup.map _
  have hI : I = ⊥ := by
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact hb
    · obtain ⟨n, hn⟩ := hp.exists_card_eq
      have hc : Nat.card I = 168 := by
        rw [ht]
        exact (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (MulAut baseElementary)) ≃*
          MulAut baseElementary).toEquiv).trans
          ((Nat.card_congr baseAutomorphismEquiv.toEquiv).trans Matrix.PSL3Two.card_SL)
      have hthree : 3 ∣ 2 ^ n := hn ▸ hc ▸ (by decide : 3 ∣ 168)
      exact ((by decide : ¬ 3 ∣ 2) ((Nat.prime_three.dvd_of_dvd_pow hthree))).elim
  exact le_antisymm hk_le ((Subgroup.map_eq_bot_iff _).mp hI)

/-- The actual quotient by the two-core is `SL_3(2)` once the conjugation action is surjective. -/
theorem baseNormalizer_quotient_of_surjective
    (hact : Function.Surjective baseElementary.normalizerMonoidHom) :
    Nonempty ((baseNormalizer ⧸ pCore 2 baseNormalizer) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let f : baseNormalizer →* MulAut baseElementary := baseElementary.normalizerMonoidHom
  have he : f.ker = pCore 2 baseNormalizer := baseNormalizer_ker_eq_pCore_of_surjective hact
  let q : (baseNormalizer ⧸ pCore 2 baseNormalizer) ≃* (baseNormalizer ⧸ f.ker) :=
    QuotientGroup.quotientMulEquivOfEq (M := pCore 2 baseNormalizer) (N := f.ker) he.symm
  exact ⟨q.trans ((QuotientGroup.quotientKerEquivOfSurjective f hact).trans
    baseAutomorphismEquiv)⟩
end Sporadic.LeechRelated.HS.BlockNormalizer
