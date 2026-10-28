module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.DegreeBounds
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.Geometry
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The prime-degree route to the six pariah FF exclusions

All six degree lower bounds are proved for arbitrary finite central covers.
Under three-conjugate generation, an FF normalizer would force degree at most
three times the automorphism two-rank of the simple quotient. This contradicts
the bounds 18, 18, 36, 28, 18 and 66 for J₁, J₃, J₄, Ru, O'N and Ly.

The six geometric premises below are still explicit proof obligations, not
source hypotheses. In particular this module does not yet prove any of the six
`FaithfulExclusion` contracts unconditionally. The final assembly owner must
supply the actual normalizer generation and rank producers for every carrier.

Source: Aschbacher–Smith B.1.13, printed pp.73–74 / PDF pp.84–85, citing
Guralnick–Malle, Classification of 2F-modules II, Table 2
(DOI 10.1515/9783110198126.117), and I (DOI 10.1016/S0021-8693(02)00526-4).
This alternative reduction uses the elementary prime-degree argument G.7.1(1).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- Apply the image-rank and displacement bounds to a specified actual simple
quotient. All central covers are retained through perfect central descent. -/
theorem exclusion_of_geometry_and_degree
    (name : KnownSimple.SporadicName) (r d : ℕ) (hgap : 3 * r < d)
    (hgeometry : Geometry.{u,v} name r)
    (hdegree : ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
      [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
      (σ : Representation (ZMod 2) L W), Function.Injective σ → σ.IsIrreducible →
      Nonempty (L ⧸ center L ≃* name.Carrier) → d ≤ Module.finrank (ZMod 2) W) :
    FaithfulExclusion.{u,v} name := by
  intro L W _ _ _ _ _ _ σ hf hi he hff
  obtain ⟨hgen, hr⟩ := hgeometry σ hf hi he
  obtain ⟨e⟩ := he
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hk : σ.ker ≤ center L := by
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf]
    exact bot_le
  let := actionImage_quasisimple_of_central_kernel σ hk
  let e' := (simpleQuotientEquivImage σ hk).symm.trans e
  have hrank := automorphism_primeRank_le_quotient_center (E := actionImage σ) 2
  rw [primeRank_equiv 2 (MulAut.congr e')] at hrank
  have hupper := finrank_le_of_ff_normalizer_three_conjugates σ hf hi hgen hff
  have hlower := hdegree σ hf hi ⟨e⟩
  have hbound := (Nat.mul_le_mul_left 3 (hrank.trans hr))
  omega

/-- J₁ exclusion conditional only on its remaining normalizer geometry. -/
theorem j1_exclusion_of_geometry (h : Geometry.{u,v} .j1 3) : FaithfulExclusion.{u,v} .j1 := by
  apply exclusion_of_geometry_and_degree .j1 3 18 (by decide) h
  intro L W _ _ _ _ _ _ σ hf _ he
  exact j1_degree σ hf he.some

/-- J₃ exclusion, including nontrivial central covers, conditional on geometry. -/
theorem j3_exclusion_of_geometry (h : Geometry.{u,v} .j3 5) : FaithfulExclusion.{u,v} .j3 := by
  apply exclusion_of_geometry_and_degree .j3 5 18 (by decide) h
  intro L W _ _ _ _ _ _ σ hf _ he
  exact j3_degree σ hf he.some

/-- J₄ exclusion conditional on three-conjugate generation and two-rank at most 11. -/
theorem j4_exclusion_of_geometry (h : Geometry.{u,v} .j4 11) : FaithfulExclusion.{u,v} .j4 := by
  apply exclusion_of_geometry_and_degree .j4 11 36 (by decide) h
  intro L W _ _ _ _ _ _ σ hf _ he
  exact j4_degree σ hf he.some

/-- Rudvalis exclusion conditional on its remaining normalizer geometry. -/
theorem ru_exclusion_of_geometry (h : Geometry.{u,v} .ru 6) : FaithfulExclusion.{u,v} .ru := by
  apply exclusion_of_geometry_and_degree .ru 6 28 (by decide) h
  intro L W _ _ _ _ _ _ σ hf _ he
  exact ru_degree σ hf he.some

/-- O'Nan exclusion for the projective simple quotient, conditional on geometry. -/
theorem onan_exclusion_of_geometry (h : Geometry.{u,v} .onan 4) : FaithfulExclusion.{u,v} .onan := by
  apply exclusion_of_geometry_and_degree .onan 4 18 (by decide) h
  intro L W _ _ _ _ _ _ σ hf _ he
  exact onan_degree σ hf he.some

/-- Lyons exclusion conditional on its remaining normalizer geometry. -/
theorem ly_exclusion_of_geometry (h : Geometry.{u,v} .ly 4) : FaithfulExclusion.{u,v} .ly := by
  apply exclusion_of_geometry_and_degree .ly 4 66 (by decide) h
  intro L W _ _ _ _ _ _ σ hf _ he
  exact ly_degree σ hf he.some

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
