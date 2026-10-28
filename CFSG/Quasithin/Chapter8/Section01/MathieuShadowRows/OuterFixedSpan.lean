module
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.FixedGeneration
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.OuterSpan.Native
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.MarkedFixedSpan

/-!
# The complete rank-four fixed-span bound for the M22 cocode

Sylow conjugacy reduces to the native setwise-pair Sylow. Its elementary
sixteen-subgroups either lie in the quintet kernel, where four-subgroup
fixed-space generation applies, or have nine independent vectors in the
sum of their element fixed spaces. This discharges the outer cases as well
as the inner cases needed in original 8.1.3; it does not assert all the
stronger centralizer identifications of H.15.5.

Source: Aschbacher--Smith H.15.4(4), H.15.5 and 8.1.3,
printed pp.400--401,713--714, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows

/-- Every elementary rank-four subgroup of the full native Aut(M22) actor
has cocode fixed-space span of codimension at most one. -/
theorem rank_four_fixedSpan_codim (A : Subgroup MathieuCode.m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hr : rank A = 4) :
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1 := by
  have hc : Nat.card A = 16 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have he : rank A = n := by rw [rank,hn,Nat.log_pow Nat.one_lt_two]
    have hn4 : n = 4 := he.symm.trans hr
    rw [hn,hn4]
    rfl
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq MathieuCode.m22PairStabilizer S M22ChapterH.CompatibleSylow.outer
  let f := (MulAut.conj g).toMonoidHom
  have hle : A.map f ≤ M22ChapterH.CompatibleSylow.outer.toSubgroup := by
    have hh := Subgroup.map_mono (f := f) hAS
    change A.map f ≤ (g • S : Sylow 2 MathieuCode.m22PairStabilizer) at hh
    rwa [hg] at hh
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (m22OuterCocodeRepresentation.asGroupHom g)
  have hE (b : MathieuCode.m22PairStabilizer) (v : M22Cocode) :
      E (m22OuterCocodeRepresentation b v) = m22OuterCocodeRepresentation (f b) (E v) := by
    change m22OuterCocodeRepresentation g (m22OuterCocodeRepresentation b v) =
      m22OuterCocodeRepresentation (g*b*g⁻¹) (m22OuterCocodeRepresentation g v)
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  rw [fixedSpaceSpan_codim_map_equivariant m22OuterCocodeRepresentation
    m22OuterCocodeRepresentation f (MulAut.conj g).injective E hE]
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hcard : Nat.card (A.map f) = 16 := (card_map_of_injective (MulAut.conj g).injective).trans hc
  rcases NormalizedShadowRows.OuterSpan.sylow_rank_four_cases (A.map f) hcard hle with hq | hb
  · have hq' : A.map f ≤ K := by
      change A.map f ≤ m22OuterQuintetKernel m22SourceSextet
      rwa [M22ChapterH.Quintet.outerTranslations_eq_core] at hq
    have hindex : (A.map f).relIndex K = 2 := by
      have hh := card_mul_index ((A.map f).subgroupOf K)
      rw [Nat.card_congr (subgroupOfEquivOfLe hq').toEquiv,hcard,
        M22ChapterH.Quintet.core_card] at hh
      change 16 * (A.map f).relIndex K = 32 at hh
      omega
    have hs := fixedSpaceSpan_eq_top_of_fourFixedSpan m22OuterCocodeRepresentation
      hindex quintet_fourFixedSpan_eq_top
    rw [hs,Submodule.finrank_quotient,finrank_top]
    omega
  · exact hb

open ChapterE Chapter7
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The complete rank-four span bound on the original ambient module, including
outer actors and the whole kernel in the literal corank-five family. -/
theorem marked_rank_four_span {T : Subgroup G} {g : G} (h : IsWOffenderAt V T g)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] M22Cocode)
    (hE : ∀ b v, E (automizerRepresentation V b v) = m22OuterCocodeRepresentation (a b) (E v))
    (hfour : rank (inducedAutomizer V (offenderNormalizer V g)) = 4)
    (hw : (globalW V T).toNat = 2) :
    subgroupCorank V (offenderCentralizerSpan V g 5) ≤ 1 := by
  let I := inducedAutomizer V (offenderNormalizer V g)
  let := offender_inducedAutomizer_elementary V g
  let : IsElementaryAbelian 2 (I.map a) := IsElementaryAbelian.map a
  have hr : rank (I.map a) = 4 := (rank_map_injective a ha I).trans hfour
  rw [rank_four_offenderCentralizerSpan_eq h hfour hw,offenderFixedSpan_corank]
  rw [fixedSpaceSpan_codim_map_equivariant (automizerRepresentation V)
    m22OuterCocodeRepresentation a ha E hE]
  exact rank_four_fixedSpan_codim (I.map a) hr
end CFSG.Quasithin.Chapter8.MathieuShadowRows
