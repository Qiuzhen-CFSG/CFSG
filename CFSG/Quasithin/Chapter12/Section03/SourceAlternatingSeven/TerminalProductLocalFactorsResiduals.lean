module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsStabilizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductCubic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperLeCubics
public import Theory.GroupTheory.PResidual.PrimeToProduct
public import Theory.GroupTheory.PResidual.PrimeToPerfect

/-!
# The two prime-to-three residuals in the original point normalizer

Cubic generation identifies O²(C_L(e)) with O^{3′}(C_L(e)). The source
normalizer residual then identifies it with O^{3′}(N_G(V)∩C_G(e)). Apply
the normal-product residual theorem to the two actual block preimages:
their embedded prime-to-three residuals generate the literal L_e.

The subsequent identifications with the published L₁ and L₂ remain the
local geometry obligation of qt-d-1231-terminal-product. ComponentAnalysis
is the allowed 12.3.12 input, discharged by qt-d-1231-terminal.
Source: Aschbacher--Smith, paragraph preceding 12.3.13, printed p.811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- Cubic generation identifies both source residual conventions in C_L(e). -/
theorem Le_eq_point_primeToResidual :
    P.Le = (primeToResidual 3 (L ⊓ P.pointCentralizer : Subgroup G)).map
      (L ⊓ P.pointCentralizer).subtype := by
  apply le_antisymm
  · rw [←P.Le_cubic_generated]
    apply (closure_le _).mpr
    rintro x ⟨hx,h3⟩
    have hxC : x ∈ L ⊓ P.pointCentralizer := map_subtype_le _ hx
    let y : (L ⊓ P.pointCentralizer : Subgroup G) := ⟨x,hxC⟩
    have hy : y ^ (3 ^ 1) = 1 := by
      apply Subtype.ext
      change x ^ (3 ^ 1) = 1
      simpa only [pow_one,h3] using (pow_orderOf_eq_one x)
    exact mem_map_of_mem _ (mem_primeToResidual_of_pow hy)
  · apply map_mono
    exact le_pResidual_of_isPPerfect (primeToResidual 3 (L ⊓ P.pointCentralizer : Subgroup G))
      (isPPerfect_primeToResidual 3 2 (by decide))

/-- The literal L_e is O^{3′} of the full original point normalizer. -/
theorem Le_eq_pointNormalizer_primeToResidual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    P.Le = (primeToResidual 3 P.pointNormalizer).map P.pointNormalizer.subtype := by
  have h := embedded_primeToResidual_intersection 3
    (normalizer (L : Set G)) P.pointNormalizer
  rw [P.normalizer_residual C,
    inf_eq_right.mpr (P.pointNormalizer_le_original structural)] at h
  have he : L ⊓ P.pointNormalizer = L ⊓ P.pointCentralizer := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans S.chosen.normalizes) inf_le_right)
  rw [he] at h
  exact P.Le_eq_point_primeToResidual.trans h

/-- The actual residual of the factor acting on the four support letters. -/
def firstPointResidual : Subgroup G :=
  (primeToResidual 3 P.firstPointFactor).map P.firstPointFactor.subtype

/-- The actual residual of the factor acting on the three complementary letters. -/
def secondPointResidual : Subgroup G :=
  (primeToResidual 3 P.secondPointFactor).map P.secondPointFactor.subtype

/-- The two source residual factors generate the literal L_e.
Identifying them with the terminal L₁ and L₂ is a subsequent geometric step. -/
theorem Le_eq_pointResidual_sup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Le = P.firstPointResidual ⊔ P.secondPointResidual := by
  let M := P.pointNormalizer
  let A := P.firstPointFactor.subgroupOf M
  let B := P.secondPointFactor.subgroupOf M
  have hAM : P.firstPointFactor ≤ M := map_subtype_le _
  have hBM : P.secondPointFactor ≤ M := map_subtype_le _
  let : A.Normal := normal_subgroupOf_of_le_normalizer P.firstPointFactor_normalized
  let : B.Normal := normal_subgroupOf_of_le_normalizer P.secondPointFactor_normalized
  have hgen : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup hAM hBM,←P.pointNormalizer_eq_factor_sup structural escape]
    exact subgroupOf_self _
  have h := congrArg (map M.subtype)
    (primeToResidual_eq_sup_of_normal_generators 3 A B hgen)
  rw [Subgroup.map_sup,map_embedded_primeToResidual_of_hom,
    map_embedded_primeToResidual_of_hom,
    map_subgroupOf_eq_of_le hAM,map_subgroupOf_eq_of_le hBM] at h
  exact (P.Le_eq_pointNormalizer_primeToResidual structural C).trans h

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
