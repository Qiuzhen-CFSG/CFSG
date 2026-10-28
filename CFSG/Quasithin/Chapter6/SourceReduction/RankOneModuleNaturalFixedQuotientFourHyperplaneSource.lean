module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneOdd
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFullReducedOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOmega
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple

/-!
# The original full Hermitian reduced module has global rank greater than one

Normalize each actual escaping hyperplane by an original L-conjugator.
The T-invariant representative is excluded by E.6.13. The nonsingular
representative contains C_B(T) and C_B(N_T(U)); the genuine Sylow kernel
and full reduced omega-center equality then contradict E.6.10(4).

All module, Sylow, odd-centralizer, E.6.1, and fixed-space duties are
constructed from the original hypotheses and the full Hermitian model.
Source: Aschbacher–Smith 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.RankOne
open ChapterE ChapterE.Section06 FourHyperplaneGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n s : ℕ} [NeZero s]
local instance sourceFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance sourceBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

omit [Finite G] in
private theorem hermitian_hyperplane_ne_bot {B U : Subgroup G}
    (hm : IsConjugationModel L B (SL2.BinarySmall.hermitian s))
    (hcor : subgroupCorank B U = 1) : U ≠ ⊥ := by
  intro he
  have hc : Nat.card B = 2 ^ (4*s) := by
    rw [hm.card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      space_binary_finrank]
  rw [he,subgroupCorank,relIndex_bot_left,hc,Nat.log_pow Nat.one_lt_two] at hcor
  have hs := NeZero.ne s
  omega

/-- Every literal binary hyperplane of the full original Hermitian R₂(LT)
has its ambient centralizer in M. All normalization and local-source
hypotheses are discharged on this same full module. -/
theorem full_reduced_hermitian_hyperplane_centralizer_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (U : Subgroup G) (hU : U ≤ reducedSubgroup (L ⊔ (T : Subgroup G)))
    (hcor : subgroupCorank (reducedSubgroup (L ⊔ (T : Subgroup G))) U = 1) :
    centralizer (U : Set G) ≤ M := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  have hE := full_reduced_hermitian_hypothesisE61 h hm
  let := hE.elementary
  have hkernel := full_reduced_hermitian_hyperplane_sylow_centralizer h hout hm hs
  obtain ⟨l,hl,hWB,hWcor,hgeo⟩ := original_hyperplane_conjugate_geometry
    h.sylow_normalizes_L hE.sylow_le_normalizer hm U hU hcor
  let W := U.map (MulAut.conj l).toMonoidHom
  have hWne : W ≠ ⊥ := hermitian_hyperplane_ne_bot hm hWcor
  have hodd : oddCentralizerCondition M B W :=
    oddCentralizerCondition_of_hyperplane_sylow_kernel hE hkernel W hWB hWne hWcor
  have hCW : centralizer (W : Set G) ≤ M := by
    rcases hgeo with hn | ⟨hfixT,hfixN⟩
    · exact InvariantSubspaces.centralizer_le_of_normal_in_sylow_knownSimple hE hWne hWB
        hodd ((normal_subgroupOf_iff_le_normalizer (hWB.trans hE.le_sylow)).mpr hn)
    · have hZ : W ⊓ sylowFixedSpace (T : Subgroup G) B ≠ ⊥ := by
        obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp
          (inf_centerIn_ne_bot T.isPGroup' hE.nontrivial hE.le_sylow hE.sylow_le_normalizer)
        have hzB : (z : G) ∈ B := z.property.1
        have hzC : (z : G) ∈ centralizer (T : Set G) := z.property.2.2
        intro he
        have hzW : (z : G) ∈ W := hfixT ⟨hzB,hzC⟩
        have hz1 : (z : G) = 1 := mem_bot.mp (he ▸ (show (z : G) ∈
          W ⊓ sylowFixedSpace (T : Subgroup G) B from ⟨hzW,hzB,hzC⟩))
        exact hz (Subtype.ext hz1)
      apply four_hyperplane_centralizer_le_of_fixed_space hE hWne hWB hodd hWcor
        (Or.inl hZ) ?_ hfixN
      rw [hkernel W hWB hWcor,full_reduced_hermitian_sylow_centralizer h hm]
      exact h.reduced_enlargement_eq_omega_core
  intro x hx
  have hxW : l*x*l⁻¹ ∈ centralizer (W : Set G) :=
    map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj l).toMonoidHom
      (mem_map_of_mem _ hx)
  have hh := M.mul_mem (M.mul_mem (M.inv_mem (h.L_le hl)) (hCW hxW)) (h.L_le hl)
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hh

/-- The genuine full Hermitian reduced module has global rank greater than
one, for every half-degree s>1, including s=2. -/
theorem full_reduced_hermitian_one_lt_globalR
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s) :
    1 < globalR (reducedSubgroup (L ⊔ (T : Subgroup G))) := by
  have hE := full_reduced_hermitian_hypothesisE61 h hm
  apply lt_of_le_of_ne (one_le_globalR _)
  intro he
  obtain ⟨U,hU,hescape,hcor⟩ := globalR_attained (by rw [←he]; exact ENat.one_ne_top)
  have hc : subgroupCorank (reducedSubgroup (L ⊔ (T : Subgroup G))) U = 1 := by
    exact_mod_cast hcor.trans he.symm
  exact hescape ((hE.centralizer_le_iff (hermitian_hyperplane_ne_bot hm hc) hU).mp
    (full_reduced_hermitian_hyperplane_centralizer_le h hout hm hs U hU hc))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
