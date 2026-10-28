module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveAlpha
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.OrbitSpan
/-!
# The original single symmetric-five moved alpha orbit

The sharp S5 two-conjugate calculation applies on the actual W=[U,O²(H)]
constructed from the original B.5.1 section. The source centralizer and
residual-fixed kernel are retained. Its two fixed spaces generate W,
proving the exact orbit identity without an extra generation assumption.
Source: Aschbacher–Smith B.6.10, C.1.24 and E.2.3(3).
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterC.SymmetricFive BinaryPermutation BinaryPermutation.FiveCentralExtension
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

private theorem symmetric_five_quotient_orbit_span
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : H →* FiveCentralExtension.Sym) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set H))
    (p : Additive U →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hker g v) =
      coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hker g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (U : Set H))
    : conjugateSpanBy (thompsonAlpha (T : Subgroup H)) (pResidual 2 H) =
      U ⊔ (thompsonAlpha (T : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hc : ∀ A, fixedCodim ρ A = fixedCodim (coreRepresentation (Fin 5)) A :=
    source_fixedCodim U T hUT q hq hker p hp he hk hJ
  obtain ⟨a, ha⟩ := source_thompson_conjugate U T hUT q hq hker p hp he hk hJ
  have hK := source_residual_image q hq
  obtain ⟨g, hg, hqg⟩ : ∃ g ∈ pResidual 2 H, q g = a * fiveCycle * a⁻¹ := by
    exact (hK ▸ conjugate_fiveCycle_even a : a * fiveCycle * a⁻¹ ∈ (pResidual 2 H).map q)
  have himage : ((elementaryAbelianMaxJ (T : Subgroup H)).map (MulAut.conj g).toMonoidHom).map q =
      ((elementaryAbelianMaxJ (T : Subgroup H)).map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hgen : (pResidual 2 H).map q ≤ (elementaryAbelianMaxJ (T : Subgroup H)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup H)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [himage, ha, hqg, two_conjugate_four_groups_generate]
    exact le_top
  have hcod : 2 * BaumannArgument.fixedCodim U (elementaryAbelianMaxJ (T : Subgroup H)) ≤
      BaumannArgument.fixedCodim U (pResidual 2 H) := by
    rw [BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,
      BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,
      hc, hc, ha, fixedCodim_map_conj, hK, fixedCodim_alternating,
      ChapterB.Offenders.Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl]
  have hα := (source_alpha_and_saturation T hP U hU q hq hker p hp he hk hJ).2.1
  exact RankOneBaumann.thompsonAlpha_span_of_two_conjugates T U q hq hker
    g hg hgen hcod (hα.trans (sup_comm _ _))

theorem quasisimple_five_source_orbit_span
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := quasisimple_five_source_marker T hP U hU hJ q hq hker hqs s e
  let W := (⁅U,pResidual 2 G⁆ : Subgroup G)
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq (hU.centralizer_moved_eq U))
  have hfixed : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation W p hp hk g v = v := by
    intro v hv g hg
    have hh : v ∈ fixedSpace (NormalElementaryQuotient.representation W p hp hk)
        (alternatingGroup (Fin 5)) := by
      rw [← ChapterC.SymmetricFive.source_residual_image p hp,← hfk]
      exact hv
    exact hh ⟨g,hg⟩
  exact symmetric_five_quotient_orbit_span T hP W (hU.moved U)
    p hp hk f hf he hfixed hJW
end CFSG.Quasithin.ChapterE.ThompsonAction
