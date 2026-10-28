module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperNatural
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperAction

/-!
# TerminalComponentProperNatural at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperNatural`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode BinaryPermutation

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

end Setup.NaturalCoordinates

namespace SylowNormalizer.Points

variable {E : S.NaturalCoordinates} (P : Points E)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode BinaryPermutation

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}

namespace Setup

variable (S : Setup T L V)

theorem omega_commutator_le_chosen_moved_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hsplit : S.NaturalOmegaDecomposition) (B : Subgroup G) (hBL : B ≤ L) :
    ⁅omegaCenterIn (T : Subgroup G),B⁆ ≤ ⁅V,B⁆ := by
  let C := omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hCN : C ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le S.chosen.le_component)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZ : omegaCenterIn (T : Subgroup G) ≤
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
    intro z hz
    obtain ⟨hzT,hzC,hz2⟩ := (mem_omegaCenterIn_iff _ _).mp hz
    have hzQ : z ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
      exact ⟨hzT,centralizer_le S.chosen.le_sylow hzC⟩
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hzQ,centralizer_le (Setup.NaturalCoordinates.subjoin_core_le_sylow L) hzC,hz2⟩
  apply commutator_le.mpr
  intro z hz b hb
  have hzs : z ∈ V ⊔ C := hsplit ▸ hZ hz
  change z ∈ (↑(V ⊔ C) : Set G) at hzs
  rw [coe_mul_of_right_le_normalizer_left V C hCN] at hzs
  obtain ⟨v,hv,c,hc,rfl⟩ := hzs
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 b (hBL hb)).symm,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hv hb

end Setup

private def coreFiveNaturalEquiv_at :
    alternatingCoreRepresentation (Fin 5) ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
  .mk (coreEquivNatural (Fin 5) (by decide)) (by
    intro g
    apply LinearMap.ext
    intro v
    exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem natural_in_overcomponent_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (R : P.ResidualAnalysis)
    {Y W : Subgroup G} (hKY : P.K ≤ Y)
    (SY : Setup T Y W) (DY : SY.LocalAnalysis) :
    ∃ q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5),
      Nonempty (BinaryConjugationSection P.K ⁅P.Z,P.K⁆ ⊥ (P.residualNaturalAction q)) := by
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect R.local_mem
  obtain ⟨v,hv,hvc,hK⟩ := DY.exists_central_weight_two_residual_at structural P.K hKY
    P.sylow_normalizes_residual R.quotient
  let E : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates,fun l v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨l,SY.chosen.normalizes l.property⟩ v⟩
  obtain ⟨z,hz,hzc⟩ := E.central_representative_weight_at structural (n := 6)
    (Or.inr (Or.inr rfl))
  let Q : SylowNormalizer.Points E := ⟨v,z,hv,hz,hvc,hzc⟩
  have hs : SY.NaturalOmegaDecomposition :=
    (E.core_omega_decomposition_of_weight_six_at structural escape (by
      intro x _ hx
      apply DY.pointCentralizers x ?_ (Or.inr hx)
      intro he
      have hh : weight (E.coordinates (1 : W)).toAdd.val = 0 := by
        simp only [map_one];rfl
      rw [he] at hx
      omega)).1
  have hKQ : P.K = Q.five := hK
  have hle : ⁅P.Z,P.K⁆ ≤ ⁅W,Q.five⁆ := by
    rw [← hKQ]
    exact SY.omega_commutator_le_chosen_moved_at structural hs P.K hKY
  let ρ := (alternatingCoreRepresentation (Fin 5)).comp
    (Q.fiveCoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Q.five)))
  let : (alternatingCoreRepresentation (Fin 5)).IsIrreducible :=
    coreFiveNaturalEquiv_at.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff
    (Q.fiveCoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Q.five)))
    (Q.fiveCoreEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    (alternatingCoreRepresentation (Fin 5))).mpr inferInstance
  have heq : ⁅P.Z,P.K⁆ = ⁅W,Q.five⁆ := by
    apply (Q.five_moved_natural.eq_kernel_or_section ⁅P.Z,P.K⁆ bot_le hle ?_).resolve_left
      (P.omega_commutator_ne_bot_at structural)
    rw [← hKQ]
    exact normalizer_commutator_ge_right P.Z P.K
  have hout : ∃ q : (Q.five ⧸ pCore 2 Q.five) ≃* alternatingGroup (Fin 5),
      Nonempty (BinaryConjugationSection Q.five ⁅P.Z,Q.five⁆ ⊥
        ((alternatingCoreRepresentation (Fin 5)).comp
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Q.five))))) := by
    refine ⟨Q.fiveCoreEquiv,?_⟩
    rw [← hKQ] at heq
    have heq' : ⁅P.Z,Q.five⁆ = ⁅W,Q.five⁆ := by simpa only [hKQ] using heq
    rw [heq']
    exact ⟨Q.five_moved_natural⟩
  have transport (B : Subgroup G) (hB : B = Q.five) :
      ∃ q : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5),
        Nonempty (BinaryConjugationSection B ⁅P.Z,B⁆ ⊥
          ((alternatingCoreRepresentation (Fin 5)).comp
            (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))))) := by
    subst B
    exact hout
  exact transport P.K hKQ

theorem componentAnalysis_of_residual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (R : P.ResidualAnalysis) : Nonempty P.ComponentAnalysis := by
  have hn := P.pointCentralizer_normalizes_of_residual_at structural escape localAnalysis_at R
  have hJ := P.thompson_generation_of_residual_at structural escape localAnalysis_at R
  obtain ⟨F⟩ := P.overcomponents_nonempty R.local_mem
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  by_cases he : P.K = F.Y
  · have hm : P.K ∈ Chapter1.LStar G (T : Subgroup G) := he.symm ▸ F.maximal
    obtain ⟨_,⟨hnat⟩⟩ := P.maximal_action_at R.quotient
      ⟨hm,(R.overgroups P.K hm le_rfl).1⟩ (R.maximal_natural hm)
    exact ⟨⟨hn,R.quotient,hJ,hnat⟩⟩
  · obtain ⟨W,⟨SY⟩⟩ := (R.overgroups F.Y F.maximal hKY).2.resolve_left he
    obtain ⟨DY⟩ := localAnalysis_at F.Y W SY
    obtain ⟨q,⟨hnat⟩⟩ := P.natural_in_overcomponent_at structural escape R hKY SY DY
    exact ⟨⟨hn,q,hJ,hnat⟩⟩

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

