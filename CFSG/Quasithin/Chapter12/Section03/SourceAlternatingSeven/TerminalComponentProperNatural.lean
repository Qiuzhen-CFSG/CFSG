module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperAction
public import Theory.Representation.BinarySevenCode.WeightTwoNatural
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.NormalInvariants
public import Theory.Representation.RepEquiv
public import Theory.Representation.Quotient

/-!
# The natural action of the terminal A₅ component

The five-letter augmentation core is the entire moved subgroup of a weight-two
point residual in the original seven-letter module, through its marked two-core
quotient. The source omega-centre splitting then places `[Z,K]` in that subgroup;
escape and irreducibility give equality.

This completes the proper-overcomponent action and combines it with the maximal
branch and relative normality. The final assembly here retains only the genuine
12.2.7 residual-recognition input, whose construction remains with the terminal
component owner.

Source: Aschbacher--Smith, 12.3.7(2) and 12.3.12, pp.809,811.
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
theorem pointResidualCoreEquiv_mk (v : V) (hv : weight (E.coordinates v).toAdd.val = 2)
    (k : SylowNormalizer.pointResidual L (v : G)) :
    E.pointResidualCoreEquiv v hv (QuotientGroup.mk' _ k) =
      WeightTwoGeometry.fiveEquiv (E.coordinates v).toAdd hv (E.pointResidualProjection v hv k) := rfl
end Setup.NaturalCoordinates
namespace SylowNormalizer.Points
variable {E : S.NaturalCoordinates} (P : Points E)

def five_moved_natural :
    Representation.BinaryConjugationSection P.five ⁅V,P.five⁆ ⊥
      ((alternatingCoreRepresentation (Fin 5)).comp
        (P.fiveCoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.five)))) := by
  let M := ⁅V,P.five⁆
  let w := (E.coordinates P.two).toAdd
  have hMV : M ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((pointResidual_le L (P.two : G)).trans inf_le_left).trans S.chosen.normalizes)
  let f : Multiplicative (core (Fin 5)) →* M :=
    (((V.subtype.comp E.coordinates.symm.toMonoidHom).comp
      (AddMonoidHom.toMultiplicative (WeightTwoGeometry.extendFive w P.two_weight).toAddMonoidHom))).codRestrict M (by
        intro a
        apply P.support_zero_mem_five_moved (E.coordinates.symm
          (Multiplicative.ofAdd (WeightTwoGeometry.extendFive w P.two_weight a.toAdd)))
        have hh := (WeightTwoGeometry.range_extendFive w P.two_weight
          (WeightTwoGeometry.extendFive w P.two_weight a.toAdd)).mp
          ⟨a.toAdd,rfl⟩
        rw [E.coordinates.apply_symm_apply]
        exact hh)
  have hf (a : Multiplicative (core (Fin 5))) :
      (E.coordinates ⟨(f a : G),hMV (f a).property⟩).toAdd =
        WeightTwoGeometry.extendFive w P.two_weight a.toAdd := by
    exact congrArg Multiplicative.toAdd (E.coordinates.apply_symm_apply _)
  have hfi : Function.Injective f := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    apply WeightTwoGeometry.extendFive_injective w P.two_weight
    exact (hf a).symm.trans ((congrArg
      (fun x : M => (E.coordinates ⟨(x : G),hMV x.property⟩).toAdd) hab).trans (hf b))
  have hfs : Function.Surjective f := by
    intro x
    let xV : V := ⟨x,hMV x.property⟩
    have hx := E.point_residual_commutator_support_zero P.two P.two_weight xV x.property
    obtain ⟨a,ha⟩ := (WeightTwoGeometry.range_extendFive w P.two_weight
      (E.coordinates xV).toAdd).mpr hx
    refine ⟨Multiplicative.ofAdd a,?_⟩
    apply Subtype.ext
    change (E.coordinates.symm (Multiplicative.ofAdd (WeightTwoGeometry.extendFive w P.two_weight a)) : G) = x
    have he : E.coordinates.symm (Multiplicative.ofAdd (WeightTwoGeometry.extendFive w P.two_weight a)) = xV :=
      E.coordinates.injective ((E.coordinates.apply_symm_apply _).trans (congrArg Multiplicative.ofAdd ha))
    exact congrArg Subtype.val he
  let e : Multiplicative (core (Fin 5)) ≃* M := MulEquiv.ofBijective f ⟨hfi,hfs⟩
  have hecoord (a : M) : WeightTwoGeometry.extendFive w P.two_weight (e.symm a).toAdd =
      (E.coordinates ⟨(a : G),hMV a.property⟩).toAdd := by
    calc
      _ = (E.coordinates ⟨(f (e.symm a) : G),hMV (f (e.symm a)).property⟩).toAdd := (hf _).symm
      _ = _ := congrArg (fun x : M => (E.coordinates ⟨(x : G),hMV x.property⟩).toAdd)
        (e.apply_symm_apply a)
  have hn : P.five ≤ normalizer (M : Set G) := normalizer_commutator_ge_right V P.five
  refine {
    section_le := le_normalizer_iff_commutator_le_right.mp
      (S.chosen.le_sylow.trans (pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central))
    kernel_le := bot_le
    normalized := hn
    coordinates := e.symm.toMonoidHom
    onto := e.symm.surjective
    kernel_eq := by
      ext a
      change e.symm a = 1 ↔ (a : G) = 1
      rw [e.symm.map_eq_one_iff]
      exact Subtype.ext_iff
    equivariant := ?_ }
  intro k a
  apply WeightTwoGeometry.extendFive_injective w P.two_weight
  change WeightTwoGeometry.extendFive w P.two_weight
    (e.symm ⟨(k : G)*a*(k : G)⁻¹,(mem_normalizer_iff.mp (hn k.property) a).mp a.property⟩).toAdd = _
  rw [hecoord]
  change _ = WeightTwoGeometry.extendFive w P.two_weight
    (alternatingCoreRepresentation (Fin 5) (E.pointResidualCoreEquiv P.two P.two_weight (QuotientGroup.mk' _ k)) (e.symm a).toAdd)
  rw [Setup.NaturalCoordinates.pointResidualCoreEquiv_mk,WeightTwoGeometry.extendFive_equivariant,hecoord]
  exact E.equivariant ⟨k,((pointResidual_le L (P.two : G)).trans inf_le_left) k.property⟩
    ⟨a,hMV a.property⟩

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
theorem omega_commutator_le_chosen_moved
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
      rw [← RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural]
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

private def coreFiveNaturalEquiv :
    alternatingCoreRepresentation (Fin 5) ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
  .mk (coreEquivNatural (Fin 5) (by decide)) (by
    intro g
    apply LinearMap.ext
    intro v
    exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)

namespace TerminalPoint
variable (P : TerminalPoint S D)
theorem natural_in_overcomponent
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (R : P.ResidualAnalysis)
    {Y W : Subgroup G} (hKY : P.K ≤ Y)
    (SY : Setup T Y W) (DY : SY.LocalAnalysis) :
    ∃ q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5),
      Nonempty (BinaryConjugationSection P.K ⁅P.Z,P.K⁆ ⊥ (P.residualNaturalAction q)) := by
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect R.local_mem
  obtain ⟨v,hv,hvc,hK⟩ := DY.exists_central_weight_two_residual structural P.K hKY
    P.sylow_normalizes_residual R.quotient
  let E : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates,fun l v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨l,SY.chosen.normalizes l.property⟩ v⟩
  obtain ⟨z,hz,hzc⟩ := E.central_representative_weight structural (n := 6)
    (Or.inr (Or.inr rfl))
  let Q : SylowNormalizer.Points E := ⟨v,z,hv,hz,hvc,hzc⟩
  have hs : SY.NaturalOmegaDecomposition :=
    (E.core_omega_decomposition_of_weight_six structural escape (by
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
    exact SY.omega_commutator_le_chosen_moved structural hs P.K hKY
  let ρ := (alternatingCoreRepresentation (Fin 5)).comp
    (Q.fiveCoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Q.five)))
  let : (alternatingCoreRepresentation (Fin 5)).IsIrreducible :=
    coreFiveNaturalEquiv.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff
    (Q.fiveCoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Q.five)))
    (Q.fiveCoreEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    (alternatingCoreRepresentation (Fin 5))).mpr inferInstance
  have heq : ⁅P.Z,P.K⁆ = ⁅W,Q.five⁆ := by
    apply (Q.five_moved_natural.eq_kernel_or_section ⁅P.Z,P.K⁆ bot_le hle ?_).resolve_left
      (P.omega_commutator_ne_bot structural)
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


/-- Source 12.3.12 after the earlier nonsolvable recognition step.
All proper-overcomponent action and normality premises are discharged here. -/
theorem componentAnalysis_of_residual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (R : P.ResidualAnalysis) : Nonempty P.ComponentAnalysis := by
  have hn := P.pointCentralizer_normalizes_of_residual structural escape localAnalysis R
  have hJ := P.thompson_generation_of_residual structural escape localAnalysis R
  obtain ⟨F⟩ := P.overcomponents_nonempty R.local_mem
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  by_cases he : P.K = F.Y
  · have hm : P.K ∈ Chapter1.LStar G (T : Subgroup G) := he.symm ▸ F.maximal
    obtain ⟨_,⟨hnat⟩⟩ := P.maximal_action R.quotient
      ⟨hm,(R.overgroups P.K hm le_rfl).1⟩ (R.maximal_natural hm)
    exact ⟨⟨hn,R.quotient,hJ,hnat⟩⟩
  · obtain ⟨W,⟨SY⟩⟩ := (R.overgroups F.Y F.maximal hKY).2.resolve_left he
    obtain ⟨DY⟩ := localAnalysis F.Y W SY
    obtain ⟨q,⟨hnat⟩⟩ := P.natural_in_overcomponent structural escape R hKY SY DY
    exact ⟨⟨hn,q,hJ,hnat⟩⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
