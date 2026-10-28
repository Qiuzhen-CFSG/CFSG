module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.CompleteSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.LinearThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.RankOne.UnitaryExtensions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Catalogue

/-!
# Direct signed-three exclusions in the original normalized component

Conjugate the actual component Sylow to the concrete model Sylow. The marked
residual is its commutator with the local Sylow, so its field action vanishes.
The uniform highest-root centralizer then contradicts the distinct actions of
the two marked involutions. The linear and unitary proofs retain the original
component quotient and its actual embedding in N(K)/C(K); no whole-extension
classification or A.3.18 alternative is assumed.

Source: Aschbacher--Smith, proof of 13.6.6, printed p.927.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open A5Module InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {T : Sylow 2 G} {s : Marking L V}

/-- Align the model Sylow using conjugacy inside the actual component image. -/
theorem exists_aligned_component_model
    (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s)))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K)
    {M : Type*} [Group M] [Finite M]
    (e0 : NormalizerAction.componentImage K ≃* M) (Q : Sylow 2 M) :
    ∃ e : K ⧸ center K ≃* M,
      (Q : Subgroup M).map (rankOneModelEmbedding K e) =
        NormalizerAction.sylowImage K (localT (T : Subgroup G) (markedV s)) ⊓
          NormalizerAction.componentImage K := by
  have hS : (d.sylow : Subgroup (Gv (markedV s))) =
      localT (T : Subgroup G) (markedV s) :=
    (localT_eq_sylow _ _ d.sylow d.sylow_image).symm
  obtain ⟨P,hP⟩ := NormalizerAction.exists_component_sylow K d.sylow (hS ▸ hTN)
  rw [hS] at hP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M
    (P.mapSurjective (f := e0.toMonoidHom) e0.surjective) Q
  let k := e0.trans (MulAut.conj g)
  have hQ : (P : Subgroup (NormalizerAction.componentImage K)).map k.toMonoidHom = Q := by
    have hh := congrArg (fun S : Sylow 2 M => (S : Subgroup M)) hg
    change ((P : Subgroup (NormalizerAction.componentImage K)).map e0.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = Q at hh
    exact (map_map _ _ _).symm.trans hh
  let e := (NormalizerAction.componentCentralQuotientEquiv K).trans k
  refine ⟨e, ?_⟩
  rw [← hQ, map_map]
  have he : (rankOneModelEmbedding K e).comp k.toMonoidHom =
      (NormalizerAction.componentImage K).subtype := by
    ext x
    change ((NormalizerAction.componentCentralQuotientEquiv K)
      ((NormalizerAction.componentCentralQuotientEquiv K).symm (k.symm (k x))) : XStar K) = x
    rw [k.symm_apply_apply, MulEquiv.apply_symm_apply]
  rw [he]
  exact hP

/-- The linear-three source row is impossible without an A3.18 extension
presentation: the actual residual commutator removes the field action. -/
theorem source_not_linearThree
    (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (hEK : EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K)
    (hk : IsPGroup 2 s.action.ker) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K)
    {m : ℕ} (hm : 1 < m)
    (hmodel : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 3 (2 ^ m)) : False := by
  obtain ⟨F, _, _, hF, ⟨e0⟩⟩ := hmodel
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨e,he⟩ := exists_aligned_component_model d K hTN e0
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
  have hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
    intro x hx
    exact Subtype.ext (mem_centralizer_iff.mp d.a_centralizes x hx)
  apply exclude_linearThree s (T : Subgroup G) K a.a_normalizes a.z_normalizes
    a.residual_normalizes hac
    (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.1)
    (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.2)
    (four_le_rootCenter s (T : Subgroup G) K a.a_normalizes a.z_normalizes a.central hEK)
    hk hTL d.sylow (localT_eq_sylow _ _ d.sylow d.sylow_image).symm hTN hm hF e
  have hemb : linearThreeEmbedding K e = rankOneModelEmbedding K e := by
    apply MonoidHom.ext
    intro x
    obtain ⟨q,rfl⟩ := e.surjective x
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) q
    rw [linearThreeEmbedding_mk]
    change _ = ((NormalizerAction.componentCentralQuotientEquiv K)
      (e.symm (e (QuotientGroup.mk' (center K) k))) : XStar K)
    rw [e.symm_apply_apply, NormalizerAction.componentCentralQuotientEquiv_mk]
    rfl
  simpa only [hemb, Matrix.PSL3.LinearThree.coe_unipotentSylow] using he

/-- The unitary-three source row is impossible under the same actual local
hypotheses, including arbitrary covers and outer actors. -/
theorem source_not_unitaryThree
    (d : Setup KnownSimple.IsKnownSimple T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K)
    (hEK : EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K)
    (hk : IsPGroup 2 s.action.ker) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K)
    {m : ℕ} (hm : 1 < m)
    (hmodel : ClassicalGroup.IsPSU (NormalizerAction.componentImage K) 3 (2 ^ m)) : False := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e0⟩⟩ := hmodel
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2 ^ (m * 2) by simpa only [pow_mul] using hF)
  obtain ⟨C,hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis J m (by omega) hF hconj
  let J0 := ChapterF.Source.Unitary.FormTransport.standardForm J
  let e1 := e0.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  have hfixed : Nat.card {x : F // J0.conj x = x} = 2 ^ m :=
    FiniteField.card_fixed_of_quadratic_frobenius J0.conj 2 m (by omega) hF hconj
  let Q := BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.rootSylow J0 rfl
    (by omega) hF hfixed
  obtain ⟨e,he⟩ := exists_aligned_component_model d K hTN e1 Q
  have hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
    intro x hx
    exact Subtype.ext (mem_centralizer_iff.mp d.a_centralizes x hx)
  have hDB := Catalogue.residualStar_le_borelCandidate_of_binaryModel s (T : Subgroup G) K
    (BinaryModelAt.unitary_three m (by omega) ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨e0⟩⟩)
    hm hk hTL d.sylow (localT_eq_sylow _ _ d.sylow d.sylow_image).symm a.residual_normalizes hTN
  apply exclude_unitaryThree_extensions s (T : Subgroup G) K hK
    a.a_normalizes a.z_normalizes a.residual_normalizes hTN hac
    (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.1)
    (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.2)
    (four_le_rootCenter s (T : Subgroup G) K a.a_normalizes a.z_normalizes a.central hEK)
    J0 rfl hm hF hfixed e he hk hTL d.sylow
    (localT_eq_sylow _ _ d.sylow d.sylow_image).symm hDB
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
