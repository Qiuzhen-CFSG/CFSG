module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.NoPlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Noncentral
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Saturation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Supported
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.InnerMarking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.LocalStructure
/-!
# The complete alternating-five seed exclusion in 13.6.15

The genuine B.5 classifier identifies the given constituent with U_K and
splits off C_W_K(K⁺). The ambient S₅ action and 13.6.11 make the residual
projection nonzero. Original Sylow invariance identifies its range as A₄.
The supported transposition supplied by the offender argument then puts the
whole residual image in K⁺. Its moved three-space cannot contain the original
invariant order-four plane, giving exactly ExcludesAlternatingFiveSeed.

Every classifier, splitting, projection, support and coordinate input is
constructed. The marked earlier local hypotheses below are discharged on the
original FlagSource configuration in OriginalSource.
Source: Aschbacher–Smith, 13.6.15, printed p.930 (PDF p.947).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection SourceContainment SourceContainment.LinearThree ChapterB.QuasisimpleSource
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
theorem excludes_alternatingFiveSeed_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : A5Module.Marking L V) (K T : Subgroup G)
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hzOmega : A5Module.markedZ s ∈ Stellmacher.omegaOneCenterAmbient (Tv T (A5Module.markedV s)))
    (hf : generalizedFitting (Gv (A5Module.markedV s)) = pCore 2 (Gv (A5Module.markedV s)))
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))] :
    let := wk_elementary K L T (A5Module.markedZ s) (A5Module.markedV s) hK.1.1 ⟨S,hS⟩ hzOmega hf
    ExcludesAlternatingFiveSeed K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  have hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v) := ⟨S,hS⟩
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  dsimp only
  intro I _hseed _hirr he0
  obtain ⟨e⟩ := he0
  have hv := (ComponentReduction.InitialSieve.marked_orders s).2
  obtain ⟨hm,hs⟩ := Support.wk_moved_and_isCompl hG K L T z v hv hL hz hSylow hzOmega hf hK hn I e
  obtain ⟨r,hr,he⟩ := Support.wk_permutation_action hG K L T z v hv hL hz hSylow hzOmega hf hK hn I e
  have hUK := UK_commutator_ne_bot s K T S hS hz hK hn
  have hcomm := plus_commutator_ne_bot K L T z v hL hz I e hm r hr he hUK
  obtain ⟨f,hfproj,g,hB⟩ := exists_projected_borel K L T z v hL hz hK hn e.groupEquiv hc hcomm
  let e' := e.innerMarking g
  obtain ⟨r',hr',he'⟩ := Support.wk_permutation_action hG K L T z v hv hL hz hSylow hzOmega hf hK hn I e'
  obtain ⟨P,hP⟩ := hSylow.restrict (show Tv T v ≤ plusActor K L T v from le_sup_right)
    (plusActor_le_Gv K L T v hK.1.1)
  let Pplus := P.mapSurjective (plusMk_surjective K L T z v hL hz)
  obtain ⟨a,ha,hat,_ha2,hasupport⟩ := Support.wk_supported_transposition hG K L T z v hv hL hz
    hSylow hzOmega hf hK hn hc I e' r' he' Pplus
  have haimage : a ∈ plusImage K L T z v hL hz (Tv T v) := by
    change a ∈ (P : Subgroup (plusActor K L T v)).map (plusMk K L T z v hL hz) at ha
    obtain ⟨t,ht,rfl⟩ := ha
    exact ⟨t,hP ▸ mem_map_of_mem (plusActor K L T v).subtype ht,rfl⟩
  have hB' : f.range.map e'.groupEquiv.toMonoidHom = BinaryPermutation.AlternatingFiveBorel.B := hB
  have hLC := residualPlus_le_component K L T z v hL hz hK hn I e' hs f hfproj hB'
    r' hr' he' hc hcomm a haimage hat hasupport
  have hfact : ∀ l, (f l : Gplus K L T z v hL hz) = residualPlusMap K L T z v hL hz l :=
    AlternatingFiveProjection.inner_projection_eq_of_range_le _ e.groupEquiv
      (residualPlusMap K L T z v hL hz) f hfproj ((residualPlusMap_range K L T z v hL hz).le.trans hLC)
  exact false_of_borel_projection s K T hL hz I e' hs f hfact hB'
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
