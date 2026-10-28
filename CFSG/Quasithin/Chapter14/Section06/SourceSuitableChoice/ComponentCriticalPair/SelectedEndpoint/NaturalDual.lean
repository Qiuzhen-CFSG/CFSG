module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SelectedEndpoint.Reversal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.OrbitMatching.RankProfiles
public import Theory.Representation.PSL3Two.NaturalDualEmbedding

/-!
# The specified crossing from the marked single-component supports

The faithful component action and the embedded natural--dual pair give the
non-FF property, the two-rank bound, and innerness of every quadratic actor
within the source budget. The selected endpoint is therefore in the actual
support normalizer. In either equal-rank case its genuine reversal has the
same property; the retained transporter places the literal inverse-conjugate
actor there too. The proved commutator profiles then supply the specified
match. The remaining index-two case contradicts dual hyperplane movement.

Only the preceding single-component support markings remain inputs: the
literal quotient actions, their kernels, the fixed-factor decomposition and
the same suitable element. No selected endpoint, non-FF assertion, rank bound,
support-preservation callback or commutator-image profile is assumed.
The component exclusions and construction of these source markings remain
with qt-e-suitable-component-marking, using qt-e-suitable-component-supports;
final suitable-choice assembly belongs to qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.20--24(4), pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G]

private theorem natural_image_rank {H L A : Subgroup G} (hLH : L ≤ H) (hAL : A ≤ L)
    (f : L →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hk : f.ker = (H.pCoreIn 2).subgroupOf L) :
    rank ((A.subgroupOf L).map f) = rank (Source.starImage H A) := by
  change Nat.log 2 (Nat.card ((A.subgroupOf L).map f)) =
    Nat.log 2 (Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
  rw [← relIndex_ker _ f, ← relIndex_ker _ (QuotientGroup.mk' (pCore 2 H)),hk,
    QuotientGroup.ker_mk',relIndex_subgroupOf hAL]
  have hc : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [←hc,relIndex_subgroupOf (hAL.trans hLH)]

private theorem natural_image_elementary {H L A : Subgroup G}
    [IsElementaryAbelian 2 A] (hAL : A ≤ L)
    (f : L →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hk : f.ker = (H.pCoreIn 2).subgroupOf L) (hn : ¬ A ≤ H.pCoreIn 2) :
    IsElementaryTwo ((A.subgroupOf L).map f) := by
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  refine ⟨?_,IsElementaryAbelian.map f⟩
  intro hz
  have hle := (Subgroup.map_eq_bot_iff _).mp hz
  rw [hk] at hle
  exact hn (fun a ha => hle (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))

variable [Finite G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (sectionModel : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ)
    (ι : Source.Hstar Mc →* MulAut BinaryLinearThree.Group) (hι : Function.Injective ι)
    (embedding : BinaryLinearThree.NaturalDual.Space →ₗ[ZMod 2] E)
    (hembedding : Function.Injective embedding)
    (hact : ∀ a v, ρ a (embedding v) = embedding (BinaryLinearThree.NaturalDual.autAction (ι a) v))
    (W W' : Subgroup G)

local notation "U" => conjugateSpanBy (localModule T M) Mc
local notation "Z" => centralInvolutions T
local notation "L" => (Mc ⊓ normalizer (W : Set G) : Subgroup G)
local notation "h" => ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab

include sectionModel hι embedding hembedding hact in
/-- Both symmetric ranks and the asymmetric rank-two branch are resolved
from the same marked component supports. The output is a literal crossing
for the original suitable u and its explicitly transported conjugator. -/
theorem source_crossing_of_marked_single_component
    (hL : (L).subgroupOf Mc = (MulAut.innerSubgroup BinaryLinearThree.Group).comap
      (ι.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (f : (L) →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (hkernel : f.ker = (Mc.pCoreIn 2).subgroupOf (L))
    (c : BinaryConjugationSection (L) W Z
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (cdual : BinaryConjugationSection (L) W' Z (LowRankProfiles.natural.dual.comp f))
    (hWU : W ≤ U) (hW'U : W' ≤ U)
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W) (hu : ComponentSupports.Suitable (h) Mc u)
    (K B C : Subgroup G) (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hBU : B ≤ U) (φ : K →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hφ : Function.Surjective φ)
    (d : BinaryConjugationSection K B Z (naturalDualRepresentation.comp φ))
    (dL : BinaryConjugationSection (L) B Z (naturalDualRepresentation.comp f))
    (hcoordinates : ∀ b : B, dL.coordinates b = d.coordinates b)
    (hW : ∀ v : B, (v : G) ∈ W ↔ (d.coordinates v).toAdd.2 = 0)
    (hW' : ∀ v : B, (v : G) ∈ W' ↔ (d.coordinates v).toAdd.1 = 0)
    (hB : ⁅U,Mc⁆ ≤ B) (hcover : ∀ v ∈ U, ∃ b ∈ B, ∃ t ∈ C, v = b * t)
    (hfixed : ⁅Mc,C⁆ ≤ Z) :
    ∃ i : (h).CriticalEndpoint, ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  have hnff := BinaryLinearThree.NaturalDual.not_ff_of_pair_embedding
    ρ ι hι embedding hembedding hact
  have hrank := BinaryLinearThree.NaturalDual.two_rank_le_of_component_embedding ι hι
  obtain ⟨q⟩ := source_selected_endpoint hG T hempty hM hunique hmany hcard e hab
    sectionModel hnff hrank
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,Z,Mc⟩
  let hh : D.Hypothesis := h
  let : IsElementaryAbelian 2 U :=
    hh.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans hh.UH_le_QH)
  let : IsElementaryAbelian 2 D.UH :=
    hh.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans hh.UH_le_QH)
  have normalize (i : (h).CriticalEndpoint)
      (hi : Reorientation.QuadraticMember ρ (Source.starImage Mc (i.conjugate U))) :
      i.conjugate U ≤ L := by
    have hAH : i.conjugate U ≤ Mc :=
      (map_mono (conjugateSpanBy_mono hh.plus_le le_rfl)).trans (i.large_le q.track_lower)
    have hin := BinaryLinearThree.NaturalDual.inner_of_pair_embedding
      ρ ι hι embedding hembedding hact _ hi.1 hi.2.1 hi.2.2
    intro a ha
    have hp : (⟨a,hAH ha⟩ : Mc) ∈ (MulAut.innerSubgroup BinaryLinearThree.Group).comap
        (ι.comp (QuotientGroup.mk' (pCore 2 Mc))) :=
      hin (mem_map_of_mem ι (mem_map_of_mem (QuotientGroup.mk' (pCore 2 Mc)) ha))
    rwa [←hL] at hp
  have hAL : q.endpoint.conjugate U ≤ L := normalize q.endpoint q.actor_quadratic
  have hnA : ¬ q.endpoint.conjugate U ≤ Mc.pCoreIn 2 := by
    intro hn
    exact not_le_of_gt q.opposite_denominator_strict (le_inf le_rfl hn)
  have hnormL : Mc ≤ normalizer (L : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (show L ≤ Mc from inf_le_left)).mp
    rw [hL]
    infer_instance
  have symmetric
      (heq : Nat.log 2 ((U ⊓ q.endpoint.conjugate (Mc.pCoreIn 2)).relIndex U) =
        rank (Source.starImage Mc (q.endpoint.conjugate U))) :
      ∃ x ∈ Mc, ∃ k : G,
        k = x⁻¹ * q.endpoint.representative ∧
        (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
          (q.endpoint.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
        ∃ crossing : SourceCrossingGeometry (localModule T M) Mc Mc u,
          crossing.A = U ∧ crossing.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
    obtain ⟨j,hj,hjq,_⟩ := q.reverse_quadratic_of_equal_ranks rfl sectionModel heq
    have hjL := normalize j hjq
    let A' := (U).map (MulAut.conj q.endpoint.representative⁻¹).toMonoidHom
    have hAL' : A' ≤ L := by
      have hm := map_mono (f := (MulAut.conj
        (j.representative * q.endpoint.representative)⁻¹).toMonoidHom) hjL
      have he : (j.conjugate U).map (MulAut.conj
          (j.representative * q.endpoint.representative)⁻¹).toMonoidHom = A' := by
        rw [ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.conjugate,map_map]
        congr 1
        ext a
        simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
        group
      have ht : (L).map (MulAut.conj
          (j.representative * q.endpoint.representative)⁻¹).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp (hnormL (Mc.inv_mem hj))
      rw [he,ht] at hm
      exact hm
    have hnA' : ¬ A' ≤ Mc.pCoreIn 2 := by
      intro hn
      have hm := map_mono (f := (MulAut.conj q.endpoint.representative).toMonoidHom) hn
      have he : A'.map (MulAut.conj q.endpoint.representative).toMonoidHom = U := by
        simpa only [inv_inv] using
          PairConsequences.conjugate_inverse_cancel q.endpoint.representative⁻¹ U
      rw [he] at hm
      exact not_le_of_gt q.denominator_strict (le_inf le_rfl hm)
    let : IsElementaryAbelian 2 (q.endpoint.conjugate U) := IsElementaryAbelian.map _
    let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
    obtain ⟨hRB,hRBg,hZR⟩ := q.commutator_inputs B hB
    exact OrbitMatching.source_crossing_of_marked_quadratic_actions
      hG T hempty hM hunique hmany hcard e hab W W' f hf c s hs hsW u huW hu
      K B hK hBU φ hφ d hW hW' q.endpoint (L) C f dL hcoordinates hcover hAL hAL'
      ((commutator_mono (hAL.trans inf_le_left) le_rfl).trans hfixed)
      ((commutator_mono (hAL'.trans inf_le_left) le_rfl).trans hfixed)
      (natural_image_elementary hAL f hkernel hnA)
      (natural_image_elementary hAL' f hkernel hnA') hRB hRBg hZR
  rcases q.rank_cases with h1 | h2 | h21
  · exact ⟨q.endpoint,symmetric (h1.2.trans h1.1.symm)⟩
  · exact ⟨q.endpoint,symmetric (h2.2.trans h2.1.symm)⟩
  · have hd : (U ⊓ q.endpoint.conjugate (Mc.pCoreIn 2)).relIndex U = 2 := by
      have he : Nat.log 2 ((U ⊓ q.endpoint.conjugate (Mc.pCoreIn 2)).relIndex U) = 1 := h21.2
      rw [log_relIndex_eq_quotient_finrank] at he
      rw [relIndex_eq_two_pow_quotient_finrank,he]
      rfl
    have hZD : Z ≤ U ⊓ q.endpoint.conjugate (Mc.pCoreIn 2) := by
      have he : Source.DH U (q.endpoint.conjugate U) (q.endpoint.conjugate Z) =
          U ⊓ q.endpoint.conjugate (Mc.pCoreIn 2) := q.denominator_eq
      rw [←he]
      exact sectionModel.line_le_DH _ _ (hAL.trans inf_le_left)
    have hr : 2 ≤ rank (((q.endpoint.conjugate U).subgroupOf (L)).map f) := by
      rw [natural_image_rank inf_le_left hAL f hkernel]
      exact h21.1.ge
    exact (OrbitMatching.source_false_of_rank_two_denominator_index_two
      hG T hempty hM hunique hmany hcard e hab W W' f hf c s hs hsW u huW hu
      q.endpoint cdual hWU hW'U hAL hZD hd.le hr).elim

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
