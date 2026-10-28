module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ChiefAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureChief
public import Theory.Representation.NormalElementaryQuotient.CentralChief
/-!
# Unique central chief action for the contained A₅ layer

The split normal closure of the original A₅ block normally generates its
component. Block irreducibility forces every proper normal subgroup of the
closure into the ambient center. The reduced quotient then has one
noncentral chief factor, and the literal involution from the source ratio
argument remains marked on that factor.

This theorem deliberately leaves the separate identification of the actor
with `I/O₂(I)` to the local head argument; the C.1.13 binary-cover alternative
cannot be removed from `U(L) ≤ O₂(I)` alone.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_overcomponent_contained_layer_unique_chief
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I) :
    let K := L.subgroupOf I
    let W := normalClosure ((blockU K).map K.subtype : Set I)
    let q := QuotientGroup.mk' (centralizer (W:Set I))
    ∃ he : IsElementaryAbelian 2 W, letI := he
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      ∃ t, HasUniqueCentralChief ρ ∧ HasMarkedChiefSection ρ t := by
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype : Set I)
  let q := QuotientGroup.mk' (centralizer (W:Set I))
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hs := hK.normalClosure_layer_split K S hSK hU
  obtain ⟨he,hred,t,htK,ht,hr,hmarked⟩ :=
    source_a5_overcomponent_contained_layer_marked_chief_section D e hn hout hLI hIX hI hS hU
  let := he
  let qsurj := QuotientGroup.mk'_surjective (centralizer (W:Set I))
  let qker := QuotientGroup.ker_mk' (centralizer (W:Set I))
  let ρ := NormalElementaryQuotient.representation W q qsurj qker
  have hgen : normalClosure (K:Set I)=⊤ :=
    hK.normalClosure_eq_top_in_cComponent hIX hI
  have hmin : ∀ N : Subgroup I, N.Normal → N ≤ W → N = W ∨ N ≤ center I := by
    intro N hN hNW
    let := hN
    exact IsAlternatingBlock.layer_closure_normal_eq_or_central K hK hgen
      hs.2.2.2.1 N hNW
  have hwhole : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    apply Representation.NormalElementaryQuotient.commutator_top W
      (by simpa [W] using IsAlternatingBlock.layer_closure_commutator_top K hK)
      q qsurj qker
  have hfaith : Function.Injective ρ :=
    NormalElementaryQuotient.representation_injective W q qsurj qker
  have hnker : ¬ (⊤ : Subgroup (I ⧸ centralizer (W:Set I))) ≤ ρ.ker := by
    intro hh
    have h1rho : ρ t = 1 := MonoidHom.mem_ker.mp (hh (show t ∈ (⊤ : Subgroup (I ⧸ centralizer (W:Set I))) from mem_top _))
    have h1 : t = 1 := hfaith (by simpa using h1rho)
    rw [h1] at ht
    norm_num at ht
  have hmax : ∀ P : Subrepresentation ρ, P=⊤ ∨ P.toSubmodule≤fixedSpace ρ ⊤ := by
    intro P
    exact Representation.NormalElementaryQuotient.central_dichotomy W hmin q qsurj qker P
  have hu := Representation.BinaryOffender.unique_central_chief ρ hfaith hred.quotient_pCore_eq_bot
      hwhole hnker hmax
  exact ⟨he,t,hu,hmarked⟩
end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
