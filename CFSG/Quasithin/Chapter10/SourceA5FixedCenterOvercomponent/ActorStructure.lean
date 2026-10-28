module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.HeadAction
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.EvenNormalQuotient
public import Theory.Alternating.proposition_5_2_9_10
/-!
# Quasisimplicity of the actual contained-layer actor

The original A₅ image embeds in the faithful actor, giving two-rank at
least two. The head I/O₂(I) is either quasisimple or has two-rank one. In
the latter case the kernel of its map to the actor must have even order:
an odd kernel preserves two-rank. The noncentral-Fitting theorem identifies
that proper even kernel with the radical and its quotient with PSL₂(p),
for a prime p>3. Thus the actor is quasisimple in both cases.

The chief-action consumer now requires no separate actor-quasisimplicity
premise and retains the literal small involution and its displacement bound.
Source: Aschbacher–Smith 10.2.1, printed p.743, using A.3.6 and B.4.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
/-- The original actor is quasisimple; a nonquasisimple head has a
prime-field PSL₂ actor, with its actual quotient marking retained. -/
theorem source_a5_involution_overcomponent_actor_structure
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {v : G} (hv : orderOf v=2) {I : Subgroup G} (hLI : L≤I)
    (hIX : I≤centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype≤pCore 2 I) :
    let A := I ⧸ centralizer
      (normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype:Set I):Set I)
    IsQuasisimple A ∧ (IsQuasisimple (I ⧸ pCore 2 I) ∨
      ∃p:ℕ,p.Prime ∧ 3<p ∧ Nonempty (A≃*PSL(2,ZMod p))) := by
  by_cases hhead : IsQuasisimple (I ⧸ pCore 2 I)
  · exact ⟨(source_a5_overcomponent_quasisimple_head_action D e hn hout
      hLI hIX hI hS hU hhead).1,Or.inl hhead⟩
  let K := L.subgroupOf I
  let W := normalClosure ((blockU K).map K.subtype:Set I)
  let C := centralizer (W:Set I)
  let A := I ⧸ C
  let H := I ⧸ pCore 2 I
  let q := QuotientGroup.mk' C
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hs := hK.normalClosure_layer_split K S hSK hU
  have hOk : pCore 2 I≤q.ker := by
    rw [QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp hs.2.1
  let f : H →* A := QuotientGroup.lift (pCore 2 I) q hOk
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ q
    (QuotientGroup.mk'_surjective _) _
  obtain ⟨ea⟩ := hK.layer_split_quotient_image K W le_normalClosure hs.2.2.2.1 q
    (QuotientGroup.ker_mk' _)
  have hrank : 2≤primeRank 2 A := by
    have hfive : primeRank 2 (alternatingGroup (Fin 5))=2 :=
      (GLS3.Chapter5.PRank.alternating_hasPRank_two 5).primeRank_eq Nat.prime_two
    calc
      2 = primeRank 2 (K.map q) := by rw [primeRank_equiv 2 ea,hfive]
      _ ≤ primeRank 2 A := Theory.GroupTheory.primeRank_le_of_injective 2 (K.map q).subtype (K.map q).subtype_injective
  have hne : K.map q≠⊥ := by
    intro he
    have hh := Nat.card_congr ea.toEquiv
    rw [he,card_bot,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  let : Nontrivial (K.map q) := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial A := (K.map q).subtype_injective.nontrivial
  have hproper : f.ker≠⊤ := by
    intro he
    obtain ⟨a,ha⟩ := exists_ne (1:A)
    obtain ⟨h,rfl⟩ := hf a
    exact ha (MonoidHom.mem_ker.mp (he ▸ mem_top h))
  have hsq := D.simpleQTKE.involution_centralizer_sqtk hv
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIX)).mp (hsq.subgroup (I.subgroupOf _))
  have hsqH : IsSQTK KnownSimple.IsKnownSimple H := by
    refine ⟨?_,hsqI.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 I) pCore_isPGroup).trans
      (hsqI.stronglyQuasithin p hp ho)
  have htop : (⊤:Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.subgroupOf_of_le le_rfl hIX
  let : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
  have hbar : (⊤:Subgroup H).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 I)
  have heven : Even (Nat.card f.ker) := by
    by_contra he
    have hodd := Nat.not_even_iff_odd.mp he
    have heq := primeRank_eq_of_surjective_of_coprime 2 f hf hodd.coprime_two_left
    have hh : 2≤primeRank 2 (⊤:Subgroup H) := by
      rw [primeRank_equiv 2 (topEquiv : (⊤:Subgroup H)≃*H),heq]
      exact hrank
    let := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
      hsqH (pCore_quotient_pCore_eq_bot 2) hbar hh
    exact hhead (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨_,p,hp,hp3,⟨ep⟩⟩ :=
    ChapterA.Section03.NoncentralFitting.intrinsic_even_normal_quotient
      hsqH (pCore_quotient_pCore_eq_bot 2) hbar hhead f.ker hproper heven
  let : Fact p.Prime := ⟨hp⟩
  let epA : A≃*PSL(2,ZMod p) :=
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans ep
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4≤p by omega))
  let : IsSimpleGroup A := epA.isSimpleGroup
  let := htop.perfect
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤:Subgroup I)≃*I).toMonoidHom) topEquiv.surjective
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := q) (QuotientGroup.mk'_surjective C)
  have hc : center A=⊥ := (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
    (fun ht => Group.IsPerfect.not_isSolvable A
      (Group.isSolvable_of_comm (center_eq_top_iff.mp ht).is_comm.comm))
  exact ⟨⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup⟩,
    Or.inr ⟨p,hp,hp3,⟨epA⟩⟩⟩

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
/-- The unique chief action, original involution, displacement and ratio
bounds follow from the original contained-layer input alone. -/
theorem source_a5_involution_overcomponent_chief_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {v : G} (hv : orderOf v = 2) {I : Subgroup G} (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I) :
    let K := L.subgroupOf I
    let W := normalClosure ((blockU K).map K.subtype : Set I)
    let A := I ⧸ centralizer (W:Set I)
    let q := QuotientGroup.mk' (centralizer (W:Set I))
    ∃ he : IsElementaryAbelian 2 W, letI := he
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      let σ := fixedQuotient ρ ⊤
      ∃ t : A, ChapterK.RankOne.SourceHypotheses σ (generalizedFitting A) ∧
        orderOf t = 2 ∧
        Module.finrank (ZMod 2) (LinearMap.range (σ t -
          (LinearMap.id : (Additive W ⧸ (fixedSubrepresentation ρ ⊤).toSubmodule) →ₗ[ZMod 2]
            (Additive W ⧸ (fixedSubrepresentation ρ ⊤).toSubmodule)))) ≤ 2 ∧
        quadraticRatio σ ≤ 2 := by
  exact source_a5_involution_overcomponent_chief_action_of_actor_quasisimple
    D e hn hout hv hLI hIX hI hS hU
    (source_a5_involution_overcomponent_actor_structure D e hn hout hv hLI hIX hI hS hU).1

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
