module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.CoverMarks
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import BenderSuzuki.Classification
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! A Bender model has solvable normalizers of nontrivial two-subgroups:
conjugate such a subgroup into a strongly embedded Borel, whose strong
embedding contains its normalizer and whose solvability follows from the
rank-one Sylow facts. Thus a characteristic two-module cannot support a
nonsolvable alternating-five block. The final theorem applies this exclusion
to the literal faithful component quotient of the original paired setup.
Source: Aschbacher–Smith 2.4.25, printed p.543. -/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
variable {X : Type*} [Group X] [Finite X]

private theorem bender_root_model (hm : ClassificationModels.IsBenderModel X) :
    _root_.IsSimpleBenderGroup X := by
  have hb := Chapter1.QuasisimpleInvolutions.isSimpleBenderGroup_of_benderModel hm
  rcases hb with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨n, hn, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, ⟨e⟩⟩⟩
  · exact .isPSL2 n hn e
  · exact .isSuzuki n hn
      (e.trans (MulEquiv.subgroupCongr
        (szModel_eq_suzukiMatrixGroup n)).symm)
  · let : Field E := hEfield
    let : Finite E := hEfinite
    obtain ⟨ePSU⟩ := projectiveSpecialUnitary_equiv_psu3Model
      J n hn hJ hEcard hfixedCard
    exact .isPSU3 n hn (e.trans ePSU)

private theorem native_strong_embedding {M : Subgroup X}
    (hM : _root_.IsStronglyEmbedded M) : BenderSuzuki.IsStronglyEmbedded M := by
  refine ⟨hM.1, hM.2.1, ?_⟩
  intro g hg x hxM hxright
  have hginv : g⁻¹ ∉ M := fun h => hg (by simpa using M.inv_mem h)
  apply hM.2.2 g⁻¹ hginv x
  refine ⟨hxM, ?_⟩
  simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using hxright

omit [Finite X] in
private theorem rank_one_model (hm : ClassificationModels.IsBenderModel X) :
    ChapterF.Source.IsRankOneModel X := by
  cases hm with
  | linear n hn h => exact .linear n (by omega) h
  | unitary n hn h => exact .projective_unitary n (by omega) h
  | suzuki m _ h => exact .suzuki m h

/-- A Bender model has solvable normalizers of all nontrivial two-subgroups.
The strongly embedded Borel contains the full normalizer, after Sylow conjugacy. -/
theorem bender_two_subgroup_normalizer_solvable
    (hm : ClassificationModels.IsBenderModel X)
    (U : Subgroup X) (hU : IsPGroup 2 U) (hne : U ≠ ⊥) :
    Group.IsSolvable (normalizer (U : Set X)) := by
  classical
  obtain ⟨M,hMroot⟩ := BenderSuzuki.exists_stronglyEmbedded_of_isSimpleBenderGroup
    (bender_root_model hm)
  have hM := native_strong_embedding hMroot
  obtain ⟨P,hPM⟩ := hM.containsSylowTwo
  have hf := (rank_one_model hm).rankOneSylowFacts P
  have hMN := hf.unique_maximal M hPM (lt_top_iff_ne_top.mpr hM.ne_top)
  let : Group.IsSolvable (normalizer (P : Set X)) := hf.solvable
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hMN) (inclusion_injective hMN)
  obtain ⟨T,hUT⟩ := hU.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq X T P
  let e := MulAut.conj g
  let V := U.map e.toMonoidHom
  have hVP : V ≤ (P : Subgroup X) := by
    rw [←hg]
    exact map_mono hUT
  have hVM : V ≤ M := hVP.trans hPM
  have hVne : V ≠ ⊥ := by
    intro hh
    exact hne ((U.map_eq_bot_iff_of_injective e.injective).mp hh)
  have hVp := hU.map e.toMonoidHom
  have hd : 2 ∣ Nat.card V := hVp.card_eq_or_dvd.resolve_left
    (fun hh => hVne (card_eq_one.mp hh))
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 hd
  have hui : BenderSuzuki.PFAppendixIII.IsInvolution (u : X) := by
    constructor
    · intro hh
      have hh' : u = 1 := Subtype.ext hh
      rw [hh',orderOf_one] at hu
      norm_num at hu
    · exact congrArg Subtype.val (hu ▸ pow_orderOf_eq_one u)
  have hNV : normalizer (V : Set X) ≤ M := by
    intro a ha
    have hua : a * (u : X) * a⁻¹ ∈ M :=
      hVM ((mem_normalizer_iff.mp ha _).mp u.property)
    have hur : (u : X) ∈ BenderSuzuki.PFchapter1section1.rightConjugate M a := by
      rw [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy, mem_map]
      refine ⟨a * (u : X) * a⁻¹,hua,?_⟩
      simp [mul_assoc]
    exact hM.mem_of_involution_mem_rightConjugate (hVM u.property) hur hui
  let : Group.IsSolvable (normalizer (V : Set X)) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hNV) (inclusion_injective hNV)
  have hnorm : (normalizer (U : Set X)).map e.toMonoidHom = normalizer (V : Set X) :=
    map_normalizer_eq_of_bijective U e.bijective
  let j := (normalizer (U : Set X)).equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsSolvable ((normalizer (U : Set X)).map e.toMonoidHom) := hnorm ▸ inferInstance
  exact Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective

/-- No alternating-five block embeds in a genuine Bender model. Its
characteristic nontrivial two-module forces the whole block into a solvable normalizer. -/
theorem bender_no_alternating_five_block
    (hm : ClassificationModels.IsBenderModel X)
    (A : Subgroup X) (hA : ChapterC.IsAlternatingBlock A 5) : False := by
  let U := (ChapterC.blockU A).map A.subtype
  let := hA.2.1.elementary
  have hUp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (ChapterC.blockU A)).map _
  have hUne : U ≠ ⊥ := by
    intro hh
    exact hA.2.1.blockU_ne_bot
      (((ChapterC.blockU A).map_eq_bot_iff_of_injective A.subtype_injective).mp hh)
  let : Group.IsSolvable (normalizer (U : Set X)) :=
    bender_two_subgroup_normalizer_solvable hm U hUp hUne
  have hAN : A ≤ normalizer (U : Set X) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hAN) (inclusion_injective hAN)
  obtain ⟨e⟩ := hA.2.2.quotient_iso
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end CFSG.Quasithin.Chapter2.AlternatingTerminal

namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

/-- The original paired block cannot have a Bender-model ordinary overcomponent. -/
theorem AlternatingPairSourceSetup.bender_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) → False := by
  intro S L GI K hK hLK hb
  obtain ⟨_, _, _, hA, _⟩ :=
    c.block_component_twoCore_quotient_marks hG T hM hTM hu hST hSM hMT hi K hK hLK
  exact AlternatingTerminal.bender_no_alternating_five_block hb _ hA

end CFSG.Quasithin.Chapter2
