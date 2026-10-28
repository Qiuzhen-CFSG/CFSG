module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryOvercomponent
public import Theory.SpecificGroups.Triality.RootPairRank
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.InnerImageGeometry

/-!
# Original degree two in the binary-triality Cartan branch

The actual triality two-core section has two-rank at least four. Odd
ternary sections have two-rank at most three; perfect subgroups of odd
PSL₂ have trivial two-core and two-rank at most two. These arguments use
the literal image and its two-core quotient, without assuming that ordinary
two-rank decreases under arbitrary quotients.

The triality section is centerless and has three-rank two. A central
three-cover would contribute an independent central cubic, contradicting
the containing quotient's SQTK three-rank bound. The full quasisimple
catalogue therefore leaves only the previously controlled rank-two rows
or Bender models. Solvable proper Sylow overgroups in the latter lift
through the original two-core and force equality of the local components.
Thus the strict-enlargement branch at original degree greater than two
is impossible, and the original minus-torus dichotomy forces degree two.

The same T,L,W,n, H-star member, both Hall conditions, original component
and residual are retained. The degree-two binary-triality case remains
open: this theorem neither identifies its residual as PSL₂(4) nor supplies
an exceptional LocalCartanWitness.

Source: Aschbacher--Smith A.3.6, A.3.12 and 5.1.12--13,
printed pp.43--48,635--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
open Chapter1.Section02.LocalModels
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

private theorem triality_section_four_rank {Q : Type*} [Group Q] [Finite Q]
    (hm : Triality.Standard.IsTrialityGroupAt 2 Q) : 4 ≤ primeRank 2 Q := by
  have hm' : Triality.Standard.IsTrialityGroupAt (2^1) Q := by simpa using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q 1 Nat.zero_lt_one).mp hm'
  rw [primeRank_equiv 2 e]
  exact Triality.Standard.RootPairRank.twoRank_ge_four_mul 1 Nat.zero_lt_one

private theorem triality_section_center {Q : Type*} [Group Q]
    (hm : Triality.Standard.IsTrialityGroupAt 2 Q) : center Q = ⊥ := by
  have hm' : Triality.Standard.IsTrialityGroupAt (2^1) Q := by simpa using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q 1 Nat.zero_lt_one).mp hm'
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_center_equiv, Subgroup.map_bot, Triality.Standard.binaryCarrier_center_eq_bot]

private theorem triality_section_three_rank (I : Subgroup G)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (I ⧸ pCore 2 I)) :
    2 ≤ primeRank 3 I := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
  have hm' : Triality.Standard.IsTrialityGroupAt (2^1) (I ⧸ pCore 2 I) := by simpa using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp hm'
  rw [primeRank_equiv 3 e]
  obtain ⟨E,hE,hEc⟩ := Triality.Standard.exists_elementaryAbelian_three_card_nine 1 Nat.zero_lt_one
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hEc

private theorem triality_section_not_center_three
    (hG : IsStronglyQuasithin G) (I : Subgroup G)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (I ⧸ pCore 2 I))
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3))) : False := by
  have hi := triality_section_three_rank I hm
  have hz : Nat.Coprime 3 (Nat.card (center I)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le
      (center_le_pCore_of_quotient_center_eq_bot (triality_section_center hm))).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hrz : 1 ≤ primeRank 3 (center G) := by
    rw [primeRank_equiv 3 hc.some]
    apply primeRank_ge_of_elementary_embedding (f := MonoidHom.id (Multiplicative (ZMod 3)))
    · decide +kernel
    · simp
    · exact Function.injective_id
  have hcomm : center G ≤ centralizer (I : Set G) :=
    center_le_centralizer _
  have hr := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (center G) I hcomm hz
  have hb := hG 3 (by decide) (by decide)
  omega

private theorem triality_section_not_odd (I : Subgroup G) [Group.IsPerfect I]
    (hm : Triality.Standard.IsTrialityGroupAt 2 (I ⧸ pCore 2 I))
    (hodd : ChapterA.Section02.IsTheoremCOddModel G) : False := by
  cases hodd with
  | linear_two p k hp ho hk he =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let f := e.toMonoidHom.comp I.subtype
    have hf : Function.Injective f := e.injective.comp I.subtype_injective
    have hcore : pCore 2 I = ⊥ := by
      apply bot_unique
      exact (Theory.PSL2.odd_perfect_hom_twoCore_le_ker (hF ▸ ho.pow) f).trans_eq
        ((MonoidHom.ker_eq_bot_iff f).mpr hf)
    let a : (I ⧸ pCore 2 I) ≃* I := (QuotientGroup.congr _ _ (MulEquiv.refl I)
      (by simpa using hcore)).trans (QuotientGroup.quotientBot)
    have hr := triality_section_four_rank hm
    rw [primeRank_equiv 2 a] at hr
    have hu : primeRank 2 G ≤ 2 :=
      (ChapterA.Section02.IsTheoremCOddModel.linear_two p k hp ho hk
        ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩).twoRank_le_two
    have hi := primeRank_subgroup_le 2 I
    omega
  | linear_three p hp ho he =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let a := I.equivMapOfInjective e.toMonoidHom e.injective
    let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have hr := triality_section_four_rank hm
    rw [primeRank_equiv 2 b] at hr
    have hu := Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
      (hF ▸ ho) (I.map e.toMonoidHom) (pCore 2 (I.map e.toMonoidHom))
    omega
  | unitary_three p hp ho he =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := he
    let a := I.equivMapOfInjective e.toMonoidHom e.injective
    let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have hr := triality_section_four_rank hm
    rw [primeRank_equiv 2 b] at hr
    have hu := Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
      J (hF ▸ ho.pow) (I.map e.toMonoidHom) (pCore 2 (I.map e.toMonoidHom))
    omega

private theorem theoremC_transport {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (hm : TheoremCModel R) : TheoremCModel Q := by
  cases hm with
  | alternating d hd he => exact .alternating d hd ⟨e.trans he.some⟩
  | linear_odd p k hp ho hk hs he => exact .linear_odd p k hp ho hk hs (he.of_mulEquiv e)
  | three_odd p hp ho u he =>
    apply TheoremCModel.three_odd p hp ho u
    cases u <;> exact he.of_mulEquiv e
  | rank_one he =>
    cases he with
    | linear n hn he => exact .rank_one (.linear n hn (he.of_mulEquiv e))
    | unitary n hn he => exact .rank_one (.unitary n hn (he.of_mulEquiv e))
    | suzuki m hm he => exact .rank_one (.suzuki m hm ⟨e.trans he.some⟩)
  | rank_two he =>
    apply TheoremCModel.rank_two
    cases he with
    | linear n hn he => exact .linear n hn (he.of_mulEquiv e)
    | symplectic n hn he => exact .symplectic n hn (he.of_mulEquiv e)
    | g2 n hn he => exact .g2 n hn (he.of_mulEquiv e)
    | triality n hn he => exact .triality n hn (he.of_mulEquiv e)
    | ree m hm he =>
      obtain ⟨d,⟨a⟩⟩ := he
      exact .ree m hm ⟨d,⟨e.trans a⟩⟩
    | symplectic_derived he => exact .symplectic_derived ⟨e.trans he.some⟩
    | g2_derived he => exact .g2_derived ⟨e.trans he.some⟩
    | tits he => exact .tits ⟨e.trans he.some⟩
  | binary_linear d hd he => exact .binary_linear d hd (he.of_mulEquiv e)
  | sporadic name hn he => exact .sporadic name hn ⟨e.trans he.some⟩
  | janko_one he => exact .janko_one ⟨e.trans he.some⟩

private theorem local_eq_of_bender_quotient
    (T : Sylow 2 G) {X J : Subgroup G}
    (hX : X ∈ localCComponents T) (hJ : J ∈ localCComponents T)
    (hXJ : X ≤ J) (hm : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)) : X = J := by
  obtain ⟨S,_,hXS⟩ := BinaryIntrinsic.local_in_local_overgroup T hX hJ hXJ
  let eJ := subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left)
  have ht : (⊤ : Subgroup (J.subgroupOf (J ⊔ (T : Subgroup G)))).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.subgroupOf le_rfl
  have htJ : (⊤ : Subgroup J).IsCComponent := by
    simpa only [map_top_of_surjective eJ.toMonoidHom eJ.surjective] using ht.map_equiv eJ
  have hproper := isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    (bender_solvable_proper_sylow_overgroup hm)
  have htop := eq_of_solvable_sylow_overgroups S hXS htJ le_top
    (isSolvable_proper_sylow_overgroup_of_equiv (topEquiv (G := J)) hproper)
  exact le_antisymm hXJ (subgroupOf_eq_top.mp htop)

/-- The original binary-triality escape has original left degree two.
The containing point-component catalogue and the literal triality section
exclude strict enlargement; this does not identify the residual with PSL₂(4). -/
theorem original_binary_triality_degree_two
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) : n = 2 := by
  obtain ⟨hn,D,E,J,t,z,hDA,hDC,hDc,hDn,ht,htL,hi,hEA,hDE,hEc,hroot,hz,hz1,hEz,hinv,
    hXJ,hRJ,hJz,hJc,hJn,hJ,hEJ,hEbar,hsection,hcases,hP,hescapeP,hquasi,horder,
    hsporadic,halt,hlinear⟩ :=
    original_minus_torus_point_component_restrictions h hH hgen c hKH hK hKT horbit
      hY hescape C hC hKC hm
  rcases hcases with hn | ⟨hstrict,hnrank⟩
  · exact hn
  exfalso
  let X := C.map Y.subtype
  let Q := J ⧸ pCore 2 J
  let q := QuotientGroup.mk' (pCore 2 J)
  let I := (X.subgroupOf J).map q
  have hmI : Triality.Standard.IsTrialityGroupAt 2 (I ⧸ pCore 2 I) :=
    hm.of_mulEquiv hsection.some.symm
  let a := C.equivMapOfInjective Y.subtype Y.subtype_injective
  let b := subgroupOfEquivOfLe hXJ
  let : Group.IsPerfect C := hC.perfect
  let : Group.IsPerfect (X.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := (a.trans b.symm).toMonoidHom) (a.trans b.symm).surjective
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap (X.subgroupOf J)) (q.subgroupMap_surjective _)
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J := by
    have hs := (Chapter3.sqtk_of_mem_H h.qtke hP.1).subgroup
      (J.subgroupOf (centralizer ({z} : Set G)))
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hJz)).mp hs
  have hsq : IsSQTK KnownSimple.IsKnownSimple Q :=
    ChapterE.Structure.sqtk_two_quotient hsqJ (pCore 2 J) pCore_isPGroup
  let : IsQuasisimple Q := hquasi
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have htop : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,inferInstance⟩).isCComponent
  have hmod : TheoremCModel Q := by
    rcases quasisimple_containing_component_models_knownSimple hsq
      (pCore_quotient_pCore_eq_bot 2) htop with ⟨_,hm⟩ | ⟨hc,_⟩
    · exact theoremC_transport topEquiv.symm hm
    · have hcQ : Nonempty (center Q ≃* Multiplicative (ZMod 3)) :=
        ⟨(centerCongr (topEquiv (G := Q))).symm.trans hc.some⟩
      exact (triality_section_not_center_three hsq.stronglyQuasithin I hmI hcQ).elim
  cases hmod with
  | alternating d hd he => exact halt d hd.1 hd.2 he
  | linear_odd p e hp ho he hs hm =>
    exact triality_section_not_odd I hmI (.linear_two p e hp ho
      (by rcases he with rfl | rfl <;> decide) hm)
  | three_odd p hp ho u hm =>
    cases u with
    | false => exact triality_section_not_odd I hmI (.linear_three p hp ho hm)
    | true => exact triality_section_not_odd I hmI (.unitary_three p hp ho hm)
  | rank_two hm => exact hnrank hm
  | binary_linear d hd he => exact hlinear d hd he
  | sporadic name _ he => exact hsporadic (.inl ⟨name,he⟩)
  | janko_one he => exact hsporadic (.inr he)
  | rank_one hm =>
    have hcomp : (X.subgroupOf Y).IsCComponent := by
      change (C.map Y.subtype |>.comap Y.subtype).IsCComponent
      simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hC
    have hX : X ∈ localCComponents T :=
      hcomp.subgroupOf_of_le le_sup_left
        (sup_le (map_subtype_le C) (hH.1.1.2.trans hY.2))
    exact hstrict.ne (local_eq_of_bender_quotient T hX hJ.1 hXJ hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
