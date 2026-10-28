module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki
public import Theory.GroupTheory.CommutingThreePrimeRank
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesTransfer

/-!
# The Suzuki alternative beside the original PSL₃(4) component

Theorem A gives SQTK for semisimple subgroups of the actual action image.
The complete A.3.6 catalogue identifies its three-free components with
Suzuki matrix groups. Such a component is normal: otherwise it and a
conjugate, together with the original PSL₃(4), give five-rank at least three
inside the semisimple layer.

A minimum cubic offender therefore preserves an actual Suzuki Irr⁺ member.
D.2.7 passes its strict bound to that member's literal action image, while
the proved Suzuki endpoint gives the opposite bound two. The Chapter 12
application supplies the original quotient map and the moved component.
No middle-layer fixedness or small cubic bound is asserted here.

Source: Aschbacher--Smith 5.1.16(2), 5.1.23, D.3.8 and K.3.6,
printed pp.639,645--646,199,457, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
universe u v
variable {Y X : Type u} [Group Y] [Finite Y] [Group X] [Finite X]

/-- Semisimple subgroups of the actual quotient inherit the source odd-rank bound. -/
theorem semisimple_image_sqtk (f : Y →* X) (hf : Function.Surjective f)
    (hs : IsSQTK KnownSimple.IsKnownSimple Y) (J : Subgroup X)
    (hJ : ChapterA.Section02.IsSemisimple J) :
    IsSQTK KnownSimple.IsKnownSimple J := by
  have hsec : ChapterA.Section02.IsSectionOf J Y :=
    (ChapterA.Section02.IsSectionOf.subgroup J).ambient_surjective f hf
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hs.stronglyQuasithin hs.isKGroup hsec hJ,
    hsec.isKGroup hs.isKGroup⟩

theorem component_image_sqtk (f : Y →* X) (hf : Function.Surjective f)
    (hs : IsSQTK KnownSimple.IsKnownSimple Y) {J : Subgroup X}
    (hJ : IsComponent X J) : IsSQTK KnownSimple.IsKnownSimple J := by
  let := hJ.2
  apply semisimple_image_sqtk f hf hs J
  apply top_unique
  exact le_sSup (show IsComponent J ⊤ from
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩)

/-- The actual three-free component is a Suzuki matrix group. -/
theorem component_image_suzuki (f : Y →* X) (hf : Function.Surjective f)
    (hs : IsSQTK KnownSimple.IsKnownSimple Y) (hcore : pCore 2 X = ⊥)
    {J : Subgroup X} (hJ : IsComponent X J) (h3 : Nat.Coprime 3 (Nat.card J)) :
    ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) := by
  let := hJ.2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,hcore]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have htop : IsComponent J ⊤ :=
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩
  have hclass := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    J (component_image_sqtk f hf hs hJ) hJ2 ⊤ htop.isCComponent
  have h3top : Nat.Coprime 3 (Nat.card (⊤ : Subgroup J)) := by
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup J) ≃* J).toEquiv] using h3
  obtain ⟨r,hr,⟨e⟩⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.a36_suzuki_of_coprime
      hclass h3top
  exact ⟨r,by omega,⟨(topEquiv : (⊤ : Subgroup J) ≃* J).symm.trans e⟩⟩

omit [Finite X] in
private theorem five_dvd_psl_four (K : Subgroup X) (hm : ClassicalGroup.IsPSL K 3 4) :
    5 ∣ Nat.card K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hF, Matrix.PSL3Four.card_F])
  rw [Nat.card_congr (e.trans (Atlas.fieldEquivPSL 3 eF)).toEquiv,
    Matrix.PSL3Four.card_PSL]
  decide

private theorem five_dvd_suzuki (r : ℕ) (hr : 0 < r) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card r hr]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : (2 ^ (2*r+1)) ^ 2 = 4 * 16 ^ r := by
    rw [← pow_mul]
    have he : (2*r+1)*2 = 2+4*r := by omega
    rw [he,pow_add,pow_mul]
    norm_num
  rw [he,Nat.add_mod,Nat.mul_mod]
  have h16 : 16 ^ r % 5 = 1 := by
    change Nat.ModEq 5 (16 ^ r) 1
    simpa using (show Nat.ModEq 5 16 1 by decide).pow r
  rw [h16]

private theorem components_eq_of_five_rank
    (K P Q : Subgroup X) (hK : IsComponent X K) (hP : IsComponent X P)
    (hQ : IsComponent X Q) (hr : primeRank 5 (componentLayer X) ≤ 2)
    (hPK : P ≤ centralizer (K : Set X)) (hQK : Q ≤ centralizer (K : Set X))
    (hPz : Nat.Coprime 5 (Nat.card (center P)))
    (hQz : Nat.Coprime 5 (Nat.card (center Q)))
    (hdK : 5 ∣ Nat.card K) (hdP : 5 ∣ Nat.card P) (hdQ : 5 ∣ Nat.card Q) : P = Q := by
  by_contra hn
  have hPQ := commutator_eq_bot_iff_le_centralizer.mp (hP.commutator_eq_bot_of_ne hQ hn)
  let E := componentLayer X
  have hk : K ≤ E := le_sSup hK
  have hp : P ≤ E := le_sSup hP
  have hq : Q ≤ E := le_sSup hQ
  let eK := subgroupOfEquivOfLe hk
  let eP := subgroupOfEquivOfLe hp
  let eQ := subgroupOfEquivOfLe hq
  have hh := primeRank_three_of_commuting_of_centers_coprime (p := 5)
    (P.subgroupOf E) (Q.subgroupOf E) (K.subgroupOf E)
    (fun p hp q hq => Subtype.ext (hPQ hp q hq))
    (fun k hk p hp => Subtype.ext ((hPK hp k hk).symm))
    (fun k hk q hq => Subtype.ext ((hQK hq k hk).symm))
    (by rwa [Nat.card_congr (centerCongr eP).toEquiv])
    (by rwa [Nat.card_congr (centerCongr eQ).toEquiv])
    (by rwa [Nat.card_congr eP.toEquiv])
    (by rwa [Nat.card_congr eQ.toEquiv])
    (by rwa [Nat.card_congr eK.toEquiv])
  change 3 ≤ primeRank 5 (componentLayer X) at hh
  omega

/-- Five-rank rules out a second conjugate of the retained Suzuki component. -/
theorem suzuki_component_normal_beside_psl_four
    (f : Y →* X) (hf : Function.Surjective f)
    (hs : IsSQTK KnownSimple.IsKnownSimple Y)
    (K J : Subgroup X) [K.Normal] (hm : ClassicalGroup.IsPSL K 3 4)
    (hJ : IsComponent X J) (hJK : J ≤ centralizer (K : Set X))
    {r : ℕ} (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    J.Normal := by
  let := hJ.2
  let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm).1
  have hK : IsComponent X K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hE := semisimple_image_sqtk f hf hs (componentLayer X) componentLayer_idempotent
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 r hr).1
  let : IsSimpleGroup J := e.isSimpleGroup
  have hz : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hh))
  have hJz : Nat.Coprime 5 (Nat.card (center J)) := by simp [hz]
  have hdJ : 5 ∣ Nat.card J := by
    rw [Nat.card_congr e.toEquiv]
    exact five_dvd_suzuki r hr
  apply normal_iff_map_conj_eq.mpr
  intro a
  let Q := J.map (MulAut.conj a).toMonoidHom
  let eJ : J ≃* Q := J.equivMapOfInjective _ (MulAut.conj a).injective
  have hQK : Q ≤ centralizer (K : Set X) := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hJK
    exact hh.trans_eq (Normal.map_conj_eq (centralizer (K : Set X)) a)
  exact (components_eq_of_five_rank K J Q hK hJ (hJ.map_conj a)
    (hE.stronglyQuasithin 5 Nat.prime_five (by decide)) hJK hQK hJz
    (by rwa [← Nat.card_congr (centerCongr eJ).toEquiv])
    (five_dvd_psl_four K hm) hdJ (by rwa [← Nat.card_congr eJ.toEquiv])).symm

variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- An actual minimum cubic actor of ratio below two cannot move a normalized Suzuki component. -/
theorem no_small_starred_normalized_suzuki
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (J A : Subgroup X) (hJ : IsComponent X J)
    (hs : IsSQTK KnownSimple.IsKnownSimple J)
    (hn : A ≤ normalizer (J : Set X)) (hm : ⁅J,A⁆ ≠ ⊥)
    (hA : A ∈ ChapterD.QhatStar ρ) (hsmall : cubicRatio ρ < 2)
    {r : ℕ} (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) : False := by
  let := hJ.2
  have hJn : J ≠ ⊥ := by
    intro he
    exact hm (by simp only [he,commutator_bot_left])
  obtain ⟨I,hI,hAI⟩ := Chapter3.Section02.ChosenSource325.exists_invariant_irrPlus_of_suzuki
    ρ hf J A hJn hA.1.2.1.2 hn hr e
  have hcomm := hJ.commutator_eq_self_of_normalizes hn hm
  have hnon : ¬ I ≤ fixedSpace ρ A := by
    intro hi
    apply hI.not_le_fixedSpace ρ
    rw [← hcomm]
    exact le_fixedSpace_commutator_of_invariant ρ hI.choose hi
  have hR := ChapterD.RPlusBound.restricted ρ
    (show A ∈ ChapterD.RPlusBound ρ (cubicRatio ρ) from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le⟩,ChapterD.QhatStar.mem_RPlus ρ hA⟩) I hAI hnon
  have hQ : restrictedSubgroup ρ I A ∈ ChapterD.Qhat (subspaceImageRepresentation ρ I) :=
    ⟨hR.1,ChapterD.isCubic_restrictedSubgroup ρ I hA.1.2.2.1,hR.2.trans hA.1.1⟩
  have hlow := Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.SuzukiSupport.restricted_actor_ratio_ge_two
    ρ hs hI hAI hn hA.1.2.1.2 hr e hQ
  exact not_lt_of_ge hlow (hR.2.trans_lt hsmall)

/-- Discharge both the model and invariance premises for the component
selected in the original residual centralizer. -/
theorem no_small_starred_centralizer_component
    (f : Y →* X) (hf : Function.Surjective f)
    (hs : IsSQTK KnownSimple.IsKnownSimple Y) (hcore : pCore 2 X = ⊥)
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    (K J A : Subgroup X) [K.Normal] (hm : ClassicalGroup.IsPSL K 3 4)
    (hJ : IsComponent X J) (hJK : J ≤ centralizer (K : Set X))
    (h3 : Nat.Coprime 3 (Nat.card J)) (hA : A ∈ ChapterD.QhatStar ρ)
    (hmove : ⁅J,A⁆ ≠ ⊥) (hsmall : cubicRatio ρ < 2) : False := by
  obtain ⟨r,hr,⟨e⟩⟩ := component_image_suzuki f hf hs hcore hJ h3
  let := suzuki_component_normal_beside_psl_four f hf hs K J hm hJ hJK hr e
  exact no_small_starred_normalized_suzuki ρ hρ J A hJ
    (component_image_sqtk f hf hs hJ) (by rw [normalizer_eq_top]; exact le_top)
    hmove hA hsmall hr e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
