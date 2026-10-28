module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognitionBounds
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualModels
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceOddNormalizerComplete
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original old residual: A₅ or the explicit PSL₃(4) exception

The complete source odd-normalizer theorem makes the original H-star Hall
Cartan cyclic of order three and fixes the nontrivial generation value at
two. A nonnormal source component would have a commuting Sylow conjugate;
their cubic tori force nine to divide the odd part of the actual maximal
subgroup. Hence the component is normal and equals the literal two-residual.
The normal marked-model analysis leaves exactly A₅ and PSL₃(4).

In the A₅ case, the separate bounds module kills the possible odd central
cover before transporting the equivalence to the original embedded O²(H).
The final overgroup-model consumer therefore needs no independent Cartan,
odd-normalizer, A₅-equivalence or plane-movement premise. It retains the
precise PSL₃(4) exclusion, source 9.3.1 line centralization, and source 9.3.6
nonzero overgroup core. The PSL₃(4) exclusion is not proved here.

The internal import exposes the definition identifying the source maximal
core with its normal core; it does not change that public definition.
Source: Aschbacher--Smith E.2.2, 9.2.7 and 9.3.6--7,
printed pp.215--216,731--734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceOldResidual
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

/-- A simple component and its commuting Sylow conjugate contribute two copies of the same subgroup order. -/
theorem paired_odd_square_dvd_maximal
    (hX : IsStronglyQuasithin X) (S : Sylow 2 X)
    (K : Subgroup X) (hK : IsComponent X K) [IsSimpleGroup K]
    (hgen : K ⊔ (S : Subgroup X) = ⊤) (hn : ¬K.Normal)
    (M : Subgroup X) (hSM : (S : Subgroup X) ≤ M)
    (C : Subgroup X) (hCK : C ≤ K) (hCM : C ≤ M) :
    Nat.card C * Nat.card C ∣ Nat.card M := by
  rcases ChapterE.Structure.component_normal_or_pair hX S hK hgen with h | ⟨t,hne,hD,hcomm,_,_,_,_⟩
  · exact (hn h.1).elim
  let D := K.map (MulAut.conj (t:X)).toMonoidHom
  have hDK : D ≤ centralizer (K : Set X) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_comm K D ▸ hcomm)
  let := hK.2
  have hz : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hz)).elim
  have hd : Disjoint K D := by
    apply disjoint_def.mpr
    intro x hxK hxD
    have hx : (⟨x,hxK⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun k => Subtype.ext (hDK hxD k k.property))
    exact congrArg Subtype.val (show (⟨x,hxK⟩ : K) = 1 from mem_bot.mp (hz ▸ hx))
  let E := C.map (MulAut.conj (t:X)).toMonoidHom
  have hED : E ≤ D := map_mono hCK
  have hEC : E ≤ centralizer (C : Set X) := (hED.trans hDK).trans (centralizer_le hCK)
  have hEM : E ≤ M := by
    have hh := map_mono (f := (MulAut.conj (t:X)).toMonoidHom) hCM
    have he : M.map (MulAut.conj (t:X)).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hSM t.property))
    exact hh.trans_eq he
  have hcard : Nat.card (C ⊔ E : Subgroup X) = Nat.card C * Nat.card C := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C E
      (hEC.trans (Subgroup.centralizer_le_normalizer _)) (hd.mono hCK hED)]
    rw [show Nat.card E = Nat.card C from card_map_of_injective (MulAut.conj (t:X)).injective]
  exact hcard ▸ card_dvd_of_le (sup_le hCM hEM)

/-- The exchanged field-four linear row forces an odd factor of nine in the actual maximal subgroup. -/
theorem not_exchanged_linear_four
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup X) = ⊤) (hn : ¬K.Normal)
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card (minimalParabolicMax S hP) → n ∣ 3)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (hm : ModelBorelPair (minimalParabolicMax S hP) K (BenderSuzuki.Converse.PBorel F)) : False := by
  let M := minimalParabolicMax S hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let K' := sourceImage M K
  let M' := sourceImage M M
  let : Group.IsSolvable J := minimalParabolic_core_solvable S hP
  have hi := ChapterE.Structure.source_component_simple_image S hP hs K hK hgen
  let : IsSimpleGroup K' := hi.1
  have hKn : ¬K'.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hK J hh)
  obtain ⟨e,he⟩ := hm
  let b := componentBorelEquiv (BenderSuzuki.Converse.PBorel F) e he
  let i : Fˣ →* X ⧸ J :=
    (sourceImage M (M ⊓ K)).subtype.comp (b.symm.toMonoidHom.comp Tori.psl2Torus)
  have hinj : Function.Injective i :=
    (sourceImage M (M ⊓ K)).subtype_injective.comp (b.symm.injective.comp Tori.psl2Torus_injective)
  let C := i.range
  have hC3 : Nat.card C = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,Nat.card_units,hF]
  have hCK : C ≤ K' := by
    rintro x ⟨a,rfl⟩
    exact map_mono (f := q) (show M ⊓ K ≤ K from inf_le_right)
      (b.symm (Tori.psl2Torus a)).property
  have hCM : C ≤ M' := by
    rintro x ⟨a,rfl⟩
    exact map_mono (f := q) (show M ⊓ K ≤ M from inf_le_left)
      (b.symm (Tori.psl2Torus a)).property
  have hS'M : (S' : Subgroup (X ⧸ J)) ≤ M' :=
    map_mono (minimalParabolicMax_spec S hP).2
  have hqthin : IsStronglyQuasithin (X ⧸ J) :=
    (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hX S hP hs).stronglyQuasithin
  have hKcomp : IsComponent (X ⧸ J) K' := hi.2.1
  have hKgen : K' ⊔ (S' : Subgroup (X ⧸ J)) = ⊤ := hi.2.2.2
  have hd := paired_odd_square_dvd_maximal hqthin
    S' K' hKcomp hKgen hKn M' hS'M C hCK hCM
  rw [hC3] at hd
  have hh := hsize 9 (by decide) (hd.trans (card_map_dvd _ _))
  norm_num at hh

/-- The source component is normal once the original maximal subgroup has odd Hall order three. -/
theorem generating_component_normal_of_three_hall_order
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬Group.IsSolvable X) (hn : 1 < generationParameter X)
    (K : Subgroup X) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card (minimalParabolicMax S hP) → n ∣ 3) : K.Normal := by
  by_contra hnot
  rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen hnot with
    ⟨f,hf,hm⟩ | ⟨p,hp,ho,h7,hm⟩
  · have hf2 := parameter_le_two_of_cyclic hsize (by omega) hm.cyclic
    have he : f=2 := by omega
    subst f
    rcases hm with ⟨F,hF,hfin,hchar,_,hcard,hB⟩ | ⟨m,hm,hf,_⟩
    · exact not_exchanged_linear_four hX S hP hs K hK hgen hnot hsize hcard hB
    · omega
  · let : Fact p.Prime := ⟨hp⟩
    have hb := paired_prime_parameter_le_one ChapterA.Section02.theoremA_knownSimple
      hX S hP hs K hK hgen hnot (p := p) (by omega) hm
    omega

/-- The literal two-residual is recognized modulo its two-core, with only the PSL₃(4) star-image exception. -/
theorem residual_a5_or_linear_three_four
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter X)
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card (minimalParabolicMax S hP) → n ∣ 3) :
    Nonempty ((pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) ≃* alternatingGroup (Fin 5)) ∨
      ((pResidual 2 X).IsCComponent ∧ IsQuasisimple (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) ∧
        ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) (pResidual 2 X)) 3 4) := by
  have hs : ¬Group.IsSolvable X := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,hqs,hgen,_⟩ := ChapterE.Structure.source_original_component hX S hP hs
  let := generating_component_normal_of_three_hall_order hX S hP hs hn K hK hgen hsize
  have hc := source_single_clauses S hP hs K hK hqs hgen
  have he := DiagramHall.single_component_eq_twoResidual S hK hc
  rcases normal_component_a5_or_linear_three_four hX S hP hs hn K hK hqs hgen hsize with h|h
  · exact .inl (he.symm ▸ h)
  · exact .inr (he.symm ▸ ⟨hK,hqs,h⟩)

end CFSG.Quasithin.Chapter10.SourceOldResidual

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open ChapterE.Section06.FixedPointBounds ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

private theorem original_oddNormalizer_control :
    ∀ (p : ℕ), p.Prime → Odd p → ∀ B : Subgroup G,
      B ≠ ⊥ → IsElementaryAbelian p B →
      B ≤ sectionCentralizer (localOrbit T L) → B ≤ centralizer (D.fullModule : Set G) →
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) →
      normalizer (B : Set G) ≤ D.maximalLocal := by
  intro p hp ho B hne hB hBC hBV hperm
  let : Fact p.Prime := ⟨hp⟩
  let := hB
  exact source_a5_oddPrimeNormalizer_control D e m.sylow_not_normalizes_component
    ho B hne hB.isPGroup hBC hBV hperm

/-- The original tensor setup gives exactly the two source generation values. -/
theorem hstar_generation_one_or_two
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H = 1 ∨ generationParameter H = 2 :=
  m.hstar_generation_one_or_two_of_control m.original_oddNormalizer_control hH

/-- The literal cyclic Hall Cartan and extended torus in the original tensor setup. -/
theorem hstar_cartan
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    generationParameter H = 2 ∧
    ∃ B A : Subgroup G, B ≤ H ∧ B ≤ (pResidual 2 H).map H.subtype ∧
      B ≤ A ∧ A ≤ sourceOrbitBorel T L ∧ Nat.card A = 9 ∧
      IsElementaryAbelian 3 A ∧ Nat.card B = 3 ∧ IsCyclic B ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (H ⊓ D.maximalLocal)) ∧
      B = A ⊓ centralizer (m.tensorLine : Set G) :=
  m.hstar_cartan_of_control m.original_oddNormalizer_control hH hlarge

/-- The original old residual moves the tensor plane. -/
theorem old_residual_moves_tensorPlane
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G) :=
  m.old_residual_moves_tensorPlane_of_control m.original_oddNormalizer_control hH hlarge


/-- Every odd divisor of the actual H-star maximal subgroup divides its constructed Hall order three. -/
theorem hstar_maximal_odd_order_dvd_three
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    ∀ n : ℕ, Odd n → n ∣ Nat.card (minimalParabolicMax (T.subtype hH.1.1.2) hP) → n ∣ 3 := by
  obtain ⟨_,B,A,hBH,_,hBA,hAM,_,_,hB3,_,hHall,_⟩ := m.hstar_cartan hH hlarge
  obtain ⟨_,_,_,_,hM,_⟩ := source_a5_hstar_cartan_data D e m.sylow_not_normalizes_component hH hlarge
  have hBM : B ≤ D.maximalLocal :=
    hBA.trans (hAM.trans ((map_subtype_le _).trans (inf_le_left.trans (localOrbit T L).le_normalizer)))
  have hcard : Nat.card (D.maximalLocal.subgroupOf H) = Nat.card (H ⊓ D.maximalLocal : Subgroup G) := by
    calc
      _ = Nat.card ((D.maximalLocal.subgroupOf H).map H.subtype) :=
        (card_map_of_injective H.subtype_injective).symm
      _ = _ := by rw [subgroupOf_map_subtype,inf_comm]
  dsimp only
  intro n ho hd
  rw [hM,hcard] at hd
  exact SourceOldResidual.odd_dvd_maximal_dvd_three (le_inf hBH hBM) hHall hB3 ho hd

/-- The original embedded old residual has A₅ quotient unless its literal source image is PSL₃(4). -/
theorem old_residual_a5_or_linear_three_four
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    Nonempty (((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) ∨
      ((pResidual 2 H).IsCComponent ∧ IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ∧
        ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax (T.subtype hH.1.1.2) hP)
          (pResidual 2 H)) 3 4) := by
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  rcases SourceOldResidual.residual_a5_or_linear_three_four
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) hP hlarge
    (m.hstar_maximal_odd_order_dvd_three hH hlarge) with ha | h
  · obtain ⟨a⟩ := ha
    let f := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let q := f.toMonoidHom.pCoreQuotientEquiv (p := 2) f.surjective
      (by rw [f.toMonoidHom.ker_eq_bot f.injective]; exact IsPGroup.of_bot)
    exact .inl ⟨q.symm.trans a⟩
  · exact .inr h

/-- A precise exclusion of the surviving PSL₃(4) image gives the original embedded A₅ equivalence. -/
theorem old_residual_a5_of_no_linear_three_four
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hlinear : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      (pResidual 2 H).IsCComponent → IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) →
        ¬ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax (T.subtype hH.1.1.2) hP)
          (pResidual 2 H)) 3 4) :
    Nonempty (((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) := by
  rcases m.old_residual_a5_or_linear_three_four hH hlarge with h | ⟨hc,hq,hl⟩
  · exact h
  · exact (hlinear hc hq hl).elim

/-- The original four-field overgroup models consume the proved Cartan, movement and residual recognition. -/
theorem old_residual_overgroup_fourField_models_of_no_linear_three_four
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hlinear : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      (pResidual 2 H).IsCComponent → IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) →
        ¬ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax (T.subtype hH.1.1.2) hP)
          (pResidual 2 H)) 3 4)
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData := by
  obtain ⟨eK⟩ := m.old_residual_a5_of_no_linear_three_four hH hlarge hlinear
  exact m.old_residual_overgroup_fourField_models_of_control
    m.original_oddNormalizer_control hH hlarge houtside eK M₀ hcore hgen hKU

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
