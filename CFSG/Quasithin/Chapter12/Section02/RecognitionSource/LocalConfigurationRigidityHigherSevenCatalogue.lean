module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherBinaryCatalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LocalQuotientEquality
public import Theory.SpecificGroups.AlternatingSeven.Containing
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension

/-!
# The actual A₇ projection of the proper containing component

In either surviving marked A₇ module row of the maximal component Y₀,
use its actual projection to Y₀/C_Y₀(W). Its kernel is solvable, with its
possible odd central part retained. Restriction to Y has two-group kernel:
the simple natural quotient makes the solvable radical of Y equal O₂(Y).
Order divisibility inside A₇ then forces d=4 and an image of order 168.

That image is maximal in A₇. If Y_R has the same image, perfection and
local component minimality lift equality through the central and two-core
quotients, contradicting Y<Y_R. Thus the actual Y_R projection is onto A₇.
The exhaustive source consumer records these maps and both original module
markings. Transport to the literal Y_R R/R image and the nonquasisimple
maximal-overcomponent case remain with qt-d-12213-local-rigidity, together
with residual normality and final assembly. This is not the full 12.2.25.

Source: Aschbacher–Smith, original 12.2.2(3), A.3.12 and 12.2.25,
printed pp.795,47–48,805.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

theorem residual_seven_image_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d)
    (f : rigidityHyperplaneResidual L U V →* alternatingGroup (Fin 7))
    [Group.IsSolvable f.ker] : d = 4 ∧ Nat.card f.range = 168 := by
  let Y := rigidityHyperplaneResidual L U V
  let := Chapter1.mem_L_isPerfect (residual_mem_local_family D A C hd
    (((structural G T L h).2.2 V D).1))
  let := (hyperplaneAut_simple_perfect C hd).1
  let : IsSimpleGroup (Y ⧸ pCore 2 Y) := (residualQuotientAutEquiv D A C hd).isSimpleGroup
  have hk : IsPGroup 2 f.ker := by
    apply pCore_isPGroup.to_le
    rw [← radical_eq_core_of_perfect_simple_core_quotient]
    exact le_solvableRadical _ inferInstance inferInstance
  let e := f.rangeRestrict.pCoreQuotientEquiv (p := 2) f.rangeRestrict_surjective (by
    show IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hk)
  have hc : Nat.card (f.range ⧸ pCore 2 f.range) = if d = 4 then 168 else 20160 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr (residualQuotientAutEquiv D A C hd).toEquiv]
    exact hyperplaneAut_card D A C hd
  obtain ⟨k,hkcard⟩ := (pCore_isPGroup (p := 2) (G := f.range)).exists_card_eq
  have hdiv : (if d = 4 then 168 else 20160) * 2^k ∣ 2520 := by
    have hh := f.range.card_subgroup_dvd_card
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range),hc,hkcard] at hh
    simpa only [nat_card_alternatingGroup,Nat.card_fin,show Nat.factorial 7 / 2 = 2520 from by decide] using hh
  have hd4 : d = 4 := by
    by_contra hh
    rw [if_neg hh] at hdiv
    have hh := (dvd_mul_right 20160 (2^k)).trans hdiv
    norm_num at hh
  rw [if_pos hd4] at hc hdiv
  have hpow : 2^k ∣ 15 := by
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 168)).mp hdiv
  have hone : 2^k = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 15).pow_left k) (dvd_refl _) hpow
  refine ⟨hd4,?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 f.range),hc,hkcard,hone,mul_one]

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory
open ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual seven-point action quotient of the original chosen module. -/
def chosenSevenProjection {K₀ W : Subgroup G} (E : ChosenModule T K₀ W)
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    K₀ →* alternatingGroup (Fin 7) := by
  let := E.actionCentralizer_normal
  exact e.toMonoidHom.comp (QuotientGroup.mk' _)

private theorem chosen_seven_core_kernel_central {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    letI := E.actionCentralizer_normal
    (e.toMonoidHom.comp E.coreToFaithful).ker ≤ center (K₀ ⧸ pCore 2 K₀) := by
  let := E.actionCentralizer_normal
  let := hq
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp E.coreToFaithful_surjective
  apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
  intro ht
  have hz : f = 1 := f.ker_eq_top_iff.mp ht
  have hone (x : alternatingGroup (Fin 7)) : x = 1 := by
    obtain ⟨y,rfl⟩ := hf x
    exact DFunLike.congr_fun hz y
  obtain ⟨x,hx⟩ := exists_ne (1 : alternatingGroup (Fin 7))
  exact hx (hone x)

/-- The kernel of the seven-point projection is solvable, including its
possible central odd part; it is not identified with the two-core. -/
theorem chosenSevenProjection_kernel_solvable {K₀ W : Subgroup G}
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    Group.IsSolvable (chosenSevenProjection E e).ker := by
  let := E.actionCentralizer_normal
  let f := e.toMonoidHom.comp E.coreToFaithful
  have hk := chosen_seven_core_kernel_central E hq e
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm
    (fun x y => Subtype.ext (mem_center_iff.mp (hk y.property) x.val))
  let q := QuotientGroup.mk' (pCore 2 K₀)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 K₀) := pCore_isPGroup.isNilpotent
    infer_instance
  exact isSolvable_comap_of_solvable_ker q f.ker

private theorem restriction_range {X Q : Type*} [Group X] [Group Q]
    {B K : Subgroup X} (hBK : B ≤ K) (f : K →* Q) :
    (f.comp (inclusion hBK)).range = (B.subgroupOf K).map f := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨inclusion hBK b,b.property,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,rfl⟩

/-- A proper containing component in either marked A7 row surjects onto
that exact A7 quotient. The residual has its actual order-168 image. -/
theorem proper_containing_seven_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : 3 < d) {K K₀ W : Subgroup G}
    (hYK : rigidityHyperplaneResidual L U V < K)
    (hlocal : K ∈ Chapter1.L G (T : Subgroup G)) (hKK₀ : K ≤ K₀)
    (hK₀ : K₀ ∈ Chapter1.L G (T : Subgroup G))
    (E : ChosenModule T K₀ W) (hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀))
    (e : letI := E.actionCentralizer_normal
      (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7)) :
    d = 4 ∧
      Nat.card (((rigidityHyperplaneResidual L U V).subgroupOf K₀).map
        (chosenSevenProjection E e)) = 168 ∧
      Function.Surjective ((chosenSevenProjection E e).comp (inclusion hKK₀)) := by
  let := E.actionCentralizer_normal
  let Y := rigidityHyperplaneResidual L U V
  let F := chosenSevenProjection E e
  have hYK₀ : Y ≤ K₀ := hYK.le.trans hKK₀
  let f := F.comp (inclusion hYK₀)
  let : Group.IsSolvable F.ker := chosenSevenProjection_kernel_solvable E hq e
  let j : f.ker →* F.ker :=
    { toFun := fun x => ⟨inclusion hYK₀ x.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun x y hh => Subtype.ext (Subtype.ext
      (congrArg (fun z : F.ker => (z.val : G)) hh)))
  obtain ⟨hd4,hcard⟩ := residual_seven_image_card h D structural A C hd f
  have hycard : Nat.card ((Y.subgroupOf K₀).map F) = 168 := by
    rwa [restriction_range hYK₀ F] at hcard
  have heq_or := AlternatingSeven.Containing.eq_or_top_of_card
    ((Y.subgroupOf K₀).map F) ((K.subgroupOf K₀).map F) hycard (map_mono (comap_mono hYK.le))
  refine ⟨hd4,hycard,?_⟩
  rcases heq_or with heq | htop
  · obtain ⟨S,hS,hKS⟩ := BinaryIntrinsic.local_in_local_overgroup T hlocal.1 hK₀.1 hKK₀
    have hYS : Y.subgroupOf K₀ ∈ ChapterA.Section03.localCComponents S := by
      rw [hS]
      exact local_restrict (residual_mem_local_family D A C hd
        (((structural G T L h).2.2 V D).1)).1 hYK₀
    have hh : Y.subgroupOf K₀ = K.subgroupOf K₀ :=
      local_eq_of_central_twoCore_map_eq S hYS hKS (comap_mono hYK.le)
        (e.toMonoidHom.comp E.coreToFaithful) (chosen_seven_core_kernel_central E hq e) heq.symm
    have hm := congrArg (map K₀.subtype) hh
    rw [map_subgroupOf_eq_of_le hYK₀,map_subgroupOf_eq_of_le hKK₀] at hm
    exact (hYK.ne hm).elim
  · apply MonoidHom.range_eq_top.mp
    rw [restriction_range hKK₀ F]
    exact htop

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The original exhaustive source reduction now retains a surjection from the
actual proper containing component to the marked seven-point quotient, and
identifies the smaller image there. The nonquasisimple head and the central
cover of this projection remain to be discharged by the final rigidity owner. -/
theorem source_rigidity_or_marked_seven_projection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222Modules.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d) :
    (normalizer (sectionRadical T U : Set G) ≤ normalizer (rigidityHyperplaneResidual L U V : Set G) ∧
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U) ∨
    ∃ K K₀ : Subgroup G,
      K ≤ normalizer (sectionRadical T U : Set G) ∧
      (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent ∧
      rigidityHyperplaneResidual L U V < K ∧
      normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G) ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ hKK₀ : K ≤ K₀, FaithfulMaximalLocal T K₀ ∧
      pCore 2 (ThreeRigidity.image T U K) ≤ center (ThreeRigidity.image T U K) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 ∧
      ((¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀)) ∨
        (IsQuasisimple (K₀ ⧸ pCore 2 K₀) ∧
        ∃ W : Subgroup G, ∃ E : ChosenModule T K₀ W, ExceptionalContainingModuleRows E ∧
        letI := E.actionCentralizer_normal
        ∃ e : (K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃* alternatingGroup (Fin 7),
          d = 4 ∧
          Nat.card (((rigidityHyperplaneResidual L U V).subgroupOf K₀).map
            (chosenSevenProjection E e)) = 168 ∧
          Function.Surjective ((chosenSevenProjection E e).comp (inclusion hKK₀)))) := by
  rcases source_rigidity_or_exceptional_containing_rows h D structural modules A C hnone hd with hc | hc
  · exact Or.inl hc
  · obtain ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,hrows⟩ := hc
    refine Or.inr ⟨K,K₀,hKN,hK,hYK,hn,hlocal,hKK₀,hK₀,hcore,hseven,?_⟩
    rcases hrows with hnot | ⟨W,E,hrows⟩
    · exact Or.inl hnot
    · by_cases hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀)
      · refine Or.inr ⟨hq,W,E,hrows,?_⟩
        let := E.actionCentralizer_normal
        have he : Nonempty ((K₀ ⧸ (centralizer (W : Set G)).subgroupOf K₀) ≃*
            alternatingGroup (Fin 7)) := by
          cases hrows with
          | alternatingSeven e => exact ⟨e.groupEquiv⟩
          | alternatingSevenFour e _ => exact ⟨e⟩
        obtain ⟨e⟩ := he
        exact ⟨e,proper_containing_seven_projection h D structural A C hd hYK hlocal hKK₀
          hK₀.1.1 E hq e⟩
      · exact Or.inl hq

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
