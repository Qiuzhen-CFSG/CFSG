module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.RankTwo
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.QuotientStabilizer
public import Theory.SpecificGroups.SymplecticFour.Sylow.NoncyclicOddActor
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CentralModel
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph

/-!
# Excluding the symplectic star component in the irreducible source branch

The actual map K → K/O₂(K) → (K/O₂(K))/Z transports the canonical odd
radical and the specified component Sylow to the Sp₄ model. The noncyclic
odd actor forces the radical image to have that full Sylow as its two-core.
Thus C_L(u) preserves it. An inner stabilizer belongs to its Borel, whose
commutator subgroup lies in the Sylow; it acts trivially on the original
Frattini quotient after lifting through the two-core and central kernels.
The S₃ quotient therefore factors through the cyclic outer group of Sp₄,
a contradiction. All kernel and normalization premises are constructed.

The characteristic-two source catalogue now leaves only G₂. The literal
centralizer and TI consumers retain that exclusion and the ordinary and
reducible component-normalizer branches. Their final assembly remains with
qt-d-1317-centralizer-irreducible (irreducible branches) and
qt-d-1317-centralizer-sieve (global assembly). The earlier SieveActions
construction remains with qt-d-1317-module-orbits.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875; C.2.7, pp.145–147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- In the actual symplectic central model, the image of the canonical radical
has the full image of the component Sylow as its two-core. -/
theorem Context.symplectic_model_radical_core (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Sp F) :
    ∃ S : Sylow 2 K,
      (S : Subgroup K).map K.subtype =
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ⊓ K ∧
      (((XiP p L).subgroupOf K).map (componentCentralModelMap K j)).pCoreIn 2 =
        (S : Subgroup K).map (componentCentralModelMap K j) := by
  let X := XiP p L
  have hXK : X ≤ K := h.radical_le_component s e hi
  have hshape := (RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  let P : Sylow p X := default
  let P₀ := (P : Subgroup X).map X.subtype
  have hPX : P₀ ≤ X := map_subtype_le _
  have hP : XiOddQuotient p P₀ := hshape.of_mulEquiv
    (RadicalActions.ambientSylowQuotientEquiv h.odd hshape.isPGroup P).symm
  let q := componentCentralModelMap K j
  have hq : Function.Surjective q := j.surjective.comp
    ((QuotientGroup.mk'_surjective (center (XiQuotient K))).comp
      (QuotientGroup.mk'_surjective (pCore 2 K)))
  let Y := (X.subgroupOf K).map q
  let B := (P₀.subgroupOf K).map q
  have hinj : Function.Injective (q.subgroupMap (P₀.subgroupOf K)) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P₀ => (z : G)) (componentCentralModelMap_injective_odd K P₀ (hPX.trans hXK)
      hP.isPGroup h.odd hz j
        (a₁ := ⟨a.val.val,a.property⟩) (a₂ := ⟨b.val.val,b.property⟩)
        (congrArg Subtype.val hab))
  let ep : P₀ ≃* B := (subgroupOfEquivOfLe (hPX.trans hXK)).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap (P₀.subgroupOf K))
      ⟨hinj,q.subgroupMap_surjective _⟩)
  let : Group.IsSolvable X := by
    let : Group.IsNilpotent (XiQuotient X) := hshape.isPGroup.isNilpotent
    let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable (X.subgroupOf K) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXK).toMonoidHom) (subgroupOfEquivOfLe hXK).injective
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  obtain ⟨S,hS,hSX⟩ := h.component_sylow e
  let S' := S.mapSurjective hq
  have hSY : (S' : Subgroup (Sp F)) ≤ normalizer (Y : Set (Sp F)) := by
    have hSK : (S : Subgroup K) ≤ normalizer (X.subgroupOf K : Set K) := by
      intro a ha
      exact X.le_normalizer_comap K.subtype (hSX (mem_map_of_mem K.subtype ha))
    exact (map_mono hSK).trans ((X.subgroupOf K).le_normalizer_map q)
  exact ⟨S,hS,NoncyclicOddActor.twoCore_eq_sylow hF hn h.odd Y B
    (map_mono (subgroupOf_mono K hPX)) (hP.of_mulEquiv ep).isPGroup
    (hP.of_mulEquiv ep).not_isCyclic S' hSY⟩


/-- The original stabilizer preserves the full model Sylow because it is the
constructed two-core of the radical image. -/
theorem Context.symplectic_model_stabilizer_sylow (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Sp F) :
    let q := componentCentralModelMap K j
    let τ := (MulAut.centralQuotientAction j).comp
      (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi))
    ∃ S : Sylow 2 K,
      (S : Subgroup K).map K.subtype =
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ⊓ K ∧
      (((XiP p L).subgroupOf K).map q).pCoreIn 2 = (S : Subgroup K).map q ∧
      ∀ a : (L ⊓ centralizer ({u} : Set G) : Subgroup G),
        ((S : Subgroup K).map q).map (τ a).toMonoidHom = (S : Subgroup K).map q := by
  obtain ⟨S,hS,hcore⟩ := h.symplectic_model_radical_core s e hi hF hn hz j
  refine ⟨S,hS,hcore,fun a => ?_⟩
  rw [← hcore,map_pCoreIn_of_injective 2 _ _ (MulEquiv.injective _),
    h.model_stabilizer_preserves_radical s e hi j a]

/-- The literal characteristic-two Sp₄ branch constructs the normalized model Sylow.
No marking of the radical core or assumption about its stabilizer is added. -/
theorem Context.symplectic_star_stabilizer_sylow (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree)
    (jStar : starImage K (centralizerCore T L p u) K ≃* Sp F.Carrier) :
    ∃ j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Sp F.Carrier,
      let q := componentCentralModelMap K j
      let τ := (MulAut.centralQuotientAction j).comp
        (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi))
      ∃ S : Sylow 2 K,
        (S : Subgroup K).map K.subtype =
          ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ⊓ K ∧
        (((XiP p L).subgroupOf K).map q).pCoreIn 2 = (S : Subgroup K).map q ∧
        ∀ a : (L ⊓ centralizer ({u} : Set G) : Subgroup G),
          ((S : Subgroup K).map q).map (τ a).toMonoidHom = (S : Subgroup K).map q := by
  let input := h.characteristic_two_input c s hnt e hi hf
  have hb := (kernel_offender_from_source input).1.upper
  let eQ := coreStarCenterEquiv input.normalizes input.quasisimple
    (starImage_ne_bot_of_bound input.normalizes input.quasisimple hb)
  let j := (eQ.trans (componentModelCenterCongruence jStar)).trans EvenProjective.equiv.symm
  have hz : Nat.Coprime p (Nat.card (center (XiQuotient K))) := by
    rcases coreQuotient_center_card_from_source input with hc | hc
    · rw [hc]; exact Nat.coprime_one_right p
    · rw [hc]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) h.prime_gt_three)
  exact ⟨j,h.symplectic_model_stabilizer_sylow s e hi F.card_eq hn hz j⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- Inner elements of the actual stabilizer action kill the original Frattini quotient. -/
theorem Context.symplectic_inner_kernel (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (hz2 : Nat.Coprime 2 (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Sp F)
    (a : (L ⊓ centralizer ({u} : Set G) : Subgroup G)) (d : Sp F)
    (ha : MulAut.centralQuotientAction j
      (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi) a) =
        MulAut.conj d) : componentStabilizerFrattiniAction L p u a = 1 := by
  let X := XiP p L
  let A := L ⊓ centralizer ({u} : Set G)
  have hAX : A ≤ normalizer (X : Set G) := inf_le_left.trans (XiP_invariant p L.le_normalizer)
  let _ := conjMulDistribMulActionOfLeNormalizer A X hAX
  let b := MulDistribMulAction.toMulAut A X a
  have hXK : X ≤ K := h.radical_le_component s e hi
  let q := componentCentralModelMap K j
  let f : X →* Sp F := q.comp (inclusion hXK)
  let Y := (X.subgroupOf K).map q
  have hrange : f.range = Y := by rw [MonoidHom.range_comp,inclusion_range]
  have hshape := (RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  have hpre := componentCentralModelMap_core_preimage X K hXK hshape hz hz2 j
  obtain ⟨S,_,hcore⟩ := h.symplectic_model_radical_core s e hi hF hn hz j
  have hq : Function.Surjective q := j.surjective.comp
    ((QuotientGroup.mk'_surjective (center (XiQuotient K))).comp
      (QuotientGroup.mk'_surjective (pCore 2 K)))
  let U : Sylow 2 (Sp F) := S.mapSurjective hq
  have hNY : normalizer (Y : Set (Sp F)) ≤ normalizer (U : Set (Sp F)) := by
    have hh := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
    change normalizer (Y : Set (Sp F)) ≤ normalizer (Y.pCoreIn 2 : Set (Sp F)) at hh
    rwa [hcore] at hh
  have hd : d ∈ normalizer (Y : Set (Sp F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := h.model_stabilizer_preserves_radical s e hi j a
    change Y.map (MulAut.centralQuotientAction j
      (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi) a)).toMonoidHom = Y at hh
    rwa [ha] at hh
  have heq (x : X) : f (b x) = d * f x * d⁻¹ := by
    have hh := componentCentralModelMap_conjugate K j
      (inclusion (h.stabilizer_normalizes_component s e hi) a) (inclusion hXK x)
    change f (b x) = _ at hh
    change f (b x) = (MulAut.centralQuotientAction j
      (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi) a)) (f x) at hh
    rw [ha] at hh
    exact hh
  have hdisp (x : X) : x⁻¹ * b x ∈ pCore 2 X := by
    have hxY : f x ∈ Y := hrange ▸ (show f x ∈ f.range from ⟨x,rfl⟩)
    have hc : f (x⁻¹ * b x) ∈ Y.pCoreIn 2 := by
      rw [map_mul,map_inv,heq,hcore]
      have hc := commutator_sylow_normalizer_le hF hn.le U
        (commutator_mem_commutator
          ((normalizer (U : Set (Sp F))).inv_mem (hNY (Y.le_normalizer hxY))) (hNY hd))
      simpa only [U, Sylow.coe_mapSurjective, commutatorElement_def,inv_inv,mul_assoc] using hc
    rw [← hrange] at hc
    obtain ⟨y,hy,he⟩ := hc
    have he' : y = f.rangeRestrict (x⁻¹ * b x) := Subtype.ext he
    have hmem : f.rangeRestrict (x⁻¹ * b x) ∈ pCore 2 f.range := he' ▸ hy
    exact hpre.le hmem
  apply MulEquiv.ext
  intro v
  induction v using QuotientGroup.induction_on with | H v =>
    induction v using QuotientGroup.induction_on with | H x =>
      have he : QuotientGroup.mk' (pCore 2 X) x = QuotientGroup.mk' (pCore 2 X) (b x) :=
        QuotientGroup.eq.mpr (hdisp x)
      change xiFrattiniAction A X hAX a
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)) = _
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
      exact congrArg (QuotientGroup.mk' (frattini (XiQuotient X))) he.symm

/-- The original S₃ section excludes a symplectic central model once the genuine
center bound is supplied. The outer factorization is constructed in this proof. -/
theorem Context.not_symplectic_model (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SymmetricThreeStabilizerQuotient L p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (hz2 : Nat.Coprime 2 (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Sp F) : False := by
  let A := L ⊓ centralizer ({u} : Set G)
  let τ := (MulAut.centralQuotientAction j).comp
    (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi))
  let π := QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  let ω := π.comp τ
  let σ := componentStabilizerFrattiniAction L p u
  have hk : ω.ker ≤ σ.ker := by
    intro a ha
    have ht : τ a ∈ MulAut.innerSubgroup (Sp F) := (QuotientGroup.eq_one_iff _).mp ha
    obtain ⟨d,hd⟩ := ht
    exact h.symplectic_inner_kernel s e hi hF hn hz hz2 j a d hd.symm
  let f : ω.range →* σ.range := ω.rangeRestrict.liftOfSurjective
    ω.rangeRestrict_surjective ⟨σ.rangeRestrict,by
      simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a,rfl⟩ := σ.rangeRestrict_surjective y
    exact ⟨ω.rangeRestrict a,by simp [f]⟩
  let : IsCyclic (MulAut.Outer (Sp F)) :=
    DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card hF hn
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let : IsCyclic σ.range := isCyclic_of_surjective f hf
  obtain ⟨g,hg⟩ := hs
  let : IsCyclic (Equiv.Perm (Fin 3)) := isCyclic_of_surjective g hg
  have hc : (Equiv.swap (0 : Fin 3) 1) * Equiv.swap 1 2 =
      Equiv.swap 1 2 * Equiv.swap 0 1 := mul_comm' _ _
  have hh := congrArg (fun t : Equiv.Perm (Fin 3) => t 0) hc
  have hneq : (Equiv.swap (0 : Fin 3) 1) ((Equiv.swap 1 2) 0) ≠
      (Equiv.swap (1 : Fin 3) 2) ((Equiv.swap 0 1) 0) := by decide
  exact hneq hh


/-- The characteristic-two Sp₄ star row is excluded from the genuine source action. -/
theorem Context.not_symplectic_star (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K)
    (hs : SymmetricThreeStabilizerQuotient L p u)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree)
    (jStar : starImage K (centralizerCore T L p u) K ≃* Sp F.Carrier) : False := by
  obtain ⟨j,_⟩ := h.symplectic_star_stabilizer_sylow c s hnt e hi hf F hn jStar
  let input := h.characteristic_two_input c s hnt e hi hf
  have hz : Nat.Coprime p (Nat.card (center (XiQuotient K))) ∧
      Nat.Coprime 2 (Nat.card (center (XiQuotient K))) := by
    rcases coreQuotient_center_card_from_source input with hc | hc
    · rw [hc]; exact ⟨Nat.coprime_one_right p,by decide⟩
    · rw [hc]
      exact ⟨(Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) h.prime_gt_three),by decide⟩
  exact h.not_symplectic_model s e hi hs F.card_eq hn hz.1 hz.2 j

/-- The source star catalogue now leaves only G₂; the symplectic inner-kernel
and outer-action premises have both been discharged. -/
theorem Context.characteristic_two_g2_model (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) :
    ∃ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree ∧
      Nonempty (starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier) := by
  rcases h.characteristic_two_rankTwo_models c s hnt e hi hf with ⟨F,hn,⟨j⟩⟩ | hg
  · exact (h.not_symplectic_star c s hnt e hi hf
      (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2 F hn j).elim
  · exact hg

/-- Literal centralizer application after elimination of the Sp₄ star family.
The earlier SieveActions producer is qt-d-1317-module-orbits. -/
theorem Context.centralizer_le_of_g2_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hordinary : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → False)
    (hg2 : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        generalizedFitting K = pCore 2 K →
        ∀ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree →
          Nonempty (starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier) → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_rankTwo_exclusions o c hordinary _ hg2 hred hu hne
  intro v s hnt K e hi hf F hn hm
  obtain ⟨j⟩ := hm
  exact h.not_symplectic_star c s hnt e hi hf
    (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2 F hn j

/-- TI uses the same source exclusions, with no residual symplectic callback. -/
theorem Context.ti_of_g2_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hordinary : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → False)
    (hg2 : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        generalizedFitting K = pCore 2 K →
        ∀ F : ChapterB.QuasisimpleSource.BinaryField, 1 < F.degree →
          Nonempty (starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier) → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_rankTwo_exclusions o c hordinary _ hg2 hred
  intro v s hnt K e hi hf F hn hm
  obtain ⟨j⟩ := hm
  exact h.not_symplectic_star c s hnt e hi hf
    (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2 F hn j

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
