module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.CharacteristicTwo.Symplectic
public import Theory.SpecificGroups.G2.NoncyclicOddActor
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.CyclicOuter

/-!
# Excluding G₂ and completing the characteristic-two branch

The canonical radical and the specified component Sylow map through K/O₂(K)
and its center to the actual G₂ model. Noncyclic torus actors identify the
radical image's two-core with the full model Sylow. The Borel commutator
bound kills inner stabilizers on the original Frattini quotient, including
the kernel lifts through both preceding quotients. Consequently the actual
S₃ section would be a quotient of a subgroup of the cyclic outer group.

This eliminates the last characteristic-two star row without an assumed
model list or parabolic marking. The centralizer and TI consumers retain
only the ordinary irreducible and separate reducible component branches.
The ordinary branch and final irreducible assembly remain with
qt-d-1317-centralizer-irreducible; global assembly remains with
qt-d-1317-centralizer-sieve. The earlier SieveActions premise is produced
by qt-d-1317-module-orbits.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875; C.2.7, pp.145–147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- In the actual G₂ central model, the image of the canonical radical
has the full image of the component Sylow as its two-core. -/
theorem Context.g2_model_radical_core (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Atlas.G2.Model F) :
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
  have hqs : Function.Surjective q := j.surjective.comp
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
  let S' := S.mapSurjective hqs
  have hSY : (S' : Subgroup (Atlas.G2.Model F)) ≤ normalizer (Y : Set (Atlas.G2.Model F)) := by
    have hSK : (S : Subgroup K) ≤ normalizer (X.subgroupOf K : Set K) := by
      intro a ha
      exact X.le_normalizer_comap K.subtype (hSX (mem_map_of_mem K.subtype ha))
    exact (map_mono hSK).trans ((X.subgroupOf K).le_normalizer_map q)
  exact ⟨S,hS,Atlas.G2.NoncyclicOddActor.twoCore_eq_sylow hq h.odd Y B
    (map_mono (subgroupOf_mono K hPX)) (hP.of_mulEquiv ep).isPGroup
    (hP.of_mulEquiv ep).not_isCyclic S' hSY⟩


/-- Inner elements of the actual stabilizer action kill the original Frattini quotient. -/
theorem Context.g2_inner_kernel (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (hz2 : Nat.Coprime 2 (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Atlas.G2.Model F)
    (a : (L ⊓ centralizer ({u} : Set G) : Subgroup G)) (d : Atlas.G2.Model F)
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
  let f : X →* Atlas.G2.Model F := q.comp (inclusion hXK)
  let Y := (X.subgroupOf K).map q
  have hrange : f.range = Y := by rw [MonoidHom.range_comp,inclusion_range]
  have hshape := (RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  have hpre := componentCentralModelMap_core_preimage X K hXK hshape hz hz2 j
  obtain ⟨S,_,hcore⟩ := h.g2_model_radical_core s e hi hq hz j
  have hqs : Function.Surjective q := j.surjective.comp
    ((QuotientGroup.mk'_surjective (center (XiQuotient K))).comp
      (QuotientGroup.mk'_surjective (pCore 2 K)))
  let U : Sylow 2 (Atlas.G2.Model F) := S.mapSurjective hqs
  have hNY : normalizer (Y : Set (Atlas.G2.Model F)) ≤ normalizer (U : Set (Atlas.G2.Model F)) := by
    have hh := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
    change normalizer (Y : Set (Atlas.G2.Model F)) ≤ normalizer (Y.pCoreIn 2 : Set (Atlas.G2.Model F)) at hh
    rwa [hcore] at hh
  have hd : d ∈ normalizer (Y : Set (Atlas.G2.Model F)) := by
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
      have hc := Atlas.G2.NoncyclicOddActor.commutator_sylow_normalizer_le U
        (commutator_mem_commutator
          ((normalizer (U : Set (Atlas.G2.Model F))).inv_mem (hNY (Y.le_normalizer hxY))) (hNY hd))
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

/-- The original S₃ section excludes a G₂ central model once the genuine
center bound is supplied. The outer factorization is constructed in this proof. -/
theorem Context.not_g2_model (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SymmetricThreeStabilizerQuotient L p u)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (hz : Nat.Coprime p (Nat.card (center (XiQuotient K))))
    (hz2 : Nat.Coprime 2 (Nat.card (center (XiQuotient K))))
    (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* Atlas.G2.Model F) : False := by
  let A := L ⊓ centralizer ({u} : Set G)
  let τ := (MulAut.centralQuotientAction j).comp
    (componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi))
  let π := QuotientGroup.mk' (MulAut.innerSubgroup (Atlas.G2.Model F))
  let ω := π.comp τ
  let σ := componentStabilizerFrattiniAction L p u
  have hk : ω.ker ≤ σ.ker := by
    intro a ha
    have ht : τ a ∈ MulAut.innerSubgroup (Atlas.G2.Model F) := (QuotientGroup.eq_one_iff _).mp ha
    obtain ⟨d,hd⟩ := ht
    exact h.g2_inner_kernel s e hi hq hz hz2 j a d hd.symm
  let f : ω.range →* σ.range := ω.rangeRestrict.liftOfSurjective
    ω.rangeRestrict_surjective ⟨σ.rangeRestrict,by
      simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a,rfl⟩ := σ.rangeRestrict_surjective y
    exact ⟨ω.rangeRestrict a,by simp [f]⟩
  let : IsCyclic (MulAut.Outer (Atlas.G2.Model F)) :=
    Atlas.G2.LieAutomorphismExtensions.outer_isCyclic hq
  let : IsCyclic σ.range := isCyclic_of_surjective f hf
  obtain ⟨g,hg⟩ := hs
  let : IsCyclic (Equiv.Perm (Fin 3)) := isCyclic_of_surjective g hg
  have hc : (Equiv.swap (0 : Fin 3) 1) * Equiv.swap 1 2 =
      Equiv.swap 1 2 * Equiv.swap 0 1 := mul_comm' _ _
  have hh := congrArg (fun t : Equiv.Perm (Fin 3) => t 0) hc
  have hneq : (Equiv.swap (0 : Fin 3) 1) ((Equiv.swap 1 2) 0) ≠
      (Equiv.swap (1 : Fin 3) 2) ((Equiv.swap 0 1) 0) := by decide
  exact hneq hh


/-- The characteristic-two G₂ star row is excluded from the genuine source action. -/
theorem Context.not_g2_star (h : Context T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K)
    (hs : SymmetricThreeStabilizerQuotient L p u)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree)
    (jStar : starImage K (centralizerCore T L p u) K ≃* Atlas.G2.Model F.Carrier) : False := by
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show 2^1 < 2^F.degree from Nat.pow_lt_pow_right (by decide) hn)
  let input := h.characteristic_two_input c s hnt e hi hf
  have hb := (kernel_offender_from_source input).1.upper
  let eQ := coreStarCenterEquiv input.normalizes input.quasisimple
    (starImage_ne_bot_of_bound input.normalizes input.quasisimple hb)
  let j := (eQ.trans (componentModelCenterCongruence jStar)).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)).trans QuotientGroup.quotientBot)
  have hz : Nat.Coprime p (Nat.card (center (XiQuotient K))) ∧
      Nat.Coprime 2 (Nat.card (center (XiQuotient K))) := by
    rcases coreQuotient_center_card_from_source input with hc | hc
    · rw [hc]; exact ⟨Nat.coprime_one_right p,by decide⟩
    · rw [hc]
      exact ⟨(Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) h.prime_gt_three),by decide⟩
  exact h.not_g2_model s e hi hs hq hz.1 hz.2 j

/-- The characteristic-two alternative is impossible without an assumed model list.
The earlier quaternion and S₃ action data are the explicit SieveActions input. -/
theorem Context.not_characteristic_two_of_source_actions (h : Context T L p)
    (a : SieveActions h) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hf : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨F,hn,⟨j⟩⟩ := h.characteristic_two_g2_model a c s hnt e hi hf
  exact h.not_g2_star c s hnt e hi hf
    (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2 F hn j

/-- Literal centralizer application with the characteristic-two branch discharged.
The ordinary irreducible branch remains with this owner, the reducible branch
with its source owner, and SieveActions with qt-d-1317-module-orbits. -/
theorem Context.centralizer_le_of_ordinary_irreducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hordinary : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_g2_exclusion o a c hordinary _ hred hu hne
  intro v s hnt K e hi hf F hn hm
  exact h.not_g2_star c s hnt e hi hf
    (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2 F hn hm.some

/-- The TI consumer has no remaining characteristic-two model or geometry premise. -/
theorem Context.ti_of_ordinary_irreducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (a : SieveActions h) (c : Control T L p)
    (hordinary : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u →
        IsQuasisimple K → False)
    (hred : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u → False) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply h.ti_of_g2_exclusion o a c hordinary _ hred
  intro v s hnt K e hi hf F hn hm
  exact h.not_g2_star c s hnt e hi hf
    (h.sylow_reducible_and_symmetric_three a c s hnt e hi).2 F hn hm.some

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
