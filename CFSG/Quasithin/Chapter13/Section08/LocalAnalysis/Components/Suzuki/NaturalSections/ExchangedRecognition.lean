module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SourceRecognition
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.OriginalNonnormal

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.PairQuotient

/-!
# The full moved natural section of an exchanged Suzuki pair

The quadratic four-group theorem excludes an actor exchanging Suzuki factors:
its PSL₂ conclusion contradicts the Suzuki order being prime to three. Select
an inclusion-minimal bounded subactor and, if necessary, conjugate it onto the
chosen factor. Odd outer order supplies an invariant Irr⁺ constituent. Its
Suzuki lower bound forces equality in the restriction estimate; a nonzero
restriction kernel would be a smaller bounded subactor. The resulting fixed
space supplement identifies this constituent with the whole moved space.

The normalizing-actor recognition gives its natural central quotient.
Conjugation gives the second factor. Each perfect factor fixes the other's
moved space, so addition identifies the literal full moved central quotient
with the two natural modules. The actor equivalence is onto the full Suzuki
product; no splitting of the original moved space is assumed.
`ExchangedSource` supplies the actual F.9.18 actor and applies this result to
the original 13.8.16 contradiction.

Source: Aschbacher--Smith, D.2.4--5, pp.178--179; F.9.18(5--7),
pp.325--326; K.3.6, p.457; 13.8.16, pp.952--953.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.ExchangedRecognition
open Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
universe u
variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- A quadratic actor with the source bound preserves every Suzuki factor.
An exchanged factor would instead be PSL₂ by quadratic four-group recognition. -/
theorem quadratic_actor_normalizes
    (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}
    (geo : ExchangedGeometry K K₀ T B C)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hf : Function.Injective ρ) (hK : IsComponent D K)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hAT : A ≤ T) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hd : fixedCodim ρ A ≤ 2 * rank A) : A ≤ normalizer (K : Set D) := by
  by_contra hp
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple K := hK.2
  let : IsElementaryAbelian 2 A := hA.2
  have hZ := SectionRecognition.center_eq_bot_of_equiv_suzuki eK
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨F,a,hF,_⟩ := Exchanged.moving_fourGroup_of_small_ratio ρ geo hTK hf hK hAT hq hAC hp hd
  obtain ⟨M,f,hf,hker,_⟩ := ChapterB.ComponentNormalization.QuadraticSource.exists_marked_model hF
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (hker.trans hZ)
  let e := (MulEquiv.ofBijective f ⟨hinj,hf⟩).symm.trans eK
  apply suzukiMatrixGroup_three_free m hm
  rw [← Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card (GaloisField 2 M.n) 2 (by decide)

/-- Recognition for a Suzuki component normalized by its faithful quadratic actor.
Normality is required only inside the actual generated subgroup K A. -/
theorem natural_moved_of_normalizing_actor
    (ρ : Representation (ZMod 2) D V) (K A : Subgroup D)
    [IsQuasisimple K] (hAN : A ≤ normalizer (K : Set D))
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K
      (subspaceCommutator ρ ⊤ K) (subspaceCommutator_invariant ρ ⊤ K)) (natural m)) := by
  let E := K ⊔ A
  let L := K.subgroupOf E
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer (show K ≤ E from le_sup_left)).mpr
    (sup_le K.le_normalizer hAN)
  let f : L ≃* K := subgroupOfEquivOfLe (show K ≤ E from le_sup_left)
  let : IsQuasisimple L :=
    Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.componentInSup_quasisimple K A
  have hn' : ¬ L ≤ (ρ.comp E.subtype).ker := by
    intro hh
    apply hn
    intro k hk
    exact hh (show (⟨k,(le_sup_left : K ≤ E) hk⟩ : E) ∈ L from hk)
  have hmove : subspaceCommutator (ρ.comp E.subtype) ⊤ L = subspaceCommutator ρ ⊤ K := by
    unfold subspaceCommutator
    congr 1
    ext v
    constructor
    · rintro ⟨k,hk,w,hw,rfl⟩
      exact ⟨k,hk,w,hw,rfl⟩
    · rintro ⟨k,hk,w,hw,rfl⟩
      exact ⟨⟨k,(le_sup_left : K ≤ E) hk⟩,hk,w,hw,rfl⟩
  obtain ⟨a⟩ := SourceRecognition.natural_moved_of_quadratic_supplement (ρ.comp E.subtype) L (A.subgroupOf E)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.componentInSup_generated K A)
    hm (f.trans eK) (hs.subgroup E)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_elementary K A hA)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_quadratic ρ K A hq)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_bound ρ K A hc)
    (Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal.actorInSup_faithful K A hAC) hn'
  have changeSpace (W I : Submodule (ZMod 2) V)
      (hW : L ≤ subspaceStabilizer (ρ.comp E.subtype) W)
      (hI : L ≤ subspaceStabilizer (ρ.comp E.subtype) I) (he : W = I) :
      Nonempty (ActionEquiv (centralQuotientRepresentation (ρ.comp E.subtype) L W hW) (natural m)) →
      Nonempty (ActionEquiv (centralQuotientRepresentation (ρ.comp E.subtype) L I hI) (natural m)) := by
    subst I
    exact id
  obtain ⟨a⟩ := changeSpace _ _ _
    (hmove ▸ subspaceCommutator_invariant (ρ.comp E.subtype) ⊤ L) hmove ⟨a⟩
  let q := subgroupCentralQuotientEquiv ρ K E (show K ≤ E from le_sup_left)
    (subspaceCommutator ρ ⊤ K)
  have hqact (k : K) (v : centralQuotient (ρ.comp E.subtype) L (subspaceCommutator ρ ⊤ K)) :
      q (centralQuotientRepresentation (ρ.comp E.subtype) L _
        (hmove ▸ subspaceCommutator_invariant (ρ.comp E.subtype) ⊤ L) (f.symm k) v) =
      centralQuotientRepresentation ρ K _ (subspaceCommutator_invariant ρ ⊤ K) k (q v) := by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl
  refine ⟨⟨f.symm.trans a.groupEquiv,q.symm.trans a.linearEquiv,?_⟩⟩
  intro k v
  obtain ⟨v,rfl⟩ := q.surjective v
  change a.linearEquiv (q.symm (centralQuotientRepresentation ρ K _
    (subspaceCommutator_invariant ρ ⊤ K) k (q v))) =
    natural m (a.groupEquiv (f.symm k)) (a.linearEquiv (q.symm (q v)))
  rw [← hqact,q.symm_apply_apply,q.symm_apply_apply]
  exact a.intertwines (f.symm k) v


omit [Finite V] in
/-- Choose an inclusion-minimal subgroup satisfying the original quadratic ratio bound. -/
theorem exists_minimal_bounded_actor
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D) (hA : IsElementaryTwo A)
    (hb : actionRatio ρ A ≤ 2) :
    ∃ J ≤ A, J ∈ ChapterD.RPlusBound ρ 2 ∧
      ∀ B ≤ J, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J := by
  classical
  let S : Set (Subgroup D) := {J | J ≤ A ∧ J ≠ ⊥ ∧ actionRatio ρ J ≤ 2}
  obtain ⟨J,hJ,hmin⟩ := Set.exists_min_image S (fun B => Nat.card B)
    (Set.toFinite _) ⟨A,le_rfl,hA.1,hb⟩
  have hminimal : ∀ B ≤ J, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J := by
    intro B hBJ hn hc
    exact eq_of_le_of_card_ge hBJ (hmin B ⟨hBJ.trans hJ.1,hn,hc⟩)
  have he := hA.of_le hJ.1 hJ.2.1
  refine ⟨J,hJ.1,⟨⟨he,hJ.2.2⟩,he,?_⟩,hminimal⟩
  intro B hBJ hn
  by_cases hb : actionRatio ρ B ≤ 2
  · rw [hminimal B hBJ hn hb]
  · exact hJ.2.2.trans (le_of_not_ge hb)

/-- The Suzuki endpoint and minimality eliminate the restricted actor kernel. -/
theorem minimal_actor_faithful
    (ρ : Representation (ZMod 2) D V) (K J : Subgroup D) [IsQuasisimple K]
    (hf : Function.Injective ρ) (hs : IsSQTK KnownSimple.IsKnownSimple K)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hJN : J ≤ normalizer (K : Set D)) (hnJ : ¬ J ≤ centralizer (K : Set D))
    (hJ : J ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ J)
    (hmin : ∀ B ≤ J, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J) :
    J ⊓ centralizer (K : Set D) = ⊥ ∧
      ∃ I : Submodule (ZMod 2) V, IsIrrPlus ρ K I ∧
        J ≤ subspaceStabilizer ρ I ∧ I ⊔ fixedSpace ρ J = ⊤ := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  obtain ⟨I,hI,hJI⟩ := Chapter3.Section02.ChosenSource325.exists_invariant_irrPlus_of_suzuki
    ρ hf K J ((nontrivial_iff_ne_bot K).mp inferInstance) hJ.1.1.2 hJN hm eK
  have hnI : ¬ I ≤ fixedSpace ρ J := by
    intro hh
    apply hnJ
    intro j hj
    exact centralizes_of_fixes_faithful_section ρ K I hI.choose
      (hI.component_faithful ρ K (SectionRecognition.center_eq_bot_of_equiv_suzuki eK))
      (hJN hj) (fun v hv => hh hv ⟨j,hj⟩)
  have hr := ChapterD.RPlusBound.restricted ρ hJ I hJI hnI
  have hl := Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.SuzukiSupport.restricted_actor_ratio_ge_two
    ρ hs hI hJI hJN hJ.1.1.2 hm eK
    ⟨hr.1,ChapterD.isCubic_restrictedSubgroup ρ I (isCubic_of_isQuadratic hq),hr.2⟩
  have hk : subspaceKernel ρ I J = ⊥ ∧ I ⊔ fixedSpace ρ J = ⊤ := by
    rcases ChapterD.RPlus.restriction_alternatives ρ hJ.2 I hJI hnI with hlt | hfaith | hker
    · exact (not_lt_of_ge hl (hlt.trans_le hJ.1.2)).elim
    · exact ⟨hfaith.1,hfaith.2.1⟩
    · have he := hmin (subspaceKernel ρ I J) (subspaceKernel_le ρ I J) hker.1.1.1
        (hker.2.2.1.le.trans hJ.1.2)
      exact (subspaceKernel_ne_self ρ I hnI he).elim
  have hJC : J ⊓ centralizer (K : Set D) = ⊥ := by
    let Q := J ⊓ centralizer (K : Set D)
    let : IsElementaryAbelian 2 J := hJ.1.1.2
    have hp : IsPGroup 2 Q := (IsElementaryAbelian.isPGroup 2 J).of_injective
      (inclusion (show Q ≤ J from inf_le_left)) (inclusion_injective _)
    have hfix := Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hI hp
      (show Q ≤ centralizer (K : Set D) from inf_le_right)
      ((show Q ≤ J from inf_le_left).trans hJI)
    apply bot_unique
    intro j hj
    apply hk.1.le
    exact ⟨hj.1,fun v hv => hfix hv ⟨j,hj⟩⟩
  exact ⟨hJC,I,hI,hJI,hk.2⟩

/-- The fixed-space supplement saturates the whole moved space and recognizes
its literal natural central quotient. -/
theorem minimal_actor_moved_natural
    (ρ : Representation (ZMod 2) D V) (K J : Subgroup D) (hK : IsComponent D K)
    (hf : Function.Injective ρ) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hJN : J ≤ normalizer (K : Set D)) (hnJ : ¬ J ≤ centralizer (K : Set D))
    (hJ : J ∈ ChapterD.RPlusBound ρ 2) (hq : IsQuadratic ρ J)
    (hmin : ∀ B ≤ J, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J) :
    IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) ∧
      Nonempty (ActionEquiv (centralQuotientRepresentation ρ K
        (subspaceCommutator ρ ⊤ K) (subspaceCommutator_invariant ρ ⊤ K)) (natural m)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsQuasisimple K := hK.2
  obtain ⟨hc,I,hI,hJI,hspan⟩ := minimal_actor_faithful ρ K J hf (hs.subgroup K) hm eK
    hJN hnJ hJ hq hmin
  have hKJ : ⁅K,J⁆ = K := by
    rcases hK.commutator_dichotomy J with hb | he
    · exact (hnJ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))).elim
    · exact he.trans (le_antisymm (iSup_conjugates_le_of_le_normalizer K J K le_rfl hJN)
        (le_componentOrbit K J))
  have he : subspaceCommutator ρ ⊤ K = I := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,v,_,rfl⟩
      obtain ⟨i,hi,c,hc,rfl⟩ := Submodule.mem_sup.mp (show v ∈ I ⊔ fixedSpace ρ J by rw [hspan]; trivial)
      have hdiff := differences_mem_of_invariant_mod_fixed ρ hI.choose hJI
        (show K ≤ subspaceStabilizer ρ (fixedSpace ρ J ⊔ I) by
          rw [sup_comm,hspan]; exact le_subspaceStabilizer ρ ⊤ (by intros; trivial))
        (le_rfl : fixedSpace ρ J ≤ fixedSpace ρ J) hKJ c hc k hk
      have hh : ρ k (i+c) - (i+c) = (ρ k i-i)+(ρ k c-c) := by rw [map_add]; abel
      rw [hh]
      exact I.add_mem (I.sub_mem ((hI.choose hk i).2 hi) hi) hdiff
    · rw [← hI.choose_spec.1]
      exact subspaceCommutator_mono_left ρ le_top K
  refine ⟨he ▸ hI, natural_moved_of_normalizing_actor ρ K J hJN hm eK hs
    hJ.1.1 hq ((actionRatio_le_nat_iff ρ hJ.1.1 2).mp hJ.1.2) hc ?_⟩
  intro hh
  exact hI.not_le_fixedSpace ρ (fun v _ k => LinearMap.congr_fun (hh k.property) v)



omit [Finite D] in
/-- Inclusion minimality of a bounded actor is preserved by conjugation. -/
theorem minimal_bound_conjugate
    (ρ : Representation (ZMod 2) D V) (J : Subgroup D) (g : D)
    (hmin : ∀ B ≤ J, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J) :
    ∀ B ≤ J.conjBy g, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J.conjBy g := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let e := (MulAut.conj g).mapSubgroup
  intro B hBJ hB hr
  have hle : e.symm B ≤ J := e.symm_apply_le.mpr hBJ
  have hn : e.symm B ≠ ⊥ := by
    intro hh
    apply hB
    calc
      B = e (e.symm B) := (e.apply_symm_apply B).symm
      _ = ⊥ := by rw [hh,e.map_bot]
  have he : actionRatio ρ B = actionRatio ρ (e.symm B) := by
    have h := ChapterD.actionRatio_map_conj ρ (e.symm B) g
    change actionRatio ρ (e (e.symm B)) = _ at h
    simpa only [e.apply_symm_apply] using h
  have hh := hmin (e.symm B) hle hn (he ▸ hr)
  exact e.symm.injective (hh.trans (e.symm_apply_apply J).symm)

omit [Finite D] [Finite V] in
private theorem quadratic_conjugate (ρ : Representation (ZMod 2) D V)
    {A : Subgroup D} (hq : IsQuadratic ρ A) (g : D) : IsQuadratic ρ (A.conjBy g) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (g*a*g⁻¹) (ρ (g*b*g⁻¹) v-v) = ρ (g*b*g⁻¹) v-v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,ρ.inv_self_apply,ρ.self_inv_apply] using hh

/-- Conjugate a minimal actor onto the chosen factor when it centralizes that factor. -/
theorem exists_minimal_actor_on_factor
    (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}
    (geo : ExchangedGeometry K K₀ T B C)
    (hindex : (normalizer (K : Set D)).index = 2)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hf : Function.Injective ρ) (hK : IsComponent D K)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hAT : A ≤ T) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hd : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ J : Subgroup D, J ≤ normalizer (K : Set D) ∧ ¬ J ≤ centralizer (K : Set D) ∧
      J ∈ ChapterD.RPlusBound ρ 2 ∧ IsQuadratic ρ J ∧
      ∀ B ≤ J, B ≠ ⊥ → actionRatio ρ B ≤ 2 → B = J := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hp := quadratic_actor_normalizes ρ geo hTK hf hK hm eK hAT hA hq hAC hd
  obtain ⟨J,hJA,hJ,hmin⟩ := exists_minimal_bounded_actor ρ A hA
    ((actionRatio_le_nat_iff ρ hA 2).mpr hd)
  have hqJ : IsQuadratic ρ J := fun a ha b hb v => hq a (hJA ha) b (hJA hb) v
  have hn0 : ¬ J ≤ centralizer (K₀ : Set D) := by
    intro hj
    exact hJ.1.1.1 (le_bot_iff.mp ((le_inf hJA hj).trans_eq hAC))
  by_cases hn : J ≤ centralizer (K : Set D)
  · obtain ⟨t,ht,hout⟩ := geo.moved
    have hpair := (geo.pair t ht hout).1
    refine ⟨J.conjBy t,?_,?_,ChapterD.RPlusBound.map_conj ρ hJ t,
      quadratic_conjugate ρ hqJ t,minimal_bound_conjugate ρ J t hmin⟩
    · let N := normalizer (K : Set D)
      let : N.Normal := normal_of_index_eq_two hindex
      rintro _ ⟨j,hj,rfl⟩
      exact (inferInstance : N.Normal).conj_mem j (hp (hJA hj)) t
    · intro hj
      apply hn0
      apply le_centralizer_iff.mpr
      rw [←hpair]
      refine sup_le (le_centralizer_iff.mp hn) ?_
      apply le_centralizer_iff.mp
      intro j hjJ l hl
      obtain ⟨k,hk,rfl⟩ := hl
      have hh := hj (mem_map_of_mem (MulAut.conj t).toMonoidHom hjJ) k hk
      have he := congrArg (MulAut.conj t⁻¹) hh
      simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
        inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using he
  · exact ⟨J,hJA.trans hp,hn,hJ,hqJ,hmin⟩

/-- The full moved central quotient of the exchanged pair has two independent
natural Suzuki factors, with an equivariant group and module identification. -/
theorem exchanged_natural_pair
    (ρ : Representation (ZMod 2) D V) {K K₀ T B C A : Subgroup D}
    (geo : ExchangedGeometry K K₀ T B C)
    (hindex : (normalizer (K : Set D)).index = 2)
    (hTK : T ≤ normalizer (K₀ : Set D))
    (hf : Function.Injective ρ) (hK : IsComponent D K)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hAT : A ≤ T) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hAC : A ⊓ centralizer (K₀ : Set D) = ⊥)
    (hd : fixedCodim ρ A ≤ 2 * rank A) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K₀
      (subspaceCommutator ρ ⊤ K₀) (subspaceCommutator_invariant ρ ⊤ K₀)) (naturalPair m)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨J,hJN,hnJ,hJ,hqJ,hmin⟩ := exists_minimal_actor_on_factor ρ geo hindex hTK hf hK
    hm eK hAT hA hq hAC hd
  obtain ⟨t,ht,hout⟩ := geo.moved
  obtain ⟨hpair,hdis,hcross,_,_⟩ := geo.pair t ht hout
  let K₂ := K.conjBy t⁻¹
  let J₂ := J.conjBy t⁻¹
  let f : K ≃* K₂ := K.equivMapOfInjective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective
  have hJN₂ : J₂ ≤ normalizer (K₂ : Set D) :=
    (map_mono hJN).trans (le_normalizer_map _)
  have hnJ₂ : ¬ J₂ ≤ centralizer (K₂ : Set D) := by
    intro hh
    apply hnJ
    intro j hj k hk
    apply (MulAut.conj t⁻¹).injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      hh (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hj)
        _ (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hk)
  obtain ⟨hI₁,⟨a₁⟩⟩ := minimal_actor_moved_natural ρ K J hK hf hs hm eK hJN hnJ hJ hqJ hmin
  obtain ⟨hI₂,⟨a₂⟩⟩ := minimal_actor_moved_natural ρ K₂ J₂ (hK.map_conj t⁻¹) hf hs hm
    (f.symm.trans eK) hJN₂ hnJ₂ (ChapterD.RPlusBound.map_conj ρ hJ t⁻¹)
    (quadratic_conjugate ρ hqJ t⁻¹) (minimal_bound_conjugate ρ J t⁻¹ hmin)
  let W₁ := subspaceCommutator ρ ⊤ K
  let W₂ := subspaceCommutator ρ ⊤ K₂
  have hs₁ : K₀ ≤ subspaceStabilizer ρ W₁ :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (hpair ▸ sup_le K.le_normalizer ((le_centralizer_iff.mp hcross).trans (Subgroup.centralizer_le_normalizer _)))
  have hs₂ : K₀ ≤ subspaceStabilizer ρ W₂ :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (hpair ▸ sup_le (hcross.trans (Subgroup.centralizer_le_normalizer _)) K₂.le_normalizer)
  have hc₁ : W₁ ≤ fixedSpace ρ K₂ := by
    let : Group.IsPerfect K₂ := (hK.map_conj t⁻¹).2.toIsPerfect
    exact hI₁.le_fixedSpace_of_perfect_centralizes ρ (le_centralizer_iff.mp hcross)
      ((hpair ▸ (le_sup_right : K₂ ≤ K ⊔ K₂)).trans hs₁)
  have hc₂ : W₂ ≤ fixedSpace ρ K := by
    let : Group.IsPerfect K := hK.2.toIsPerfect
    exact hI₂.le_fixedSpace_of_perfect_centralizes ρ hcross
      ((hpair ▸ (le_sup_left : K ≤ K ⊔ K₂)).trans hs₂)
  have hW : subspaceCommutator ρ ⊤ K₀ = W₁ ⊔ W₂ := by
    rw [←hpair]
    simpa only [iSup_bool_eq,Bool.false_eq_true,if_false,if_true] using
      subspaceCommutator_iSup_family ρ (fun b : Bool => if b then K else K₂)
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K K₂ hdis hcross
  let e₀ := e.trans (MulEquiv.subgroupCongr hpair)
  let d : PairQuotient.ProductActors K₀ K K₂ := {
    le₁ := hpair ▸ le_sup_left
    le₂ := hpair ▸ le_sup_right
    equiv := e₀.symm
    inclusion₁ := by
      intro k
      apply e₀.injective
      simpa using (Subtype.ext (by change (e (k,1) : D) = k; simpa using he k 1) : e₀ (k,1) = inclusion (hpair ▸ le_sup_left) k).symm
    inclusion₂ := by
      intro k
      apply e₀.injective
      simpa using (Subtype.ext (by change (e (1,k) : D) = k; simpa using he 1 k) : e₀ (1,k) = inclusion (hpair ▸ le_sup_right) k).symm }
  refine ⟨⟨d.equiv.trans (MulEquiv.prodCongr a₁.groupEquiv a₂.groupEquiv),
    PairQuotient.pairedEquiv ρ d hW hc₁ hc₂ a₁.linearEquiv a₂.linearEquiv,?_⟩⟩
  exact PairQuotient.pairedEquiv_intertwines ρ d hW hc₁ hc₂ a₁.linearEquiv a₂.linearEquiv
    (subspaceCommutator_invariant ρ ⊤ K₀) hs₁ hs₂
    a₁.groupEquiv.toMonoidHom a₂.groupEquiv.toMonoidHom a₁.intertwines a₂.intertwines

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.ExchangedRecognition
