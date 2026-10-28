module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.CubicExclusion
public import Theory.Representation.SL2.PerfectCoreQuotientDegree

/-!
# The remaining odd-degree ordinary-root action rows

The original point local is a perfect extension with quotient SL₂(2ⁿ).
Every faithful binary representation of the secondary action image therefore
has dimension at least 2n. This excludes SL₄(2), SL₅(2), and their action
variants when n is odd. The literal inclusions A_d → A₈ ≃ SL₄(2) exclude
the alternating rows. Order divisibility removes the small symplectic and
triple-cover rows. The marked binary G₂ endpoint would identify its proper
derived subgroup with the full actor, contradicting its checked index two.

The complete source table thus leaves the natural SL₂ row and four larger
action rows, with their original moved-section equivalences. The natural
SL₂ comparison and the completed even-degree contradiction are applied to
the literal root consumer, leaving odd degree with natural or doubled SL₃,
nonbinary Sp₄, or nonbinary G₂. The remaining field and embedded-module
comparisons are still required for the full ordinary-root contradiction.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2 and B.5.1,
pp.86 and 99–103. The binary degree bound uses the actual SL₂
highest-weight and Frobenius-descent theorems through E.2.13(4), p.225.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- A faithful binary representation of the actual secondary image contains
a nontrivial section of the original perfect point local. Its marked SL₂
quotient forces dimension at least twice the original field degree. -/
theorem secondary_faithful_binary_degree (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) (image m KZ) X) (hf : Function.Injective ρ) :
    2 * n ≤ Module.finrank (ZMod 2) X := by
  let d := secondNaturalExtension m hn
  have hF : 2 < Nat.card m.Field := by
    rw [m.card]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  let := d.perfect hF
  let q := secondaryProjection m m.second m.second_le_rootNormalizer
  let f := (inclusion (image_mono m hJK)).comp q
  let σ := ρ.comp f
  have hnt : ∃ j, σ j ≠ 1 := by
    by_contra! ht
    have he : image m m.second = ⊥ := by
      apply bot_unique
      intro x hx
      obtain ⟨j,hj⟩ := secondaryProjection_surjective m m.second m.second_le_rootNormalizer ⟨x,hx⟩
      have hx1 : (inclusion (image_mono m hJK)) (q j) = 1 :=
        hf ((ht j).trans ρ.map_one.symm)
      exact (congrArg Subtype.val hj).symm.trans (congrArg Subtype.val hx1)
    exact second_image_ne_bot m hn hUN hcore he
  let e := QuotientGroup.liftEquiv (pCore 2 m.second) d.surjective d.kernel.symm
  exact SL2.perfect_core_quotient_finrank_bound e σ hnt (by omega) m.card

private theorem binary_embedding_bound (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    {d : ℕ} (f : image m KZ →* SL(d,ZMod 2)) (hf : Function.Injective f) :
    2 * n ≤ d := by
  simpa only [Module.finrank_fin_fun] using secondary_faithful_binary_degree m hn hUN hcore KZ hJK
    ((specialLinearNatural (k := ZMod 2) d).comp f)
    ((specialLinearNatural_injective d).comp hf)

private def altEightEmbedding {d : ℕ} (hd : d ≤ 8) :
    alternatingGroup (Fin d) →* alternatingGroup (Fin 8) :=
  (((Equiv.Perm.extendDomainHom (Fin.castLEEmb hd).toEquivRange).comp
    (alternatingGroup (Fin d)).subtype)).codRestrict _ (by
      intro x
      change Equiv.Perm.sign (x.val.extendDomain _) = 1
      rw [Equiv.Perm.sign_extendDomain]
      exact x.prop)

private theorem altEightEmbedding_injective {d : ℕ} (hd : d ≤ 8) :
    Function.Injective (altEightEmbedding hd) := by
  intro x y h
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective (Fin.castLEEmb hd).toEquivRange (congrArg Subtype.val h)

private theorem no_small_alternating (hn : 1 < n) (ho : Odd n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    {d : ℕ} (hd : d ≤ 8) (e : image m KZ ≃* alternatingGroup (Fin d)) : False := by
  let a := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm
  let f := a.toMonoidHom.comp ((altEightEmbedding hd).comp e.toMonoidHom)
  have hb := binary_embedding_bound m hn hUN hcore KZ hJK f
    (a.injective.comp ((altEightEmbedding_injective hd).comp e.injective))
  have hodd := Nat.odd_iff.mp ho
  omega

omit [Finite G] in
private theorem image_order_dvd (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ) :
    2^n*((2^n)^2-1) ∣ Nat.card (image m KZ) := by
  have hi := card_dvd_of_le (image_mono m hJK)
  rw [Nat.card_congr (secondImageEquiv m hn hr hUN hcore).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,m.card] at hi
  exact hi

omit [Finite G] in
private theorem no_small_order (hn : 1 < n) (ho : Odd n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (hc : Nat.card (image m KZ) ∣ 720 ∨ Nat.card (image m KZ) ∣ 1080) : False := by
  have hd := image_order_dvd m hn hr hUN hcore KZ hJK
  have ho' := Nat.odd_iff.mp ho
  rcases hc with hc | hc
  · have hd := hd.trans hc
    have hb : n < 5 := by
      by_contra! hb
      have hh := (Nat.pow_dvd_pow 2 hb).trans ((dvd_mul_right _ _).trans hd)
      norm_num at hh
    have hn3 : n = 3 := by omega
    norm_num [hn3] at hd
  · have hd := hd.trans hc
    have hb : n < 4 := by
      by_contra! hb
      have hh := (Nat.pow_dvd_pow 2 hb).trans ((dvd_mul_right _ _).trans hd)
      norm_num at hh
    have hn3 : n = 3 := by omega
    norm_num [hn3] at hd

private theorem marked_full_model_eq_top
    {H X E Y : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} {σ : Representation (ZMod 2) E Y}
    {A : Subgroup H} {M : Subgroup E}
    (e : MarkedActionEquiv ρ A ⊤ σ M) : M = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨a,rfl⟩ := e.action.groupEquiv.surjective g
  have he := e.compatible (⟨a,mem_top _⟩ : (⊤ : Subgroup H))
  have hh : (⟨(a : H),e.contained (mem_top _)⟩ : A) = a := rfl
  rw [hh] at he
  exact he.symm ▸ (e.subgroupEquiv (⟨a,mem_top _⟩ : (⊤ : Subgroup H))).property

/-- The larger rows remaining after the finite exceptions are excluded. Every
alternative retains its action equivalence on the original moved section. -/
def OddHigherRows {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) : Prop :=
  (∃ (F : BinaryField), Nonempty
    (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 3))) ∨
  (∃ (F : BinaryField), Nonempty
    (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
      (repeated (linearNatural F 3) 2))) ∨
  (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
    (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binarySymplectic F))) ∨
  (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
    (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binaryG2 F)))

/-- The retained rows expose their literal action comparisons to subsequent consumers. -/
theorem oddHigherRows_iff {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) :
    OddHigherRows ρ s ↔
      (∃ (F : BinaryField), Nonempty
        (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 3))) ∨
      (∃ (F : BinaryField), Nonempty
        (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
          (repeated (linearNatural F 3) 2))) ∨
      (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
        (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binarySymplectic F))) ∨
      (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
        (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binaryG2 F))) := Iff.rfl

/-- The natural rank-one row, or one of the retained larger action rows. -/
def OddRows {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) : Prop :=
  (∃ (F : BinaryField)
      (_e : ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 2)),
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup H),
        A = (S : Subgroup (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype) ∨
  OddHigherRows ρ s

/-- The full B.5.1/B.4.2 table excludes all finite exceptional actors at odd
source degree, using the original embedded point image. -/
theorem oddRows_of_source (hn : 1 < n) (ho : Odd n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (s : letI := hr.elementary
      ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((representation m hr).comp (image m KZ).subtype) ⊤) :
    letI := hr.elementary
    OddRows ((representation m hr).comp (image m KZ).subtype) s.sectionData := by
  let := hr.elementary
  have noLin {d : ℕ} (hd : d = 4 ∨ d = 5)
      (e : (⊤ : Subgroup (image m KZ)) ≃* SL(d,ZMod 2)) : False := by
    have hb := binary_embedding_bound m hn hUN hcore KZ hJK
      (topEquiv.symm.trans e).toMonoidHom (topEquiv.symm.trans e).injective
    have hh := Nat.odd_iff.mp ho
    omega
  have noAlt {d : ℕ} (hd : d ≤ 8)
      (e : (⊤ : Subgroup (image m KZ)) ≃* alternatingGroup (Fin d)) : False :=
    no_small_alternating m hn ho hUN hcore KZ hJK hd (topEquiv.symm.trans e)
  cases s.clause_one with
  | doubleThree F _ e _ _ => exact Or.inr (Or.inr (Or.inl ⟨F,⟨e⟩⟩))
  | naturalDual d hd _ e => exact (noLin hd e.some.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ e => exact (noLin hd e.some.groupEquiv).elim
  | irreducible _ hf _ hs _ =>
    cases hs with
    | linearTwo F _ e ha _ => exact Or.inl ⟨F,e,ha⟩
    | linearThree F _ e _ => exact Or.inr (Or.inl ⟨F,⟨e⟩⟩)
    | symplectic F hF _ e _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨F,hF,⟨e⟩⟩)))
    | g2 F hF _ e _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F,hF,⟨e⟩⟩)))
    | g2Two e _ _ =>
      have he := marked_full_model_eq_top e
      have hi : (commutator (Atlas.G2.Model (ZMod 2))).index = 2 := by
        rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
          Atlas.G2.BinaryException.index_H]
      rw [he,index_top] at hi
      contradiction
    | symmetric d hd e _ _ => exact (noAlt (by omega) e.subgroupEquiv).elim
    | alternatingSix _ e _ _ => exact (noAlt (by decide) e.groupEquiv).elim
    | alternatingSeven _ _ e _ _ _ => exact (noAlt (by decide) e).elim
    | orthogonalSix _ _ e _ _ => exact (noAlt (by decide) e.groupEquiv).elim
    | symmetricEight _ e _ => exact (noAlt (by decide) e.subgroupEquiv).elim
    | binaryLinear d hd _ e _ => exact (noLin hd e.groupEquiv).elim
    | exteriorFive _ _ e _ _ _ => exact (noLin (Or.inr rfl) e).elim
    | symplecticTwo e _ =>
      apply False.elim
      apply no_small_order m hn ho hr hUN hcore KZ hJK
      left
      rw [Nat.card_congr (topEquiv.symm.trans e.subgroupEquiv).toEquiv]
      exact (Subgroup.card_subgroup_dvd_card (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))).trans
        (by rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two])
    | tripleSix _ a _ =>
      apply False.elim
      apply no_small_order m hn ho hr hUN hcore KZ hJK
      right
      rw [← Nat.card_congr (topEquiv : (⊤ : Subgroup (image m KZ)) ≃* image m KZ).toEquiv,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (center (⊤ : Subgroup (image m KZ))),
        Nat.card_congr a.centerEquiv.toEquiv,Nat.card_congr a.quotientEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num

/-- Apply the complete classification to the actual secondary action. The
rank-one row gives equality inside the original actor; the remaining rows
retain their moved-section coordinates for the field comparison. -/
theorem image_eq_or_oddHigherRows (hn : 1 < n) (ho : Odd n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer) (hJK : m.second ≤ KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    letI := hr.elementary
    image m KZ = image m m.second ∨
      ∃ s : MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤,
        OddHigherRows ((representation m hr).comp (image m KZ).subtype) s := by
  let := hr.elementary
  obtain ⟨s⟩ := secondary_source_classification m hn h hr hUN hcore hQ KZ hKN hJK hquasi hnormal
  rcases oddRows_of_source m hn ho hr hUN hcore KZ hJK s with ⟨F,e,ha⟩ | hs
  · exact Or.inl (image_eq_of_linearTwo_section m hn hr hUN hcore hQ KZ hJK s.sectionData F e ha)
  · exact Or.inr ⟨s.sectionData,hs⟩

/-- With the exact core and secondary inputs, every surviving configuration
has odd source degree and one of the four retained larger action rows.
Even degree and the natural SL₂ row are removed by the literal root consumer. -/
theorem remaining_action_rows
    {V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    letI := hr.elementary
    Odd n ∧ ∃ s : MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤,
      OddHigherRows ((representation m hr).comp (image m KZ).subtype) s := by
  let := hr.elementary
  have ho : Odd n := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact false_of_even m D hn he h hr hUN hcore hT hseed hQ KZ hK hcomp hKZ hquasi hnormal
  refine ⟨ho,?_⟩
  rcases image_eq_or_oddHigherRows m hn ho h hr hUN hcore hQ KZ
      (hK.trans (Subgroup.centralizer_le_normalizer _))
      ((le_conjugateSpanBy _ _).trans_eq hKZ) hquasi hnormal with he | hs
  · exact (false_of_image_eq m D hn hr hUN hcore KZ hT hseed hQ hK hKZ hquasi hnormal he).elim
  · exact hs

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
