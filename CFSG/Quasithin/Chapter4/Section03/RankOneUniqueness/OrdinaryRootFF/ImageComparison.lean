module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.PointAction
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Comparing the actual images in the natural SL₂ branch

An offender remains an offender on the literal moved section. The natural
SL₂ row of B.4.2 places a best offender inside the full module image and
identifies it with a Sylow subgroup of the secondary image. Thus this Sylow
lies in the embedded point-local image. Both groups are marked SL₂ groups:
the Sylow orders compare their coefficient fields, and the SL₂ order formula
forces equality of the two actual subgroups. No abstract isomorphism alone
is used to lift containment modulo the root core.

The final consumer applies this equality to the original root contradiction.
This closes the natural SL₂ row; the other B.5.1/B.4.2 rows remain to be
excluded by the ordinary-root classification argument.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2(1), printed p.86.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF

private theorem linearTwo_eq_top_of_contains_sylow
    {H F E : Type*} [Group H] [Finite H]
    [Field F] [Finite F] [CharP F 2] [Field E] [Finite E] [CharP E 2]
    (J : Subgroup H) (eH : H ≃* SL(2,E)) (eJ : J ≃* SL(2,F))
    (P : Sylow 2 H) (hPJ : (P : Subgroup H) ≤ J) : J = ⊤ := by
  have hpc : Nat.card P = Nat.card E := by
    let PE := P.mapSurjective (f := eH.toMonoidHom) eH.surjective
    calc
      Nat.card P = Nat.card PE := Nat.card_congr
        ((P : Subgroup H).equivMapOfInjective eH.toMonoidHom eH.injective).toEquiv
      _ = Nat.card E := Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive E 2 PE).symm.toEquiv
  have hp : IsPGroup 2 ((P : Subgroup H).subgroupOf J) :=
    P.isPGroup'.of_equiv (subgroupOfEquivOfLe hPJ).symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hsc : Nat.card S = Nat.card F := by
    let SF := S.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
    calc
      Nat.card S = Nat.card SF := Nat.card_congr
        ((S : Subgroup J).equivMapOfInjective eJ.toMonoidHom eJ.injective).toEquiv
      _ = Nat.card F := Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 SF).symm.toEquiv
  have hfield : Nat.card E ≤ Nat.card F := by
    rw [← hpc, ← hsc, ← Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv]
    exact Nat.card_le_card_of_injective _ (inclusion_injective hS)
  apply eq_of_le_of_card_ge (le_top : J ≤ ⊤)
  rw [Nat.card_congr topEquiv.toEquiv, Nat.card_congr eH.toEquiv,
    Nat.card_congr eJ.toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    BenderSuzuki.External.huppert614_card_specialLinearGroup]
  gcongr

private theorem exists_section_bestOffender
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    [Module.Finite (ZMod 2) X]
    {ρ : Representation (ZMod 2) H X} {K : Subgroup H}
    (s : ChapterB.QuasisimpleSource.MovedSection ρ K)
    {A : Subgroup H} (hA : IsOffender ρ A) :
    ∃ B ≤ A, IsBestOffender s.action B := by
  apply IsOffender.exists_bestOffender s.action
  refine ⟨hA.1, ?_⟩
  have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  have hs := fixedCodim_subrepresentation_le ρ s.space A
  have ha := hA.2
  change fixedCodim s.action A + _ ≤ _ at hq
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- The natural source row gives equality inside the original quotient actor. -/
theorem image_eq_of_linearTwo_section (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (s : letI := hr.elementary
      ChapterB.QuasisimpleSource.MovedSection
        ((representation m hr).comp (image m KZ).subtype) ⊤)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : letI := hr.elementary
      ChapterB.QuasisimpleSource.ActionEquiv
        (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
        (ChapterB.QuasisimpleSource.linearNatural F 2))
    (hactors : letI := hr.elementary
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup (image m KZ)),
        A = (S : Subgroup (⊤ : Subgroup (image m KZ))).map
          (⊤ : Subgroup (image m KZ)).subtype) :
    image m KZ = image m m.second := by
  let := hr.elementary
  let H := image m KZ
  let J := (image m m.second).subgroupOf H
  have hJH := image_mono m hJK
  have hWH := image_mono m ((m.fullModule_le_second hn).trans hJK)
  let A := (image m c.ordinaryModule).subgroupOf H
  have hA : IsOffender ((representation m hr).comp H.subtype) A :=
    ((fullModule_isBestOffender m hn hr hUN hcore hQ).subgroupOf
      (representation m hr) hWH).isOffender _
  obtain ⟨B,hBA,hB⟩ := exists_section_bestOffender s hA
  obtain ⟨S,hS⟩ := hactors B hB
  let t : (⊤ : Subgroup H) ≃* H := topEquiv
  let P := S.mapSurjective (f := t.toMonoidHom) t.surjective
  have hP : (P : Subgroup H) ≤ J := by
    change (S : Subgroup (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype ≤ J
    rw [← hS]
    exact hBA.trans (fun _ hx => image_mono m (m.fullModule_le_second hn) hx)
  have he := linearTwo_eq_top_of_contains_sylow J
    (topEquiv.symm.trans e.groupEquiv)
    ((subgroupOfEquivOfLe hJH).trans (secondImageEquiv m hn hr hUN hcore)) P hP
  apply le_antisymm ?_ hJH
  intro x hx
  exact (show (⟨x,hx⟩ : H) ∈ J from he.symm ▸ mem_top _)

/-- The natural SL₂ row discharges both literal terminal group premises. -/
theorem module_and_containment_of_linearTwo_section (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (s : letI := hr.elementary
      ChapterB.QuasisimpleSource.MovedSection
        ((representation m hr).comp (image m KZ).subtype) ⊤)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : letI := hr.elementary
      ChapterB.QuasisimpleSource.ActionEquiv
        (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
        (ChapterB.QuasisimpleSource.linearNatural F 2))
    (hactors : letI := hr.elementary
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup (image m KZ)),
        A = (S : Subgroup (⊤ : Subgroup (image m KZ))).map
          (⊤ : Subgroup (image m KZ)).subtype) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore :=
  module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ hKN hKZ hquasi hnormal
    (image_eq_of_linearTwo_section m hn hr hUN hcore hQ KZ
      ((le_conjugateSpanBy _ _).trans_eq hKZ) s F e hactors)

/-- Application to `ordinary_false_of_root_module`, using the original action
and the complete natural-row offender clause. -/
theorem false_of_linearTwo_section
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hcentral : KZ ≤ centralizer (m.root : Set G))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (s : letI := hr.elementary
      ChapterB.QuasisimpleSource.MovedSection
        ((representation m hr).comp (image m KZ).subtype) ⊤)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : letI := hr.elementary
      ChapterB.QuasisimpleSource.ActionEquiv
        (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
        (ChapterB.QuasisimpleSource.linearNatural F 2))
    (hactors : letI := hr.elementary
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup (image m KZ)),
        A = (S : Subgroup (⊤ : Subgroup (image m KZ))).map
          (⊤ : Subgroup (image m KZ)).subtype) : False := by
  obtain ⟨hU,hle⟩ := module_and_containment_of_linearTwo_section m hn hr hUN hcore hseed hQ
    KZ (hcentral.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal s F e hactors
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hKZ hle hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
