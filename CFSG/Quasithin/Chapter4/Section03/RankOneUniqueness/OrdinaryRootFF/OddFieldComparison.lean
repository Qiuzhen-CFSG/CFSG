module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.OddTableComparison
public import Theory.Representation.SL2.OffenderFieldDegree
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-!
# Completing the odd-degree ordinary-root action comparison

Retain the original W-image inside the embedded J-image, identified with
SL₂(2ⁿ) by its actual action projection. The offender descends to the literal
moved section in each remaining B.5.1/B.4.2 row. The involution displacement
bound and the Sylow order force its fixed codimension to be n. Thus the
model field degree divides n, by restriction of scalars.

Every nonbinary model has a rank-two split torus at some prime dividing
its multiplicative field order. This prime also divides 2ⁿ−1, contradicting
the proved rank-one restriction on the original secondary action image.
The possible binary SL₃ endpoint is excluded by the faithful binary degree
bound for the embedded point local. This handles the natural and doubled
SL₃ rows and the nonbinary symplectic and G₂ rows with their actual actions.
Together with the completed even-degree and rank-one comparisons, this gives
equality of the two subgroups inside the original centralizer quotient.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2 and B.5.1,
pp.86 and 99–103; E.2.13(4), p.225.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open ChapterB.QuasisimpleSource

private theorem binaryField_finrank (F : BinaryField) :
    Module.finrank (ZMod 2) F.Carrier = F.degree := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [Nat.card_zmod,F.card_eq] at h
  exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm

private theorem restrict_injective
    {F H X : Type*} [Field F] [Algebra (ZMod 2) F] [Group H]
    [AddCommGroup X] [Module F X] [Module (ZMod 2) X] [IsScalarTower (ZMod 2) F X]
    (ρ : Representation F H X) (hf : Function.Injective ρ) :
    Function.Injective (restrictScalars (k := ZMod 2) ρ) := by
  intro a b h
  apply hf
  ext x
  exact LinearMap.congr_fun h x

private def removeTop
    {H E X Y : Type*} [Group H] [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} {σ : Representation (ZMod 2) E Y}
    (e : ActionEquiv (ρ.comp (⊤ : Subgroup H).subtype) σ) : ActionEquiv ρ σ :=
  ⟨topEquiv.symm.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (topEquiv.symm g) v⟩

private theorem model_fieldDegree_dvd
    {H E X Y K : Type*} [Group H] [Finite H] [Group E] [Finite E]
    [AddCommGroup X] [Module (ZMod 2) X]
    [Field K] [Finite K] [CharP K 2]
    (F : BinaryField) [AddCommGroup Y] [Module F.Carrier Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) F.Carrier Y]
    [Module.Finite (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} (τ : Representation F.Carrier E Y)
    (hf : Function.Injective τ)
    (J A : Subgroup H) (hAJ : A ≤ J) (eJ : J ≃* SL(2,K))
    {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2^n)
    (hA : IsOffender ρ A)
    (e : ActionEquiv (ρ.comp (⊤ : Subgroup H).subtype) (restrictScalars (k := ZMod 2) τ)) :
    F.degree ∣ n := by
  let a := removeTop e
  let f := a.groupEquiv.toMonoidHom
  let J' := J.map f
  let A' := A.map f
  have hA' := hA.map_equivariant ρ (restrictScalars (k := ZMod 2) τ)
    f a.groupEquiv.injective a.linearEquiv a.intertwines
  let eJ' : J' ≃* SL(2,K) :=
    (J.equivMapOfInjective f a.groupEquiv.injective).symm.trans eJ
  have hd := SL2.scalar_degree_dvd_of_offender τ (restrict_injective τ hf)
    J' A' (map_mono hAJ) eJ' hn hK hA'
  rwa [binaryField_finrank] at hd

private def scalarDouble {F H X : Type*} [Field F] [Group H]
    [AddCommGroup X] [Module F X] (ρ : Representation F H X) :
    Representation F H (Fin 2 → X) where
  toFun g := {
    toFun := fun v i => ρ g (v i)
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun ρ.map_one (v i)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun (ρ.map_mul g h) (v i)

private theorem scalarDouble_injective {F H X : Type*} [Field F] [Group H]
    [AddCommGroup X] [Module F X] (ρ : Representation F H X)
    (hf : Function.Injective ρ) : Function.Injective (scalarDouble ρ) := by
  intro a b he
  apply hf
  ext x
  exact congrFun (LinearMap.congr_fun he (fun _ => x)) 0

private theorem symplectic_faithful (F : BinaryField) :
    Function.Injective (symplecticNatural (k := F.Carrier) 2) := by
  intro a b h
  apply Subtype.ext
  exact Matrix.toLin'.injective h

private theorem g2_split_rank (F : BinaryField) (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card F.Carrier - 1) : 2 ≤ primeRank p (Atlas.G2.Model F.Carrier) := by
  have hu : 1 ≤ primeRank p F.Carrierˣ := by
    by_contra hh
    have hz : primeRank p F.Carrierˣ = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by simpa only [Nat.card_units] using hd)
  have hi := Theory.GroupTheory.primeRank_le_of_injective p
    (Atlas.G2.torusHom (K := F.Carrier)) Atlas.G2.torusHom_injective
  rw [primeRank_prod_eq_add] at hi
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

private theorem linearThree_degree_gt_one (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (F : BinaryField) (e : (⊤ : Subgroup (image m KZ)) ≃* SL(3,F.Carrier)) :
    1 < F.degree := by
  let a := topEquiv.symm.trans e
  let ρ := (linearNatural F 3).comp a.toMonoidHom
  have hf := (restrict_injective (specialLinearNatural (k := F.Carrier) 3)
    (specialLinearNatural_injective 3)).comp a.injective
  have hb := secondary_faithful_binary_degree m hn hUN hcore KZ hJK ρ hf
  have hd : Module.finrank (ZMod 2) (Fin 3 → F.Carrier) = 3 * F.degree := by
    rw [←Module.finrank_mul_finrank (ZMod 2) F.Carrier,
      Module.finrank_fin_fun,binaryField_finrank,mul_comm]
  rw [hd] at hb
  omega

private theorem incompatible_field_degree
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (F : BinaryField) (hF : 1 < F.degree) (hd : F.degree ∣ n)
    {E : Type*} [Group E] [Finite E] (e : (⊤ : Subgroup (image m KZ)) ≃* E)
    (hlower : ∀ p, p.Prime → p ∣ Nat.card F.Carrier - 1 → 2 ≤ primeRank p E) : False := by
  have hpow : 2 < 2^F.degree :=
    Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hF
  obtain ⟨p,hp,hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : 2^F.degree - 1 ≠ 1)
  have hpn : p ∣ 2^n-1 := hpdiv.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hd)
  have hpodd : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    have heven := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : F.degree ≠ 0))
    have hodd := Nat.mod_eq_zero_of_dvd hpdiv
    omega)
  have hb := secondary_image_primeRank_le_one m hn h hr hUN hcore hQ KZ hK hJK
    hcomp hquasi hnormal p hp hpodd hpn
  have hl := hlower p hp (F.card_eq.symm ▸ hpdiv)
  rw [primeRank_congr p (topEquiv.symm.trans e)] at hb
  omega

/-- Exclude all four retained higher rows using the original embedded offender
and the already proved Cartan-prime restriction; no model premise remains. -/
theorem not_oddHigherRows (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (s : letI := hr.elementary
      MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤) :
    letI := hr.elementary
    ¬ OddHigherRows ((representation m hr).comp (image m KZ).subtype) s := by
  let := hr.elementary
  let H := image m KZ
  let J := (image m m.second).subgroupOf H
  let A := (image m c.ordinaryModule).subgroupOf H
  have hJH := image_mono m hJK
  have hWH := image_mono m ((m.fullModule_le_second hn).trans hJK)
  have hAJ : A ≤ J := fun _ hx => image_mono m (m.fullModule_le_second hn) hx
  let eJ : J ≃* SL(2,m.Field) :=
    (subgroupOfEquivOfLe hJH).trans (secondImageEquiv m hn hr hUN hcore)
  have hA : IsOffender ((representation m hr).comp H.subtype) A :=
    (fullModule_isOffender m hn hr hUN hcore hQ).subgroupOf (representation m hr) hWH
  have hAm : IsOffender s.space.toRepresentation A :=
    ⟨hA.1,(fixedCodim_subrepresentation_le _ s.space A).trans hA.2⟩
  have hAs : IsOffender s.action A := by
    refine ⟨hA.1,?_⟩
    have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
    have ha := hAm.2
    change fixedCodim s.action A + _ ≤ _ at hq
    omega
  rw [oddHigherRows_iff]
  rintro (⟨F,⟨e⟩⟩ | ⟨F,⟨e⟩⟩ | ⟨F,hF,⟨e⟩⟩ | ⟨F,hF,⟨e⟩⟩)
  · have hd := model_fieldDegree_dvd F (specialLinearNatural 3)
      (specialLinearNatural_injective 3) J A hAJ eJ hn m.card hAs e
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
      F (linearThree_degree_gt_one m hn hUN hcore KZ hJK F e.groupEquiv) hd e.groupEquiv
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd
  · let τ := scalarDouble (specialLinearNatural (k := F.Carrier) 3)
    have he : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
        (restrictScalars (k := ZMod 2) τ) := e
    have hd := model_fieldDegree_dvd F τ
      (scalarDouble_injective _ (specialLinearNatural_injective 3)) J A hAJ eJ hn m.card hAm he
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
      F (linearThree_degree_gt_one m hn hUN hcore KZ hJK F e.groupEquiv) hd e.groupEquiv
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd
  · have hd := model_fieldDegree_dvd F (symplecticNatural 2)
      (symplectic_faithful F) J A hAJ eJ hn m.card hAs e
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal F hF hd e.groupEquiv
    exact fun p hp hd => Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank hp hd
  · have hd := model_fieldDegree_dvd F (g2Natural F.Carrier)
      (Atlas.G2.Natural.action_injective F.Carrier) J A hAJ eJ hn m.card hAs e
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal F hF hd e.groupEquiv
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact g2_split_rank F p hd

/-- The full source table gives equality of the two subgroups inside the
original centralizer quotient, in every source field degree. -/
theorem secondary_image_eq_second (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    image m KZ = image m m.second := by
  rcases Nat.even_or_odd n with he | ho
  · exact image_eq_of_even m hn he h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
  · let := hr.elementary
    rcases image_eq_or_oddHigherRows m hn ho h hr hUN hcore hQ KZ
      (hK.trans (Subgroup.centralizer_le_normalizer _)) hJK hquasi hnormal with he | ⟨s,hs⟩
    · exact he
    · exact (not_oddHigherRows m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal s hs).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
