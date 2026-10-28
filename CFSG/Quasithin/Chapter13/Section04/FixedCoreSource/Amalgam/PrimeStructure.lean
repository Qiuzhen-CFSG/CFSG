module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PrimeQuotient
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SourceComponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Complete

/-!
# The nonsolvable quotient has the original component as its whole residual

F.6.16 makes the two-residual a three-group when the three-core is
noncyclic. This is impossible for our nonsolvable quotient. In the
cyclic-three-core branch, F.6.10 either places both local residuals in
the selected component, or gives a component containing exactly one.

In the latter case, the proved F.6.13 and component sieve give a prime
PSL₂(p) model, and the literal four-group/cubic normalizer calculation
forces p=11 or 13 modulo 24. None of the five actual 13.3.2 quotient
orders can be its order. Thus both local residuals lie in the same
component, which is O²(X/O₃′(X)) and F*(X/O₃′(X)).

The same chosen component and original quotient maps are retained. No
universal F.6.18 classification or marked-triple recognition premise is
used. Earlier Source1332OneTwo remains explicit. Generation lifts this
conclusion to the actual join.
Source: Aschbacher–Smith 13.4.7, p.900; F.6.10,13,16–18, pp.306–310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V A B : Subgroup G}

private theorem local_cover_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple H := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R,hH,isPGroup_pCoreIn 2 H,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩

/-- The actual quotient reaches the cyclic-three-core component alternatives,
with the same selected component retained in every branch. -/
theorem original_pair_prime_component_reduction
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let q := QuotientGroup.mk' (pPrimeCore 3 X)
    let Ap := (A.subgroupOf X).map q
    let Bp := (B.subgroupOf X).map q
    let Kp := K.map q
    IsCyclic (pCore 3 (X ⧸ pPrimeCore 3 X)) ∧
      ((pResidual 2 (X ⧸ pPrimeCore 3 X) = Kp ∧
          generalizedFitting (X ⧸ pPrimeCore 3 X) = Kp) ∨
        (∃ d : SingleResidualComponent Ap Bp, d.component = Kp) ∨
        (∃ d : SingleResidualComponent Bp Ap, d.component = Kp)) := by
  let X := A ⊔ B
  let Q := X ⧸ pPrimeCore 3 X
  let q := QuotientGroup.mk' (pPrimeCore 3 X)
  let Ap := (A.subgroupOf X).map q
  let Bp := (B.subgroupOf X).map q
  let Kp := K.map q
  obtain ⟨hns,_,hg,hc,hn,horient⟩ := original_pair_prime_component_supplement
    h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB K hK
  let : Kp.Normal := hn
  let : IsQuasisimple Kp := hc.2
  have hs := local_cover_sqtk h₀.qtke
    (original_pair_local D m hTA hTB eA eB hne hindexA hindexB).1
  have hcyclic : IsCyclic (pCore 3 Q) := by
    by_contra hncyclic
    have hr := residual_isThreeGroup_of_cover hs (MulEquiv.refl Q) hg hncyclic
    let : Group.IsNilpotent (pResidual 2 Q) := hr.isNilpotent
    let : Group.IsNilpotent (Q ⧸ pResidual 2 Q) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact hns ((Group.isSolvable_iff_subgroup_quotient (pResidual 2 Q)).mpr
      ⟨inferInstance,inferInstance⟩)
  refine ⟨hcyclic,?_⟩
  have both (hA : (pResidual 2 Ap).map Ap.subtype ≤ Kp)
      (hB : (pResidual 2 Bp).map Bp.subtype ≤ Kp) :
      pResidual 2 Q = Kp ∧ generalizedFitting Q = Kp := by
    obtain ⟨hr,hf,_⟩ := quasisimple_residual_of_both_local_containments hg
      (pPrimeCore_quotient_pPrimeCore_eq_bot 3) Kp hA hB
    exact ⟨hr,hf⟩
  rcases horient with ⟨hA,hgen⟩ | ⟨hB,hgen⟩
  · by_cases hB : (pResidual 2 Bp).map Bp.subtype ≤ Kp
    · exact Or.inl (both hA hB)
    · obtain ⟨_,hj,hS⟩ := normal_subgroup_rigidity_setup hg Kp hA hB
      exact Or.inr (Or.inl ⟨⟨Kp,hc,hn,hA,hB,hgen,hj,hS⟩,rfl⟩)
  · by_cases hA : (pResidual 2 Ap).map Ap.subtype ≤ Kp
    · exact Or.inl (both hA hB)
    · obtain ⟨_,hj,hS⟩ := normal_subgroup_rigidity_setup hg.symm Kp hB hA
      exact Or.inr (Or.inr ⟨⟨Kp,hc,hn,hB,hA,hgen,hj,hS⟩,rfl⟩)



private theorem small_order_not_prime_row {n p : ℕ}
    (hn : n = 60 ∨ n = 168 ∨ n = 360 ∨ n = 1080 ∨ n = 6048)
    (hp : p % 24 = 11 ∨ p % 24 = 13)
    (hc : n * 2 = p * (p ^ 2 - 1)) : False := by
  have hnle : n ≤ 6048 := by rcases hn with h | h | h | h | h <;> omega
  have hp24 : p < 24 := by
    by_contra hh
    have h24 : 24 ≤ p := by omega
    have hsq : 576 ≤ p ^ 2 := by nlinarith
    have hs : 575 ≤ p ^ 2 - 1 := by omega
    have hb := Nat.mul_le_mul h24 hs
    omega
  rw [Nat.mod_eq_of_lt hp24] at hp
  rcases hp with hp | hp <;> rcases hn with hn | hn | hn | hn | hn <;>
    norm_num [hp,hn] at hc

universe v
private theorem single_residual_not_midSize_order
    {H Q : Type v} [Group H] [Finite H] [Group Q] [Finite Q]
    {A B : Subgroup Q} (hs : IsSQTK KnownSimple.IsKnownSimple H)
    (e : Q ≃* (H ⧸ pPrimeCore 3 H)) (hg : ChapterF.IsGoldschmidtTriple A B)
    (d : SingleResidualComponent A B)
    (hcards : Nat.card d.component = 60 ∨ Nat.card d.component = 168 ∨
      Nat.card d.component = 360 ∨ Nat.card d.component = 1080 ∨ Nat.card d.component = 6048) :
    False := by
  have hz : pCore 2 Q = ⊥ := le_bot_iff.mp (ChapterF.twoCore_le_primeToThreeCore.trans
    (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient e).le)
  obtain ⟨p,hp,ho,h8,hm⟩ := d.prime_psl2_of_either_exceptional
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
    hs e hg hz (Or.inl (d.left_not_characteristic_two hg hz))
  let : Fact p.Prime := ⟨hp⟩
  let : d.component.Normal := d.normal
  have hthree := left_residual_card_three_of_normal_subgroup hg hz d.component
    d.left_contains d.right_escapes
  have h24 := d.source_prime_congruence e hg ho h8 hm hthree
  obtain ⟨_,_,⟨ep⟩⟩ := prime_psl_component_center_and_outer e d.isComponent ho hm
  have hc : Nat.card d.component * 2 = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr ep.toEquiv]
    simpa using Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := ZMod p) (by simpa using ho)
  exact small_order_not_prime_row hcards h24 hc

/-- The original component is the entire two-residual and generalized Fitting
subgroup of the literal prime-to-three quotient. -/
theorem original_pair_prime_component_is_residual
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let q := QuotientGroup.mk' (pPrimeCore 3 X)
    pResidual 2 (X ⧸ pPrimeCore 3 X) = K.map q ∧
      generalizedFitting (X ⧸ pPrimeCore 3 X) = K.map q := by
  let X := A ⊔ B
  let Q := X ⧸ pPrimeCore 3 X
  let q := QuotientGroup.mk' (pPrimeCore 3 X)
  let C := K.map X.subtype
  obtain ⟨_,hf,_,_,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨_,_,_,⟨eq,heq⟩⟩ := original_pair_component_prime_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 C) j (pCore_map_iso 2 j)
  have hcard : Nat.card (K.map q) = Nat.card (C ⧸ pCore 2 C) :=
    Nat.card_congr (eq.symm.trans jq).toEquiv
  have hcards := (h1332 _ hf).2.card
  have hs := local_cover_sqtk h₀.qtke
    (original_pair_local D m hTA hTB eA eB hne hindexA hindexB).1
  obtain ⟨_,_,hg,_,_,_⟩ := original_pair_prime_component_supplement h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  obtain ⟨_,hcases⟩ := original_pair_prime_component_reduction h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  rcases hcases with h | ⟨d,hd⟩ | ⟨d,hd⟩
  · exact h
  · apply False.elim
    apply single_residual_not_midSize_order hs (MulEquiv.refl Q) hg d
    rw [hd,hcard]
    exact hcards
  · apply False.elim
    apply single_residual_not_midSize_order hs (MulEquiv.refl Q) hg.symm d
    rw [hd,hcard]
    exact hcards



end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
