module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Transport
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# A radical lift of a nonidentity component involution

The source identities L=[L,J(R)] and R=O₂(LR)O₂(Y_L) force O₂(Y_L) to
act nontrivially on W_L. Indeed O₂(LR) centralizes the span, by its normality
and its containment in C_G(V); if R also centralized the span, the Thompson
commutator identity would make L centralize V. The nontrivial two-group image
of O₂(Y_L) in L/O₂(L) therefore contains an involution. Cauchy's theorem
lifts it to an actual element of L∩R.

Source: Aschbacher–Smith, 15.3.16(2) and the first paragraph of 15.3.23,
printed pp.1126,1128 of the combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)

/-- The normal two-core of LR fixes the span of V, already fixed by R. -/
theorem LR_core_centralizes_span
    (hcore : (L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hR : d.R ≤ centralizer (d.V : Set G)) :
    (L ⊔ d.R).pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G) := by
  apply le_centralizer_iff.mpr
  apply conjugateSpanBy_le (le_centralizer_iff.mp (hcore.trans hR))
  exact ((le_sup_left : L ≤ L ⊔ d.R).trans
    ((L ⊔ d.R).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ d.R) (pCore 2 (L ⊔ d.R : Subgroup G))))).trans
        (normalizer_le_normalizer_centralizer _)

/-- The actual Thompson commutator identity makes J(R) nontrivial on W_L. -/
theorem thompson_not_centralizes_span
    (houtside : ¬ L ≤ d.M) (hC : centralizer (d.V : Set G) ≤ d.M)
    (hJR : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆) :
    ¬ Stellmacher.elementaryAbelianMaxJ d.R ≤ centralizer (d.componentSpan L : Set G) := by
  intro hJ
  have hLC : L ≤ centralizer (d.componentSpan L : Set G) := by
    conv_lhs => rw [hJR]
    exact (commutator_mono le_rfl hJ).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((le_normalizer_conjugateSpanBy d.V L).trans (normalizer_le_normalizer_centralizer _)))
  exact houtside (hLC.trans ((centralizer_le (le_conjugateSpanBy d.V L)).trans hC))

/-- In particular R itself cannot fix W_L. -/
theorem radical_not_centralizes_span
    (houtside : ¬ L ≤ d.M) (hC : centralizer (d.V : Set G) ≤ d.M)
    (hJR : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆) :
    ¬ d.R ≤ centralizer (d.componentSpan L : Set G) := by
  intro hR
  have hJRle : Stellmacher.elementaryAbelianMaxJ d.R ≤ d.R := sSup_le fun A hA => hA.1
  exact thompson_not_centralizes_span d L houtside hC hJR (hJRle.trans hR)

/-- The normal elementary span lies in O₂(LR), hence in R. This uses only
normalization by LR; normalization of L by S is unnecessary. -/
theorem span_le_radical [Finite G] [IsElementaryAbelian 2 (d.componentSpan L)]
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
    (hcore : (L ⊔ d.R).pCoreIn 2 ≤ d.R) : d.componentSpan L ≤ d.R := by
  apply le_trans ?_ hcore
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (d.componentSpan L))
  · exact conjugateSpanBy_le ((V_le_R d hR).trans le_sup_right)
      (le_sup_left.trans (L ⊔ d.R).le_normalizer)
  · exact (le_sup_left : L ⊔ d.R ≤ overgroup d L).trans hN

/-- A nontrivial two-subgroup image in the genuine core quotient contains
an involution which lifts inside the prescribed ambient subgroup. -/
theorem involution_lift [Finite G] (A : Subgroup G) (hAL : A ≤ L)
    (hA : IsPGroup 2 A) (hne : ¬ A ≤ L.pCoreIn 2)
    {T : Type*} [Group T] (e : (L ⧸ pCore 2 L) ≃* T) :
    ∃ l : L, (l : G) ∈ A ∧ e (QuotientGroup.mk l) ^ 2 = 1 ∧
      e (QuotientGroup.mk l) ≠ 1 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let B := (A.subgroupOf L).map f
  have hB : IsPGroup 2 B := (hA.comap_of_injective L.subtype L.subtype_injective).map f
  have hBne : B ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff (A.subgroupOf L)).mp hb
    apply hne
    intro a ha
    have hf : f ⟨a,hAL ha⟩ = 1 := hk ha
    have he : QuotientGroup.mk' (pCore 2 L) ⟨a,hAL ha⟩ = 1 :=
      e.injective (hf.trans e.map_one.symm)
    exact mem_map.mpr ⟨⟨a,hAL ha⟩, (QuotientGroup.eq_one_iff _).mp he, rfl⟩
  let _ : Nontrivial B := (nontrivial_iff_ne_bot _).mpr hBne
  let _ : Finite B := Finite.of_surjective
    (f.subgroupMap (A.subgroupOf L)) (by
      rintro ⟨b,a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩)
  obtain ⟨b,hb⟩ := exists_ne (1 : B)
  have hd : 2 ∣ Nat.card B := (hB.dvd_orderOf hb).trans (orderOf_dvd_natCard b)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 hd
  obtain ⟨l,hl,he⟩ := t.property
  refine ⟨l,hl,?_,?_⟩
  · have hh : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    have hh' := congrArg Subtype.val hh
    change (t : T) ^ 2 = 1 at hh'
    change f l ^ 2 = 1
    rwa [he]
  · intro hh
    have ht1 : t = 1 := Subtype.ext (he.symm.trans hh)
    rw [ht1, orderOf_one] at ht
    omega

/-- The source residual factorization and Thompson identity construct the
radical involution, without any S-normalization or chief-case exclusion. -/
theorem radical_involution [Finite G]
    (houtside : ¬ L ≤ d.M) (hC : centralizer (d.V : Set G) ≤ d.M)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hJR : L = ⁅L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hfactor : d.R = (L ⊔ d.R).pCoreIn 2 ⊔ (YL d L).pCoreIn 2)
    {T : Type*} [Group T] (e : (L ⧸ pCore 2 L) ≃* T) :
    ∃ l : L, (l : G) ∈ d.R ∧ e (QuotientGroup.mk l) ^ 2 = 1 ∧
      e (QuotientGroup.mk l) ≠ 1 := by
  have hCR : (L ⊔ d.R).pCoreIn 2 ≤ d.R := le_sup_left.trans hfactor.ge
  have hAR : (YL d L).pCoreIn 2 ≤ d.R := le_sup_right.trans hfactor.ge
  have hAL : (YL d L).pCoreIn 2 ≤ L := ((YL d L).pCoreIn_le 2).trans
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right)
  have hn : ¬ (YL d L).pCoreIn 2 ≤ L.pCoreIn 2 := by
    intro h
    apply radical_not_centralizes_span d L houtside hC hJR
    rw [hfactor]
    exact sup_le (LR_core_centralizes_span d L hCR (hR.le.trans inf_le_right))
      (h.trans (core_centralizes_span d L hcore (hR.le.trans inf_le_right)))
  obtain ⟨l,hl,ht,hn⟩ := involution_lift L ((YL d L).pCoreIn 2) hAL
    ((YL d L).isPGroup_pCoreIn 2) hn e
  exact ⟨l,hAR hl,ht,hn⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
