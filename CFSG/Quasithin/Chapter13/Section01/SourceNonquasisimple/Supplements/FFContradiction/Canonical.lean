module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Action
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Intersection
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The marked canonical factor and the actual direct product

The map from L_R into Ĥ has kernel exactly O₂(L_R): the two-core
centralizes D, while a proper kernel in the local C-component lies in
its solvable radical. The completed radical-intersection theorem
identifies that radical with the two-core. This constructs the actual
PSL₂(p) image and records its value on every original representative.

The two commuting factor images have trivial intersection because
PSL₂(p) has trivial center. Multiplication therefore identifies their
external product with Ĥ, with the original embeddings retained.

This is the common-action stage of the FF contradiction, not the later
L₃(2) tensor identification. The controlled Thompson index and all
chief-section and generation steps remain with qt-d-1319-ff-contradiction;
qt-d-1317-supplements owns final discharge of the earlier source inputs.
Source: Aschbacher--Smith 13.1.9, printed p.870.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

@[expose] def canonicalHatHom (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] :
    canonicalSupplement T L →*
      hatImage T L Y j (canonicalSupplement T L) :=
  ((hatMap T L Y j).subgroupMap _).comp
    (subgroupOfEquivOfLe (show canonicalSupplement T L ≤ commonGroup T L Y j from le_sup_left)).symm.toMonoidHom

theorem canonicalHatHom_surjective (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] : Function.Surjective (canonicalHatHom T L Y j) :=
  ((hatMap T L Y j).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (show canonicalSupplement T L ≤ commonGroup T L Y j from le_sup_left)).symm.surjective

theorem canonicalHatHom_ker (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    (canonicalHatHom T L Y j).ker = pCore 2 (canonicalSupplement T L) := by
  let A := canonicalSupplement (T : Subgroup G) L
  let E := commonGroup (T : Subgroup G) L Y j
  let f := canonicalHatHom (T : Subgroup G) L Y j
  have hcan := canonical_frattini_geometry h hmany hL hn
  have hDC := canonical_core_centralizes_omegaClosure w hTH hAH hTL hcan.2.1 j
  have hDE : omegaClosure T L Y j ≤ E :=
    (omegaClosure_geometry w hTH hAH hTL j).2.1.trans le_sup_right
  have hproper : f.ker ≠ ⊤ := by
    intro he
    apply omegaClosure_moved_by_canonical h hmany hL hn w hTH hAH hTL j
    apply (hat_image_eq_bot_iff (T : Subgroup G) L Y A j hDE le_sup_left).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,ha⟩ := canonicalHatHom_surjective (T : Subgroup G) L Y j ⟨x,hx⟩
    have hz : f a = 1 := he.ge (mem_top a)
    have hg := congrArg Subtype.val (ha.symm.trans hz)
    exact mem_bot.mpr hg
  have ht : (⊤ : Subgroup A).IsCComponent := by
    simpa only [subgroupOf_self] using hcan.1.1.1.subgroupOf_of_le le_rfl le_sup_left
  apply le_antisymm
  · exact (kernel_le_solvableRadical_of_top_isCComponent ht f hproper).trans_eq
      (canonical_radical_eq_twoCore h hmany hL hn)
  · intro a ha
    apply Subtype.ext
    change hatMap T L Y j (⟨a,(show A ≤ E from le_sup_left) a.property⟩ : E) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    intro d hd
    exact Subtype.ext (hDC (mem_map_of_mem A.subtype ha) d hd)

private noncomputable def canonicalHatEquivOfKernel (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hk : (canonicalHatHom T L Y j).ker = pCore 2 (canonicalSupplement T L)) :
    XiQuotient (canonicalSupplement T L) ≃* hatImage T L Y j (canonicalSupplement T L) :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (canonicalHatHom T L Y j)
      (canonicalHatHom_surjective T L Y j))

def canonicalHatEquiv (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    XiQuotient (canonicalSupplement T L) ≃*
      hatImage T L Y j (canonicalSupplement T L) :=
  canonicalHatEquivOfKernel (T : Subgroup G) L Y j
    (canonicalHatHom_ker h hmany hL hn w hTH hAH hTL j)

/-- The isomorphism agrees with the original homomorphism on every representative. -/
@[expose] def CanonicalHatMarking (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (e : XiQuotient (canonicalSupplement T L) ≃*
      hatImage T L Y j (canonicalSupplement T L)) : Prop :=
  ∀ a : canonicalSupplement T L,
    e (QuotientGroup.mk' (pCore 2 (canonicalSupplement T L)) a) = canonicalHatHom T L Y j a

theorem canonicalHatEquiv_apply (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    CanonicalHatMarking (T : Subgroup G) L Y j
      (canonicalHatEquiv h hmany hL hn w hTH hAH hTL j) := by
  intro a
  rfl

theorem canonical_hat_model (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL
      (hatImage T L Y j (canonicalSupplement T L)) 2 p := by
  obtain ⟨p,hp,hp3,he⟩ := canonical_twoCore_quotient h hmany hL hn
  exact ⟨p,hp,hp3,he.of_mulEquiv (canonicalHatEquiv h hmany hL hn w hTH hAH hTL j).symm⟩

private theorem pslTwo_center {Q : Type*} [Group Q] {p : ℕ}
    (hq : ClassicalGroup.IsPSL Q 2 p) : center Q = ⊥ := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := hq
  let := hF
  let := hfin
  apply le_bot_iff.mp
  intro a ha
  have hz : e a ∈ center (GorensteinWalter.PSL2 F) :=
    (Subgroup.centerCongr e ⟨a,ha⟩).property
  rw [GorensteinWalter.psl2_center_eq_bot F] at hz
  exact mem_bot.mpr (e.injective ((mem_bot.mp hz).trans (map_one e).symm))

private theorem disjoint_of_centerless_commuting {Q : Type*} [Group Q]
    (A B : Subgroup Q) (hz : center A = ⊥) (hc : ⁅A,B⁆ = ⊥) : Disjoint A B := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hz' : (⟨x,hx.1⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext ((le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc)) hx.2 a a.property)
  rw [hz] at hz'
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hz'))

/-- The two commuting images form the actual internal direct product Ĥ.
The first factor is identified by its literal quotient map, so its trivial
center supplies disjointness, without a separate product hypothesis. -/
theorem hat_direct_product (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hAC : canonicalSupplement T L ≤ C)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    let E := commonGroup (T : Subgroup G) L Y j
    let q := hatMap (T : Subgroup G) L Y j
    let A := ((canonicalSupplement T L).subgroupOf E).map q
    let B := ((thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).subgroupOf E).map q
    ∃ e : A × B ≃* HatGroup T L Y j,
      ∀ a b, e (a,b) = (a : HatGroup T L Y j) * (b : HatGroup T L Y j) := by
  dsimp only
  let E := commonGroup (T : Subgroup G) L Y j
  let q := hatMap (T : Subgroup G) L Y j
  let A := ((canonicalSupplement T L).subgroupOf E).map q
  let B := ((thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).subgroupOf E).map q
  obtain ⟨p,_,_,hp⟩ := canonical_hat_model h hmany hL hn w hTH hAH hTL j
  have hc := hat_images_commute h w hH hTH hAH hAC hTL
    (canonical_frattini_geometry h hmany hL hn).2.1 j
  have hd := disjoint_of_centerless_commuting A B (pslTwo_center hp) hc
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  let e' := (e.trans (MulEquiv.subgroupCongr (hat_images_generate (T : Subgroup G) L Y j))).trans
    (Subgroup.topEquiv : (⊤ : Subgroup (HatGroup T L Y j)) ≃* HatGroup T L Y j)
  exact ⟨e',he⟩


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
