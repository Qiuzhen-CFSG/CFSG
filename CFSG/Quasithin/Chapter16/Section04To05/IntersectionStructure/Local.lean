module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.SylowTransport
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Comparison
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The intersection structure and symmetry

Apply I.7.7 to K', K, and T_C R. Its factor is precisely T_C, since R
lies in T; this gives the actual factor isomorphism, the relative Sylow
comparison, and R ∩ K = 1. Tight embedding then identifies N_{T_C}(R)
with N_{T_C}(K'). Sylow conjugacy chooses an adapted conjugator.

Restriction through the normal centralizer in N_H(R) proves the final
centralizer Sylow clause. The central involution z belongs to the opposite
normalizer, proving Δ symmetry. Its nontrivial action on the quasisimple
conjugate component gives L' = [L',z]. The noncontainment conclusion
uses the genuine earlier implication 16.3.13(3), kept explicit.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 16.4.2–16.4.3 and the first assertion of 16.4.4(1), pp.1183–1184.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections
open CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

omit [Finite G] in
private theorem conjugate_normalizer (K : Subgroup G) (a : G) :
    (normalizer (K : Set G)).conjBy a = normalizer (K.conjBy a : Set G) := by
  exact map_equiv_normalizer_eq K (MulAut.conj a)

theorem IntersectionSetup.ne_bot (h : IntersectionSetup T z L g R) : R ≠ ⊥ :=
  h.sylow.ne_bot_of_even h.mem_delta.2.2

private theorem IntersectionSetup.product_intersection (h : IntersectionSetup T z L g R) :
    (commutingSylow T L ⊔ R) ⊓ centralizer (L : Set G) = commutingSylow T L := by
  apply le_antisymm
  · exact inf_le_inf_right _ (sup_le inf_le_left h.le_sylow)
  · exact le_inf le_sup_left inf_le_right

private theorem IntersectionSetup.tightNormalizerSetup (h : IntersectionSetup T z L g R) :
    TightNormalizerSetup ((centralizer (L : Set G)).conjBy g) g⁻¹ R
      (commutingSylow T L ⊔ R) := by
  have hc : conjSubgroup ((centralizer (L : Set G)).conjBy g) g⁻¹ =
      centralizer (L : Set G) := (centralizer (L : Set G)).conjBy_inv g
  have hST : commutingSylow T L ⊔ R ≤ (T : Subgroup G) :=
    sup_le inf_le_left h.le_sylow
  refine ⟨tight_map h.tight (MulAut.conj g), ?_, h.sylow.isPGroup, h.ne_bot,
    ?_, ?_, T.isPGroup'.of_injective (inclusion hST) (inclusion_injective _),
    ?_, le_sup_right, ?_⟩
  · intro hn
    have he : conjSubgroup ((centralizer (L : Set G)).conjBy g) g⁻¹ =
        (centralizer (L : Set G)).conjBy g := mem_normalizer_iff_map_conj_eq.mp hn
    exact h.mem_delta.2.1 (hc.symm.trans he).symm
  · simpa only [hc] using h.sylow.le
  · intro Q hp hQ hRQ
    rw [hc] at hQ
    exact (h.sylow.maximal hp hQ hRQ).le
  · rw [hc]
    exact sup_le_sup inf_le_right le_rfl
  · intro Q hp hQ hSQ
    rw [hc] at hQ
    have hcap : Q ⊓ centralizer (L : Set G) = commutingSylow T L :=
      h.toStandardSetup.commutingSylow_sylow.maximal
        (hp.of_injective (inclusion inf_le_left) (inclusion_injective _))
        inf_le_right (le_inf (le_sup_left.trans hSQ) inf_le_right)
    intro x hx
    have hm : x ∈ (centralizer (L : Set G) : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (h.sylow.le.trans inf_le_right)]
      exact hQ hx
    obtain ⟨k, hk, r, hr, rfl⟩ := hm
    have hkQ : k ∈ Q := by
      simpa only [mul_inv_cancel_right] using Q.mul_mem hx
        (Q.inv_mem (hSQ (mem_sup_right hr)))
    exact mul_mem_sup (hcap ▸ (show k ∈ Q ⊓ centralizer (L : Set G) from ⟨hkQ, hk⟩)) hr

/-- The isomorphism, centralizer equality and relative Sylow comparison in
16.4.2(1), obtained from the genuine I.7.7 setup with S = T_C R. -/
theorem IntersectionSetup.normalizer_structure (h : IntersectionSetup T z L g R) :
    commutingSylow T L ⊓ normalizer (R : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G) ∧
    Nonempty (R ≃* ↥(commutingSylow T L ⊓ centralizer (R : Set G))) ∧
    SylowIn (commutingSylow T L ⊓ normalizer (R : Set G))
      (centralizer (L : Set G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G)) ∧
    R ⊓ centralizer (L : Set G) = ⊥ := by
  have hn := h.tightNormalizerSetup
  have hc : conjSubgroup ((centralizer (L : Set G)).conjBy g) g⁻¹ =
      centralizer (L : Set G) := (centralizer (L : Set G)).conjBy_inv g
  have he := hn.normalizer_eq_centralizer
  have hi := hn.factor_equiv
  have hs := hn.factor_sylow
  have hd := hn.disjoint_conjugate.eq_bot
  rw [hc, h.product_intersection] at he hi hs
  rw [hc] at hd
  refine ⟨he, ?_, hs, hd⟩
  obtain ⟨e⟩ := hi
  exact ⟨e.symm.trans (MulEquiv.subgroupCongr he)⟩

/-- The remaining normalizer equality in 16.4.2(1). -/
theorem IntersectionSetup.commuting_normalizer_eq (h : IntersectionSetup T z L g R) :
    commutingSylow T L ⊓ normalizer (R : Set G) =
      commutingSylow T L ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (h.normalizer_le h.ne_bot le_rfl)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rw [h.eq_intersection]
    exact inf_normalizer_le_normalizer_inf
      ⟨hx.2, (T : Subgroup G).le_normalizer hx.1.1⟩

/-- Source 16.4.2(4): correct the conjugator inside N_G(K') using relative
Sylow conjugacy. Left conjugation makes the corrected conjugator a*g. -/
theorem IntersectionSetup.exists_sylow_conjugator (h : IntersectionSetup T z L g R) :
    ∃ a : G, (centralizer (L : Set G)).conjBy a =
      (centralizer (L : Set G)).conjBy g ∧
      (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy a := by
  have hs := h.toStandardSetup.sylowIn_normalizer.map (MulAut.conj g)
  change SylowIn ((T : Subgroup G).conjBy g)
    ((normalizer (centralizer (L : Set G) : Set G)).conjBy g) at hs
  rw [conjugate_normalizer] at hs
  obtain ⟨a, ha, hle⟩ := hs.exists_le_conjugate
    (T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)) inf_le_right
  refine ⟨a * g, ?_, ?_⟩
  · rw [conjBy_mul]
    exact mem_normalizer_iff_map_conj_eq.mp ha
  · simpa only [conjBy_conjBy] using hle

/-- The corrected conjugator retains the entire intersection setup. -/
theorem IntersectionSetup.exists_adapted_setup (h : IntersectionSetup T z L g R) :
    ∃ a : G, IntersectionSetup T z L a R ∧
      (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g ∧
      (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy a : Set G) ≤
        (T : Subgroup G).conjBy a := by
  obtain ⟨a, he, hle⟩ := h.exists_sylow_conjugator
  refine ⟨a, ⟨h.toStandardSetup, he ▸ h.mem_delta, ?_, h.le_sylow⟩, he, ?_⟩
  · rw [he]
    exact h.sylow
  · rwa [he]

theorem StandardSetup.z_mem_commutingSylow (h : StandardSetup T z L) :
    z ∈ commutingSylow T L := by
  refine ⟨h.mem_sylow, ?_⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mp (h.component.1 hx)

/-- The preliminary containment G_z ≤ H on printed p.1183. -/
theorem StandardSetup.centralizer_z_le (h : StandardSetup T z L) :
    involutionCentralizer z ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, h.involution, pow_one])
  have hne : zpowers z ≠ ⊥ := by
    intro he
    have hz : z = 1 := by simpa only [he, mem_bot] using mem_zpowers z
    simpa [hz] using h.involution
  have hn := h.tight.normalizer_le hp hne (zpowers_le.mpr h.z_mem_commutingSylow.2)
  rw [h.normalizers_eq, normalizer_zpowers_eq_centralizer_of_order_two z h.involution] at hn
  exact hn

/-- Source 16.4.2(6). Sylow restriction is relative to N_H(R), and the
containment G_z ≤ H identifies the final ambient centralizer. -/
theorem IntersectionSetup.centralizer_sylow (h : IntersectionSetup T z L g R)
    (hn : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G))) :
    SylowIn ((T : Subgroup G) ⊓ centralizer ((R ⊔ zpowers z : Subgroup G) : Set G))
      (centralizer ((R ⊔ zpowers z : Subgroup G) : Set G)) := by
  let H := normalizer (L : Set G)
  let C := H ⊓ centralizer (R : Set G)
  have hC : C ≤ H ⊓ normalizer (R : Set G) :=
    inf_le_inf_left H (centralizer_le_normalizer _)
  have hnorm : H ⊓ normalizer (R : Set G) ≤ normalizer (C : Set G) :=
    (le_inf (inf_le_left.trans H.le_normalizer)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer R))).trans
        inf_normalizer_le_normalizer_inf
  have hs := hn.inf_normal hC hnorm
  have he : ((T : Subgroup G) ⊓ normalizer (R : Set G)) ⊓ C =
      (T : Subgroup G) ⊓ centralizer (R : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2.2⟩,
      fun hx => ⟨⟨hx.1, centralizer_le_normalizer _ hx.2⟩,
        h.sylow_normalizes hx.1, hx.2⟩⟩
  rw [he] at hs
  have hTC : (T : Subgroup G) ⊓ centralizer (R : Set G) ≤
      centralizer ((R ⊔ zpowers z : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · apply zpowers_le.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes hx.1)
  have hDC : centralizer ((R ⊔ zpowers z : Subgroup G) : Set G) ≤ C := by
    apply le_inf
    · apply le_trans _ h.toStandardSetup.centralizer_z_le
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (hx z (mem_sup_right (mem_zpowers z))).symm
    · exact centralizer_le (show (R : Set G) ⊆ ((R ⊔ zpowers z : Subgroup G) : Set G) from fun _ hx => mem_sup_left hx)
  have hE : (T : Subgroup G) ⊓ centralizer ((R ⊔ zpowers z : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ centralizer (R : Set G) :=
    le_antisymm (inf_le_inf_left _ (hDC.trans inf_le_right)) (le_inf inf_le_left hTC)
  rw [hE]
  apply SylowIn.of_maximal hs.isPGroup hTC
  intro Q hp hQ hRQ
  exact hs.maximal hp (hQ.trans hDC) hRQ

omit [Finite G] in
private theorem conjugate_centralizer (J : Subgroup G) (a : G) :
    (centralizer (J : Set G)).conjBy a = centralizer (J.conjBy a : Set G) :=
  map_centralizer_equiv _ (MulAut.conj a)

/-- The central involution belongs to the opposite relative normalizer. -/
theorem IntersectionSetup.z_normalizes_conjugate (h : IntersectionSetup T z L g R) :
    z ∈ normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
  have hc : z ∈ commutingSylow T L ⊓ centralizer (R : Set G) := by
    refine ⟨h.toStandardSetup.z_mem_commutingSylow, ?_⟩
    intro r hr
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))
  rw [← h.normalizer_structure.1, h.commuting_normalizer_eq] at hc
  exact hc.2

theorem IntersectionSetup.opposite_normalizer_even (h : IntersectionSetup T z L g R) :
    Even (Nat.card ↥(centralizer (L : Set G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G))) := by
  let a : ↥(centralizer (L : Set G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)) :=
    ⟨z, h.toStandardSetup.z_mem_commutingSylow.2, h.z_normalizes_conjugate⟩
  have ha : orderOf a = 2 := (orderOf_coe a).symm.trans h.involution
  exact even_iff_two_dvd.mpr (ha ▸ orderOf_dvd_natCard a)

/-- Source 16.4.3(1): Δ gives a symmetric relation on the conjugates of K. -/
theorem IntersectionSetup.delta_symmetric (h : IntersectionSetup T z L g R) :
    centralizer (L : Set G) ∈ delta (L.conjBy g) := by
  refine ⟨⟨g⁻¹, ?_⟩, ?_, ?_⟩
  · rw [← conjugate_centralizer, conjBy_inv]
  · rw [← conjugate_centralizer]
    exact h.mem_delta.2.1.symm
  · rw [← conjugate_centralizer]
    exact h.opposite_normalizer_even

/-- Source 16.4.2(2), using precisely the earlier 16.3.13(3) implication.
Its evenness premise is supplied by the intersection argument above. -/
theorem IntersectionSetup.component_not_le_conjugate_normalizer
    (h : IntersectionSetup T z L g R)
    (h313 : ∀ a : G, a ∉ normalizer (L : Set G) →
      Even (Nat.card ↥(centralizer (L : Set G) ⊓ normalizer (L.conjBy a : Set G))) →
      ¬ L ≤ normalizer (L.conjBy a : Set G)) :
    ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
  have hN : normalizer (L.conjBy g : Set G) =
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
    rw [← conjugate_normalizer, ← conjugate_normalizer, h.normalizers_eq]
  have hg : g ∉ normalizer (L : Set G) := by
    rw [← h.normalizers_eq]
    exact fun hg => h.mem_delta.2.1 (mem_normalizer_iff_map_conj_eq.mp hg)
  simpa only [hN] using h313 g hg (hN ▸ h.opposite_normalizer_even)

omit [Finite G] in
private theorem quasisimple_eq_commutator {J A : Subgroup G} [IsQuasisimple J]
    (hn : A ≤ normalizer (J : Set G)) (hc : ¬ A ≤ centralizer (J : Set G)) :
    J = ⁅J, A⁆ := by
  let D := ⁅J, A⁆
  have hDJ : D ≤ J := le_normalizer_iff_commutator_le_left.mp hn
  let : (D.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDJ).mpr (normalizer_commutator_ge_left J A)
  rcases IsQuasisimple.normal_le_center_or_eq_top (D.subgroupOf J) with hcen | htop
  · have hbot : ⁅D, J⁆ = ⊥ := by
      have hh : ⁅D.subgroupOf J, (⊤ : Subgroup J)⁆ = ⊥ :=
        commutator_top_right_eq_bot_iff_le_center.mpr hcen
      have hm := congrArg (Subgroup.map J.subtype) hh
      simpa only [map_commutator, map_subgroupOf_eq_of_le hDJ, ← MonoidHom.range_eq_map,
        range_subtype, Subgroup.map_bot] using hm
    have hzero : ⁅A, J⁆ = ⊥ := commutator_eq_bot_of_iterated_eq_bot A J
      (by simpa only [commutator_comm A J] using hbot)
    exact (hc (commutator_eq_bot_iff_le_centralizer.mp hzero)).elim
  · exact le_antisymm (subgroupOf_eq_top.mp htop) hDJ


/-- Source 16.4.3(2): the central involution acts nontrivially on L', and
quasisimplicity makes its commutator the whole component. -/
theorem IntersectionSetup.conjugate_component_eq_commutator
    (h : IntersectionSetup T z L g R) : L.conjBy g = ⁅L.conjBy g, zpowers z⁆ := by
  have hL : IsComponentIn L (involutionCentralizer z) := h.component
  let : IsQuasisimple (L.conjBy g) := (hL.map (MulAut.conj g)).quasisimple
  apply quasisimple_eq_commutator
  · apply zpowers_le.mpr
    have hN : normalizer (L.conjBy g : Set G) =
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
      rw [← conjugate_normalizer, ← conjugate_normalizer, h.normalizers_eq]
    rw [hN]
    exact h.z_normalizes_conjugate
  · intro hcomm
    have hzK' := hcomm (mem_zpowers z)
    rw [← conjugate_centralizer] at hzK'
    have hzR : z ∈ R := by
      rw [h.eq_intersection]
      exact ⟨hzK', h.mem_sylow⟩
    have hz : z = 1 := by
      have hm : z ∈ R ⊓ centralizer (L : Set G) :=
        ⟨hzR, h.toStandardSetup.z_mem_commutingSylow.2⟩
      simpa only [h.normalizer_structure.2.2.2, mem_bot] using hm
    simpa [hz] using h.involution

/-- The centralizer equality and its exact order in 16.4.4(1). The
remaining dihedral/semidihedral and component-center assertions are separate. -/
theorem IntersectionSetup.centralizer_eq_zpowers_of_card_two
    (h : IntersectionSetup T z L g R) (hR : Nat.card R = 2) :
    commutingSylow T L ⊓ centralizer (R : Set G) = zpowers z ∧
      Nat.card ↥(commutingSylow T L ⊓ centralizer (R : Set G)) = 2 := by
  obtain ⟨e⟩ := h.normalizer_structure.2.1
  have hc : Nat.card ↥(commutingSylow T L ⊓ centralizer (R : Set G)) = 2 :=
    (Nat.card_congr e.toEquiv).symm.trans hR
  refine ⟨?_, hc⟩
  apply Eq.symm
  apply eq_of_le_of_card_ge
  · apply zpowers_le.mpr
    refine ⟨h.toStandardSetup.z_mem_commutingSylow, ?_⟩
    intro r hr
    exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))
  · rw [hc, Nat.card_zpowers, h.involution]

/-- Cardinality of a relative Sylow subgroup, retaining the source's
2-part rather than replacing it by the full normalizer order. -/
theorem SylowIn.card_eq_twoPart {P H : Subgroup G} (h : SylowIn P H) :
    Nat.card P = 2 ^ (Nat.card H).factorization 2 := by
  obtain ⟨S, rfl⟩ := h
  rw [card_map_of_injective H.subtype_injective]
  exact S.card_eq_multiplicity

/-- The two relative normalizers have equal 2-parts, as in 16.4.2(1). -/
theorem IntersectionSetup.relative_normalizer_twoPart_eq
    (h : IntersectionSetup T z L g R) :
    2 ^ (Nat.card ↥((centralizer (L : Set G)).conjBy g ⊓
      normalizer (centralizer (L : Set G) : Set G))).factorization 2 =
    2 ^ (Nat.card ↥(centralizer (L : Set G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G))).factorization 2 := by
  rw [← h.sylow.card_eq_twoPart, ← h.normalizer_structure.2.2.1.card_eq_twoPart,
    h.normalizer_structure.1]
  obtain ⟨e⟩ := h.normalizer_structure.2.1
  exact Nat.card_congr e.toEquiv

/-- R acts faithfully on L through the actual conjugation homomorphism. -/
theorem IntersectionSetup.faithful_on_component (h : IntersectionSetup T z L g R) :
    Function.Injective (L.normalizerMonoidHom.comp
      (inclusion (h.le_sylow.trans h.sylow_normalizes))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hc : (r : G) ∈ centralizer (L : Set G) := by
    change inclusion (h.le_sylow.trans h.sylow_normalizes) r ∈
      L.normalizerMonoidHom.ker at hr
    rw [normalizerMonoidHom_ker] at hr
    exact hr
  apply Subtype.ext
  have hm : (r : G) ∈ R ⊓ centralizer (L : Set G) := ⟨r.property, hc⟩
  change (r : G) = 1
  simpa only [h.normalizer_structure.2.2.2, mem_bot] using hm

end CFSG.Quasithin.Chapter16.Intersections
