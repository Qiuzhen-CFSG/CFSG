module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.QuotientProduct
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.ElementaryLift

/-!
# The actual four-member family in the two-block natural case

The source no-common-normal condition kills Φ(D), so D is elementary and
central in S. Each of the four quotient choices has elementary full preimage
U₁U₂D, U₁U₂ˣD, U₁ˣU₂D, or U₁ˣU₂ˣD. The kernel/image order argument proves
that these are exactly A(S), retaining every central covering layer.

Source: Aschbacher–Smith, C.5.6(7), printed pp.158–159.
-/
public section
open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
variable {R K L : Subgroup G} {𝔽 𝔽' : Type*} [Field 𝔽] [Field 𝔽']

theorem Setup.two_block_family
    (h : Setup R K 𝔽) (h' : Setup R L 𝔽') (hKL : L ≤ centralizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (A : Subgroup G) :
    let V₁ := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    let V₂ := (U L).map (MulAut.conj x⁻¹).toMonoidHom
    let D := S R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    A ∈ elementaryAbelianMaxSubgroups (S R) ↔
      ∃ a ∈ ({U K,V₁} : Set (Subgroup G)), ∃ b ∈ ({U L,V₂} : Set (Subgroup G)),
        A = (a ⊔ b) ⊔ D := by
  let V₁ := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let D := S R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let Q := S R ⊓ centralizer (U K ⊔ U L : Subgroup G)
  have hxR := hMR hx
  have hp := h.two_block_source_product h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hq : Q = (U K ⊔ U L) ⊔ D := hp.1
  let : IsElementaryAbelian 2 Q := hp.2.2.2.2.2
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ Q from hq ▸ le_sup_right)
  have hDS : D ≤ S R := inf_le_left
  have hDC : D ≤ centralizer (S R : Set G) := by
    have hs : S R = ((U K ⊔ U L) ⊔ (U K ⊔ U L).map (MulAut.conj x⁻¹).toMonoidHom) ⊔ D := hp.2.2.1
    rw [hs]
    apply le_centralizer_iff.mpr
    refine sup_le (sup_le ?_ (le_centralizer_iff.mp hp.2.1)) (le_centralizer D)
    exact le_centralizer_iff.mp ((show D ≤ Q from hq ▸ le_sup_right).trans inf_le_right)
  let : (D.subgroupOf (S R)).Normal := normal_subgroupOf_of_le_normalizer
    ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _))
  let f := QuotientGroup.mk' (D.subgroupOf (S R))
  have hf := QuotientGroup.mk'_surjective (D.subgroupOf (S R))
  have hk : f.ker = D.subgroupOf (S R) := QuotientGroup.ker_mk' _
  let m := baumannImage R f
  have hquot := h.two_block_quotient_family h' hKL M T_H x hx hxR hindex hpair ht hnc f hf hk
  have hc : factor K x ≤ centralizer (factor L x : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (h.four_module_geometry hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc).2.2.2
  let : IsElementaryAbelian 2 (U K) := h.elementary
  let : IsElementaryAbelian 2 (U L) := h'.elementary
  let : IsElementaryAbelian 2 V₁ := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 V₂ := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hleft (a : Subgroup G) (ha : a ∈ ({U K,V₁} : Set (Subgroup G))) :
      a ≤ S R ∧ a ≤ factor K x ∧ IsElementaryAbelian 2 a := by
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨h.module_le,le_sup_left,inferInstance⟩
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact ⟨h.conjugate_le hxR,le_sup_right,inferInstance⟩
  have hright (b : Subgroup G) (hb : b ∈ ({U L,V₂} : Set (Subgroup G))) :
      b ≤ S R ∧ b ≤ factor L x ∧ IsElementaryAbelian 2 b := by
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact ⟨h'.module_le,le_sup_left,inferInstance⟩
    · obtain rfl := Set.mem_singleton_iff.mp hb
      exact ⟨h'.conjugate_le hxR,le_sup_right,inferInstance⟩
  have hpre (a : Subgroup G) (ha : a ∈ ({U K,V₁} : Set (Subgroup G)))
      (b : Subgroup G) (hb : b ∈ ({U L,V₂} : Set (Subgroup G))) :
      (m a ⊔ m b).comap f = ((a ⊔ b) ⊔ D).subgroupOf (S R) ∧
      IsElementaryAbelian 2 ↥((a ⊔ b) ⊔ D) := by
    obtain ⟨haS,haF,haE⟩ := hleft a ha
    obtain ⟨hbS,hbF,hbE⟩ := hright b hb
    constructor
    · change ((a.subgroupOf (S R)).map f ⊔ (b.subgroupOf (S R)).map f).comap f = _
      rw [← Subgroup.map_sup,comap_map_eq,hk,← subgroupOf_sup haS hbS,
        ← subgroupOf_sup (sup_le haS hbS) hDS]
    · let := haE
      let := hbE
      let : IsElementaryAbelian 2 ↥(a ⊔ b) := IsElementaryAbelian.sup_of_le_centralizer
        ((hbF.trans (le_centralizer_iff.mp hc)).trans (centralizer_le haF))
      exact IsElementaryAbelian.sup_of_le_centralizer (hDC.trans (centralizer_le (sup_le haS hbS)))
  have hmember (B : Subgroup (S R ⧸ D.subgroupOf (S R))) :
      B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (S R ⧸ D.subgroupOf (S R))) ↔
        ∃ a ∈ ({U K,V₁} : Set (Subgroup G)), ∃ b ∈ ({U L,V₂} : Set (Subgroup G)), B = m a ⊔ m b := by
    rw [hquot]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,exists_eq_or_imp,exists_eq_left,or_assoc]
    rfl
  have hlift (B : Subgroup (S R ⧸ D.subgroupOf (S R)))
      (hB : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (S R ⧸ D.subgroupOf (S R)))) :
      IsElementaryAbelian 2 (B.comap f) := by
    obtain ⟨a,ha,b,hb,rfl⟩ := (hmember B).mp hB
    rw [(hpre a ha b hb).1]
    let := (hpre a ha b hb).2
    exact IsElementaryAbelian.subgroupOf (sup_le (sup_le (hleft a ha).1 (hright b hb).1) hDS)
  constructor
  · intro hA
    obtain ⟨B,hB,he⟩ := (max_family_comap_iff f hf hlift (A.subgroupOf (S R))).mp
      ((max_restrict hA.1).mpr hA)
    obtain ⟨a,ha,b,hb,rfl⟩ := (hmember B).mp hB
    refine ⟨a,ha,b,hb,?_⟩
    rw [(hpre a ha b hb).1] at he
    have hh := congrArg (map (S R).subtype) he
    rwa [map_subgroupOf_eq_of_le hA.1,map_subgroupOf_eq_of_le
      (sup_le (sup_le (hleft a ha).1 (hright b hb).1) hDS)] at hh
  · rintro ⟨a,ha,b,hb,rfl⟩
    apply (max_restrict (sup_le (sup_le (hleft a ha).1 (hright b hb).1) hDS)).mp
    apply (max_family_comap_iff f hf hlift _).mpr
    exact ⟨m a ⊔ m b,(hmember _).mpr ⟨a,ha,b,hb,rfl⟩,(hpre a ha b hb).1.symm⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
