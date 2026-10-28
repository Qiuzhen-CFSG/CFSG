module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Fixed
public import CFSG.Quasithin.ChapterB.Section02.RankLifting

/-!
# The two-member maximum elementary family

Uniform fixed subgroups bound the order of every elementary subgroup by
|Q|. Equality outside Q forces the full quotient image, and the actual
unique-lift theorem B.2.21 identifies that subgroup with Qˣ.
The full fixed-space calculations are supplied by the marked natural action.

Source: Aschbacher–Smith C.5.6(5) and C.5.7, printed pp.157,160.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {T : Type*} [Group T] [Finite T]

omit [Finite T] in
private theorem count (Q A : Subgroup T) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup T) (Q ⊓ A) A bot_le inf_le_right

theorem family_pair (Q E : Subgroup T) [Q.Normal]
    [IsElementaryAbelian 2 Q] [IsElementaryAbelian 2 E]
    (hself : centralizer (Q : Set T) = Q)
    (hspan : Q ⊔ E = ⊤) (hne : ¬ E ≤ Q)
    (hfix : ∀ s : T, s ∉ Q → Q ⊓ centralizer ({s} : Set T) = Q ⊓ E)
    (hcard : Nat.card Q = Nat.card E) :
    elementaryAbelianMaxSubgroups (⊤ : Subgroup T) = {Q, E} := by
  have himax (A : Subgroup T) : Q.relIndex A ≤ Q.relIndex E := by
    rw [← relIndex_sup_left E Q, hspan]
    exact relIndex_le_of_le_right le_top (by
      rw [relIndex_top_right]
      exact index_ne_zero_of_finite)
  have hbound (A : Subgroup T) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ Nat.card Q := by
    by_cases hAQ : A ≤ Q
    · exact card_le_of_le hAQ
    · obtain ⟨a, ha, haq⟩ := SetLike.not_le_iff_exists.mp hAQ
      let _ := hA
      have hi : Q ⊓ A ≤ Q ⊓ E := by
        rw [← hfix a haq]
        rintro z ⟨hzq, hza⟩
        exact ⟨hzq, mem_centralizer_iff.mpr (by
          intro y hy
          obtain rfl := Set.mem_singleton_iff.mp hy
          exact setLike_mul_comm ha hza)⟩
      calc
        Nat.card A = Nat.card ↥(Q ⊓ A) * Q.relIndex A := (count Q A).symm
        _ ≤ Nat.card ↥(Q ⊓ E) * Q.relIndex E := Nat.mul_le_mul (card_le_of_le hi) (himax A)
        _ = Nat.card E := count Q E
        _ = Nat.card Q := hcard.symm
  have hQ : Q ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T) :=
    ⟨le_top, inferInstance, fun A _ hA => hbound A hA⟩
  have hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T) :=
    ⟨le_top, inferInstance, fun A _ hA => hcard ▸ hbound A hA⟩
  obtain ⟨e, he, heq⟩ := SetLike.not_le_iff_exists.mp hne
  have hfixE : Q ⊓ centralizer (E : Set T) = Q ⊓ E := by
    apply le_antisymm
    · rw [← hfix e heq]
      exact inf_le_inf_left Q (centralizer_le (Set.singleton_subset_iff.mpr he))
    · exact inf_le_inf_left Q (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  ext A
  constructor
  · intro hA
    by_cases hAQ : A ≤ Q
    · have ha : A = Q := eq_of_le_of_card_ge hAQ (hA.2.2 Q le_top inferInstance)
      simp [ha]
    · obtain ⟨a, ha, haq⟩ := SetLike.not_le_iff_exists.mp hAQ
      let _ : IsElementaryAbelian 2 A := hA.2.1
      have hi : Q ⊓ A ≤ Q ⊓ E := by
        rw [← hfix a haq]
        rintro z ⟨hzq, hza⟩
        exact ⟨hzq, mem_centralizer_iff.mpr (by
          intro y hy
          obtain rfl := Set.mem_singleton_iff.mp hy
          exact setLike_mul_comm ha hza)⟩
      have hidx : Q.relIndex E ≤ Q.relIndex A := by
        have hh : Nat.card ↥(Q ⊓ E) * Q.relIndex E ≤
            Nat.card ↥(Q ⊓ E) * Q.relIndex A := calc
          _ = Nat.card E := count Q E
          _ ≤ Nat.card A := hA.2.2 E le_top inferInstance
          _ = Nat.card ↥(Q ⊓ A) * Q.relIndex A := (count Q A).symm
          _ ≤ _ := Nat.mul_le_mul_right _ (card_le_of_le hi)
        exact Nat.le_of_mul_le_mul_left hh (Nat.card_pos (α := ↥(Q ⊓ E)))
      let q := QuotientGroup.mk' Q
      have himage : E.map q = A.map q := by
        apply eq_of_le_of_card_ge
        · have hae : A.map q = ⊤ := by
            apply eq_of_le_of_card_ge le_top
            have htop : E.map q = ⊤ := by
              have hh := congrArg (fun B : Subgroup T => B.map q) hspan
              simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq,
                map_top_of_surjective q (QuotientGroup.mk'_surjective Q)] using hh
            rw [← htop, ← relIndex_ker, ← relIndex_ker, QuotientGroup.ker_mk']
            exact hidx
          rw [hae]
          exact le_top
        · rw [← relIndex_ker, ← relIndex_ker, QuotientGroup.ker_mk']
          exact himax A
      have haE : A = E := CFSG.Quasithin.ChapterB.lemma_B_2_21 Q E A q
        ((QuotientGroup.ker_mk' Q).trans hself.symm) hself hE hA himage e he
        (hfixE.trans (hfix e heq).symm)
      simp [haE]
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hQ
    · exact Set.mem_singleton_iff.mp ha ▸ hE


universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem card_restrict {B T : Subgroup G} (h : B ≤ T) :
    Nat.card (B.subgroupOf T) = Nat.card B :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

omit [Finite G] in
theorem max_restrict {B T : Subgroup G} (hBT : B ≤ T) :
    B.subgroupOf T ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup T) ↔
      B ∈ elementaryAbelianMaxSubgroups T := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hB
    have he : IsElementaryAbelian 2 B := by
      have hh := hB.2.1.map T.subtype
      rwa [map_subgroupOf_eq_of_le hBT] at hh
    refine ⟨hBT, he, ?_⟩
    intro E hET hE
    let _ := hE
    have hh := hB.2.2 (E.subgroupOf T) le_top (IsElementaryAbelian.subgroupOf hET)
    rwa [card_restrict hET, card_restrict hBT] at hh
  · intro hB
    let _ := hB.2.1
    refine ⟨le_top, IsElementaryAbelian.subgroupOf hBT, ?_⟩
    intro E _ hE
    have hh := hB.2.2 (E.map T.subtype) (map_subtype_le E) (hE.map T.subtype)
    rwa [card_map_of_injective T.subtype_injective, ← card_restrict hBT] at hh

variable {R L : Subgroup G} {x : G} {F : Type*} [Field F]

/-- The exact source maximum elementary family after Φ(D)=1. This applies
to the actual full block module, including every central covering layer. -/
theorem Setup.maximum_family (h : Setup R L F)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hphi : Phi R L = ⊥) :
    elementaryAbelianMaxSubgroups (S R) =
      {Q R L, (Q R L).map (MulAut.conj x⁻¹).toMonoidHom} := by
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  have hQS : Q R L ≤ S R := h.core ▸ inf_le_left
  have hES : Q' ≤ S R := (h.conjugate_core hx).le.trans inf_le_left
  let Q₀ := (Q R L).subgroupOf (S R)
  let E₀ := Q'.subgroupOf (S R)
  let _ := h.core_elementary hx hnc hphi
  let _ : IsElementaryAbelian 2 Q' := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let _ : IsElementaryAbelian 2 Q₀ := IsElementaryAbelian.subgroupOf hQS
  let _ : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hES
  let _ : Q₀.Normal :=
    (normal_subgroupOf_iff_le_normalizer hQS).mpr (S_normalizes_Q R L)
  have hself : centralizer (Q₀ : Set (S R)) = Q₀ := by
    apply le_antisymm
    · intro z hz
      change (z : G) ∈ Q R L
      rw [h.core]
      refine ⟨z.property, mem_centralizer_iff.mpr ?_⟩
      intro v hv
      exact congrArg Subtype.val (mem_centralizer_iff.mp hz
        ⟨v, h.module_le hv⟩ (h.module_le_core hv))
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hspan₀ : Q₀ ⊔ E₀ = ⊤ := by
    rw [← subgroupOf_sup hQS hES, ← h.core_span hx hnc, subgroupOf_self]
  have hne : ¬ E₀ ≤ Q₀ := by
    intro he
    apply hnc
    intro u hu
    have hue : u ∈ Q' := map_mono h.module_le_core hu
    have huq := he (show (⟨u, hES hue⟩ : S R) ∈ E₀ from hue)
    exact (h.core ▸ inf_le_right) huq
  have hfix₀ (s : S R) (hs : s ∉ Q₀) :
      Q₀ ⊓ centralizer ({s} : Set (S R)) = Q₀ ⊓ E₀ := by
    ext z
    have hh := SetLike.ext_iff.mp (h.core_fixed_singleton hx hnc hphi s s.property hs) (z : G)
    simpa only [mem_inf, mem_centralizer_singleton_iff, Q₀, E₀, mem_subgroupOf,
      Subtype.ext_iff, Subgroup.coe_mul] using hh
  have hbalance : Nat.card Q₀ = Nat.card E₀ := by
    rw [card_restrict hQS, card_restrict hES,
      card_map_of_injective (MulAut.conj x⁻¹).injective]
  have hfamily := family_pair Q₀ E₀ hself hspan₀ hne hfix₀ hbalance
  ext B
  constructor
  · intro hB
    have hh := (max_restrict hB.1).mpr hB
    rw [hfamily] at hh
    rcases Set.mem_insert_iff.mp hh with hh | hh
    · have he := congrArg (fun E : Subgroup (S R) => E.map (S R).subtype) hh
      rw [map_subgroupOf_eq_of_le hB.1, map_subgroupOf_eq_of_le hQS] at he
      simp [he]
    · have he := congrArg (fun E : Subgroup (S R) => E.map (S R).subtype)
        (Set.mem_singleton_iff.mp hh)
      rw [map_subgroupOf_eq_of_le hB.1, map_subgroupOf_eq_of_le hES] at he
      simp [he, Q']
  · intro hB
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · apply (max_restrict hQS).mp
      rw [hfamily]
      exact Set.mem_insert _ _
    · obtain rfl := Set.mem_singleton_iff.mp hB
      apply (max_restrict hES).mp
      rw [hfamily]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
