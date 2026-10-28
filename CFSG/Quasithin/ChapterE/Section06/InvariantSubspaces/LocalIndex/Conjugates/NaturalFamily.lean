module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section02.RankLifting

/-!
# The natural two-member family from full fixed-space calculations

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
C.5.6(5), printed p.157, and C.5.7, printed p.160.

The fixed-space identity first identifies `E = UˣD` with `Qˣ`, giving
equal orders. For an elementary subgroup meeting the complement of `Q`, count its
intersection with `Q` and its quotient image separately. The uniform
fixed-subgroup identity bounds the former; `S = Q E` bounds the latter.
The order balance makes both `Q` and `E` maximum. Equality forces
any other maximum subgroup outside `Q` to have the full quotient image.
B.2.21 then identifies its lift with `E`.

The argument runs inside the actual subgroup `S`; all normality and
self-centralizing hypotheses are relative to `S`. The final theorem remains
conditional on the two full-module calculations in `FixedSpaces`. It does
not discharge either model calculation or assert the source theorem.
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily
variable {T : Type*} [Group T] [Finite T]

omit [Finite T] in
private theorem count (Q A : Subgroup T) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup T) (Q ⊓ A) A bot_le inf_le_right

private theorem family_pair (Q E : Subgroup T) [Q.Normal]
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
private theorem max_restrict {B T : Subgroup G} (hBT : B ≤ T) :
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

variable {K : GroupClass.{u}} {A H R L : Subgroup G} {x : G}

omit [Finite G] in
/-- The fixed-space calculation identifies the opposite candidate with the
conjugate core, before invoking maximality. This discharges the order balance. -/
theorem opposite_eq_conjugate_of_fixed_spaces
    (h : Configuration K A H R L) (hb : BaumannStructure H R L) (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G))
    (hp : Factorization R L x) (hc : FixedSpaceCalculation R L x) :
    opposite R L x = (Q R L).map (MulAut.conj x).toMonoidHom := by
  let V := (U L).map (MulAut.conj x).toMonoidHom
  let Q' := (Q R L).map (MulAut.conj x).toMonoidHom
  have hVQ' : V ≤ Q' := map_mono (module_le_core h hb)
  have hQ'S : Q' ≤ S R := (conjugate_core_eq h hb hx).le.trans inf_le_left
  have hDQ' : D R L ≤ Q' := by
    rw [show Q' = S R ⊓ centralizer (V : Set G) from conjugate_core_eq h hb hx]
    exact le_inf inf_le_left hp.centralizes
  have hVnorm : V ≤ normalizer (Q R L : Set G) :=
    (hVQ'.trans hQ'S).trans (S_normalizes_Q R L)
  obtain ⟨s, hs, hsnc⟩ := SetLike.not_le_iff_exists.mp hnc
  have hsQ : s ∉ Q R L := fun hsq => hsnc ((hb.core_eq ▸ inf_le_right) hsq)
  apply le_antisymm (sup_le hVQ' hDQ')
  intro z hz
  have hzm : z ∈ (V : Set G) * (Q R L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V (Q R L) hVnorm]
    exact hp.span ▸ hQ'S hz
  obtain ⟨v, hv, q, hq, rfl⟩ := hzm
  have hqQ' : q ∈ Q' := by
    have hh := Q'.mul_mem (Q'.inv_mem (hVQ' hv)) hz
    simpa only [inv_mul_cancel_left] using hh
  have hqfixed : q ∈ Q R L ⊓ centralizer ({s} : Set G) := by
    refine ⟨hq, mem_centralizer_singleton_iff.mpr ?_⟩
    have hqV : q ∈ centralizer (V : Set G) :=
      ((conjugate_core_eq h hb hx) ▸ inf_le_right) hqQ'
    exact (mem_centralizer_iff.mp hqV s hs).symm
  have hqe := (hc.fixed s (hVQ'.trans hQ'S hs) hsQ).le hqfixed
  exact (opposite R L x).mul_mem (mem_sup_left hv) hqe.2


/-- Uniform full fixed subgroups determine the entire
maximum elementary family, by counting and the unique-lift theorem B.2.21. -/
theorem family_of_fixed_spaces
    (h : Configuration K A H R L) (hb : BaumannStructure H R L) (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G))
    (hp : Factorization R L x) (hf : F R L = ⊥)
    (hc : FixedSpaceCalculation R L x) :
    elementaryAbelianMaxSubgroups (S R) = {Q R L, opposite R L x} := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : Q R L ≤ S R := hb.core_eq ▸ inf_le_left
  have hES : opposite R L x ≤ S R :=
    sup_le (hp.span ▸ le_sup_left) inf_le_left
  let Q₀ := (Q R L).subgroupOf (S R)
  let E₀ := (opposite R L x).subgroupOf (S R)
  have hel := elementary_candidates_of_frattini_eq_bot h hb hp hf
  let _ : IsElementaryAbelian 2 (Q R L) := hel.1
  let _ : IsElementaryAbelian 2 (opposite R L x) := hel.2
  let _ : IsElementaryAbelian 2 Q₀ := IsElementaryAbelian.subgroupOf hQS
  let _ : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hES
  let _ : Q₀.Normal :=
    (normal_subgroupOf_iff_le_normalizer hQS).mpr (S_normalizes_Q R L)
  have hself : centralizer (Q₀ : Set (S R)) = Q₀ := by
    apply le_antisymm
    · intro z hz
      change (z : G) ∈ Q R L
      rw [hb.core_eq]
      refine ⟨z.property, mem_centralizer_iff.mpr ?_⟩
      intro v hv
      exact congrArg Subtype.val (mem_centralizer_iff.mp hz
        ⟨v, hb.module_le hv⟩ (module_le_core h hb hv))
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hspan : Q R L ⊔ opposite R L x = S R := by
    apply le_antisymm (sup_le hQS hES)
    rw [hp.span]
    exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have hspan₀ : Q₀ ⊔ E₀ = ⊤ := by
    rw [← subgroupOf_sup hQS hES, hspan, subgroupOf_self]
  have hne : ¬ E₀ ≤ Q₀ := by
    intro he
    apply hnc
    intro u hu
    have hue : u ∈ opposite R L x := mem_sup_left hu
    have huq := he (show (⟨u, hES hue⟩ : S R) ∈ E₀ from hue)
    exact (hb.core_eq ▸ inf_le_right) huq
  have hfix₀ (s : S R) (hs : s ∉ Q₀) :
      Q₀ ⊓ centralizer ({s} : Set (S R)) = Q₀ ⊓ E₀ := by
    ext z
    have hh := SetLike.ext_iff.mp (hc.fixed s s.property hs) (z : G)
    simpa only [mem_inf, mem_centralizer_singleton_iff, Q₀, E₀, mem_subgroupOf,
      Subtype.ext_iff, Subgroup.coe_mul] using hh
  have hbalance : Nat.card Q₀ = Nat.card E₀ := by
    rw [card_restrict hQS, card_restrict hES]
    rw [opposite_eq_conjugate_of_fixed_spaces h hb hx hnc hp hc,
      card_map_of_injective (MulAut.conj x).injective]
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
      simp [he]
  · intro hB
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · apply (max_restrict hQS).mp
      rw [hfamily]
      exact Set.mem_insert _ _
    · obtain rfl := Set.mem_singleton_iff.mp hB
      apply (max_restrict hES).mp
      rw [hfamily]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)


/-- Assemble the two genuine block calculations. Neither input is provided
by this theorem; both remain prerequisites for `NaturalFamilyInput`. -/
theorem naturalFamilyInput_of_calculations (K : GroupClass.{u})
    (hl : LinearInput (G := G) K) (ha : AlternatingThreeInput (G := G) K) :
    NaturalFamilyInput (G := G) K := by
  intro A H R L h hb ht x hx hnc hp hf
  apply family_of_fixed_spaces h hb hx hnc hp hf
  rcases ht with ht | ht
  · exact hl A H R L h hb ht x hx hnc hp hf
  · exact ha A H R L h hb ht x hx hnc hp hf

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily
end
