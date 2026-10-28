module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Normality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Witness
public import Stellmacher.MaxElementaryOffenderEquality

/-!
# Kernel-rank comparison for a selected singleton preimage

Let N be the full preimage of the selected factor, K the star kernel, and
C = C_{U_v}(N). For an elementary subgroup E, the replacement
B = (E ∩ N) C is elementary and has exactly the image E* ∩ H. Its order
satisfies |B| [E : E ∩ N] = |E| [C : C ∩ E]. Consequently a nontrivial
coordinate image and a bound by the maximum elementary order in K produce
a moving maximum elementary subgroup in the full preimage N.

The comparison is with K, not with the maximum order in G_v: complementary
strong offenders can make the latter strictly larger than the maximum in N.
We also select an actual global maximum moving X from the already proved
commutator [X,J(G_v)*] = X.

The index version proves that the replacement is a global maximum whenever
its fixed-part gain covers the restriction index. In particular an index at
most two can be paid for by one fixed-part vector outside E. A complementary
centralizer bound discharges that vector premise automatically.

These are conditional rank-transfer steps. The native two-factor and
hyperplane cases still have to provide the nontrivial coordinate intersection
and the cardinal bound. The support order four alone has not discharged
those premises, and this module does not assert the source Thompson equality
without them.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
printed pp.75–76, and the construction in 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton
variable {G D : Type*} [Group G] [Group D] [Finite G]

omit [Finite G] in
private theorem card_inf_index (A B : Subgroup G) :
    Nat.card (A ⊓ B : Subgroup G) * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left, inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ B) B bot_le inf_le_right

omit [Finite G] in
private theorem card_join (A C : Subgroup G) [C.Normal] :
    Nat.card (A ⊔ C : Subgroup G) = Nat.card A * A.relIndex C := by
  have hA := card_inf_index C A
  have hC := card_inf_index A C
  have hD := card_inf_index C (A ⊔ C)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_right] at hD
  calc
    Nat.card (A ⊔ C : Subgroup G) = Nat.card C * C.relIndex A := hD.symm
    _ = (Nat.card (A ⊓ C : Subgroup G) * A.relIndex C) * C.relIndex A := by rw [hC]
    _ = (Nat.card (C ⊓ A : Subgroup G) * C.relIndex A) * A.relIndex C := by
      rw [inf_comm A C]; ac_rfl
    _ = Nat.card A * A.relIndex C := by rw [hA]

omit [Finite G] in
private theorem intersect_index (E N C : Subgroup G) (hCN : C ≤ N) :
    (E ⊓ N).relIndex C = E.relIndex C := by
  change ((E ⊓ N).subgroupOf C).index = (E.subgroupOf C).index
  congr 1
  ext x
  exact and_iff_left (hCN x.property)

omit [Finite G] in
/-- Exact cardinal bookkeeping for restriction followed by central replacement. -/
private theorem replacement_card (E N C : Subgroup G) [C.Normal] (hCN : C ≤ N) :
    Nat.card ((E ⊓ N) ⊔ C : Subgroup G) * N.relIndex E =
      Nat.card E * E.relIndex C := by
  rw [card_join, intersect_index E N C hCN]
  calc
    Nat.card (E ⊓ N : Subgroup G) * E.relIndex C * N.relIndex E =
        (Nat.card (N ⊓ E : Subgroup G) * N.relIndex E) * E.relIndex C := by
      rw [inf_comm E N]; ac_rfl
    _ = Nat.card E * E.relIndex C := by rw [card_inf_index]

/-- Dominate the kernel maximum, then select a maximum in the full preimage. -/
private theorem maximum_of_kernel_bound (f : G →* D) (H : Subgroup D)
    (B : Subgroup G) (hBN : B ≤ H.comap f) (hB : IsElementaryAbelian 2 B)
    (hne : B.map f ≠ ⊥) (hcard : elementaryAbelianMaxOrder f.ker ≤ Nat.card B) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (H.comap f), A.map f ≠ ⊥ := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (H.comap f)
  by_cases ha : A.map f = ⊥
  · have hAK : A ≤ f.ker := (map_eq_bot_iff A).mp ha
    have hc : Nat.card A ≤ Nat.card B :=
      (elementary_card_le_maxOrder f.ker A hAK hA.2.1).trans hcard
    exact ⟨B, ⟨hBN, hB, fun F hFN hF => (hA.2.2 F hFN hF).trans hc⟩, hne⟩
  · exact ⟨A, hA, ha⟩

private theorem replacement_maximum (f : G →* D) (H : Subgroup D)
    (E C : Subgroup G) [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 C]
    [C.Normal] (hCK : C ≤ f.ker)
    (hcentral : C ≤ centralizer (H.comap f : Set G))
    (hne : E.map f ⊓ H ≠ ⊥)
    (hbound : elementaryAbelianMaxOrder f.ker * (H.comap f).relIndex E ≤
      Nat.card E * E.relIndex C) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap f), B.map f ≠ ⊥ := by
  let N := H.comap f
  let A := E ⊓ N
  let B := A ⊔ C
  have hCN : C ≤ N := hCK.trans (fun x hx => by
    change f x ∈ H
    rw [show f x = 1 from hx]
    exact H.one_mem)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.sup_of_le_centralizer
    (hcentral.trans (centralizer_le (show A ≤ N from inf_le_right)))
  have hmap : A.map f = E.map f ⊓ H := by
    apply le_antisymm
    · exact le_inf (map_mono inf_le_left) (map_le_iff_le_comap.mpr inf_le_right)
    · rintro x ⟨⟨a, ha, rfl⟩, hx⟩
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  have hBne : B.map f ≠ ⊥ := by
    intro hb
    apply hne
    apply le_bot_iff.mp
    rw [← hmap, ← hb]
    exact map_mono le_sup_left
  have hcount : Nat.card B * N.relIndex E = Nat.card E * E.relIndex C :=
    replacement_card E N C hCN
  have hpos : 0 < N.relIndex E := by
    have hc := card_inf_index N E
    have hp : 0 < Nat.card E := Nat.card_pos
    nlinarith
  have hcard : elementaryAbelianMaxOrder f.ker ≤ Nat.card B := by
    apply Nat.le_of_mul_le_mul_left (c := N.relIndex E) _ hpos
    rw [mul_comm _ (elementaryAbelianMaxOrder f.ker), mul_comm _ (Nat.card B), hcount]
    exact hbound
  exact maximum_of_kernel_bound f H B (sup_le inf_le_right hCN) hB hBne hcard

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]

/-- Select an actual global maximum whose star image moves the chosen residual. -/
theorem minimalSolvable_exists_global_maximum_moving
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X) :
    ∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      ⁅X, E.map (starMk z v)⁆ ≠ ⊥ := by
  classical
  obtain ⟨_, hcomm⟩ := minimalSolvable_global_thompson L T z v hz S hS hX
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) =
      JGstar z v := starImage_intrinsic_thompson z v ⊤ (Gv v)
        (by rw [← MonoidHom.range_eq_map, range_subtype])
  by_contra! hnone
  have hc : JGstar z v ≤ centralizer (X : Set (Gstar z v)) := by
    rw [← hmap]
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro E hE
    apply map_le_iff_le_comap.mp
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (hnone E hE))
  have hb : ⁅X, JGstar z v⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
  exact hX.1.1.2.2.1 (hcomm.symm.trans hb)

/-- The fixed part of U_v used for replacing the complementary coordinates. -/
def singletonFixed (z v : G) (H : Subgroup (Gstar z v)) : Subgroup (Gv v) :=
  internalUv z v ⊓ centralizer (H.comap (starMk z v) : Set (Gv v))

instance (z v : G) (H : Subgroup (Gstar z v)) [H.Normal] :
    (singletonFixed z v H).Normal := inferInstanceAs
      (internalUv z v ⊓ centralizer (H.comap (starMk z v) : Set (Gv v))).Normal

omit [Finite G] in
/-- The fixed replacement lies in the original star kernel. -/
theorem singletonFixed_le_ker (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (H : Subgroup (Gstar z v)) :
    singletonFixed z v H ≤ (starMk z v).ker := by
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  rw [starMk_ker_internal z v hz]
  exact inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)

omit [Finite G] in
/-- Exact order formula for the actual singleton replacement, before any
maximum-rank premise is imposed. -/
theorem singleton_replacement_card (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (E : Subgroup (Gv v)) :
    Nat.card ((E ⊓ H.comap (starMk z v)) ⊔ singletonFixed z v H : Subgroup (Gv v)) *
        (H.comap (starMk z v)).relIndex E =
      Nat.card E * E.relIndex (singletonFixed z v H) := by
  apply NormalThompson.Maximum.Singleton.replacement_card
  intro x hx
  change starMk z v x ∈ H
  rw [show starMk z v x = 1 from singletonFixed_le_ker z v hz H hx]
  exact H.one_mem

/-- Literal star-preimage application of the rank comparison. Only an elementary
subgroup is used as the starting point; maximum order is proved in the full preimage. -/
theorem star_maximum_of_singleton_replacement_bound
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal]
    (E : Subgroup (Gv v)) (hE : IsElementaryAbelian 2 E)
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hbound : elementaryAbelianMaxOrder (starMk z v).ker *
        (H.comap (starMk z v)).relIndex E ≤
      Nat.card E * E.relIndex (singletonFixed z v H)) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      B.map (starMk z v) ≠ ⊥ := by
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  let : IsElementaryAbelian 2 (singletonFixed z v H) :=
    IsElementaryAbelian.of_le (show singletonFixed z v H ≤ internalUv z v from inf_le_left)
  let : IsElementaryAbelian 2 E := hE
  exact NormalThompson.Maximum.Singleton.replacement_maximum (starMk z v) H E
    (singletonFixed z v H) (singletonFixed_le_ker z v hz H) inf_le_right hne hbound

/-- If the fixed-part gain covers the restriction index, the literal replacement
is still a maximum in the whole centralizer G_v. No kernel-rank equality is assumed. -/
theorem singleton_replacement_mem_global_maximum
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal]
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hindex : (H.comap (starMk z v)).relIndex E ≤
      E.relIndex (singletonFixed z v H)) :
    (E ⊓ H.comap (starMk z v)) ⊔ singletonFixed z v H ∈
      elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)) := by
  let N := H.comap (starMk z v)
  let C := singletonFixed z v H
  let B := (E ⊓ N) ⊔ C
  let : IsElementaryAbelian 2 E := hE.2.1
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  let : IsElementaryAbelian 2 C :=
    IsElementaryAbelian.of_le (show C ≤ internalUv z v from inf_le_left)
  let : IsElementaryAbelian 2 (E ⊓ N : Subgroup (Gv v)) :=
    IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 B := IsElementaryAbelian.sup_of_le_centralizer
    ((show C ≤ centralizer (N : Set (Gv v)) from inf_le_right).trans
      (centralizer_le (show E ⊓ N ≤ N from inf_le_right)))
  have hc : Nat.card B * N.relIndex E = Nat.card E * E.relIndex C :=
    singleton_replacement_card z v hz H E
  have hn : 0 < N.relIndex E := by
    have hcE := NormalThompson.Maximum.Singleton.card_inf_index N E
    have hp : 0 < Nat.card E := Nat.card_pos
    nlinarith
  have hcard : Nat.card E ≤ Nat.card B := by
    apply Nat.le_of_mul_le_mul_right (c := N.relIndex E) _ hn
    rw [hc]
    exact Nat.mul_le_mul_left _ hindex
  exact ⟨le_top, he, fun A hA hAe => (hE.2.2 A hA hAe).trans hcard⟩

/-- A global maximum with sufficient fixed-part gain supplies a moving maximum
in the full preimage. The new maximum is established by cardinal comparison. -/
theorem star_maximum_of_singleton_index_bound
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal]
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hindex : (H.comap (starMk z v)).relIndex E ≤
      E.relIndex (singletonFixed z v H)) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      B.map (starMk z v) ≠ ⊥ := by
  apply star_maximum_of_singleton_replacement_bound z v hz H E hE.2.1 hne
  have hK : elementaryAbelianMaxOrder (starMk z v).ker ≤ Nat.card E := by
    rw [← maxOrder_eq_card_of_mem ⊤ E hE]
    exact (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ le_top).1
  exact Nat.mul_le_mul hK hindex

/-- Losing at most one binary dimension is compensated by any fixed-part
vector outside E. This uses the full preimage and the actual star map. -/
theorem star_maximum_of_singleton_index_two
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal]
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hindex : (H.comap (starMk z v)).relIndex E ≤ 2)
    (hfixed : ¬ singletonFixed z v H ≤ E) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      B.map (starMk z v) ≠ ⊥ := by
  apply star_maximum_of_singleton_index_bound z v hz H E hE hne
  have hc := NormalThompson.Maximum.Singleton.card_inf_index E (singletonFixed z v H)
  have hpos : 0 < E.relIndex (singletonFixed z v H) := by
    have hp : 0 < Nat.card (singletonFixed z v H) := Nat.card_pos
    nlinarith
  have hn : E.relIndex (singletonFixed z v H) ≠ 1 := mt relIndex_eq_one.mp hfixed
  have ht : 2 ≤ E.relIndex (singletonFixed z v H) := by omega
  exact hindex.trans ht

/-- For an image of order at most four, a nontrivial intersection with the
selected factor bounds the restriction index by two. -/
theorem star_maximum_of_singleton_small_image
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal]
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hcard : Nat.card (E.map (starMk z v)) ≤ 4)
    (hfixed : ¬ singletonFixed z v H ≤ E) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      B.map (starMk z v) ≠ ⊥ := by
  apply star_maximum_of_singleton_index_two z v hz H E hE hne _ hfixed
  rw [relIndex_comap]
  have hc := NormalThompson.Maximum.Singleton.card_inf_index H (E.map (starMk z v))
  have hi := (one_lt_card_iff_ne_bot (H ⊓ E.map (starMk z v))).mpr (by rwa [inf_comm])
  nlinarith

/-- If the fixed part detects the complementary action, the index-two criterion
needs no separate fixed-vector witness. The contained case uses E itself. -/
theorem star_maximum_of_singleton_centralizer_index_two
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal]
    (hcentral : centralizer (singletonFixed z v H : Set (Gv v)) ≤ H.comap (starMk z v))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hindex : (H.comap (starMk z v)).relIndex E ≤ 2) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      B.map (starMk z v) ≠ ⊥ := by
  by_cases hEN : E ≤ H.comap (starMk z v)
  · refine ⟨E, ⟨hEN, hE.2.1, fun A _ hA => hE.2.2 A le_top hA⟩, ?_⟩
    intro hb
    exact hne (by rw [hb, bot_inf_eq])
  · apply star_maximum_of_singleton_index_two z v hz H E hE hne hindex
    intro hC
    apply hEN
    let : IsElementaryAbelian 2 E := hE.2.1
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance :
      E ≤ centralizer (E : Set (Gv v))).trans ((centralizer_le hC).trans hcentral)

/-- Apply the rank-transfer witness to the parent's literal Thompson closing
lemma. The numerical and nontrivial-intersection premises remain explicit. -/
theorem star_thompson_eq_of_singleton_replacement_bound
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v)) (hE : IsElementaryAbelian 2 E)
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hbound : elementaryAbelianMaxOrder (starMk z v).ker *
        (H.comap (starMk z v)).relIndex E ≤
      Nat.card E * E.relIndex (singletonFixed z v H)) :
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  obtain ⟨B, hB, hmove⟩ :=
    star_maximum_of_singleton_replacement_bound z v hz H E hE hne hbound
  exact star_thompson_eq_of_maximum z v H e B hB hmove

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products

end
