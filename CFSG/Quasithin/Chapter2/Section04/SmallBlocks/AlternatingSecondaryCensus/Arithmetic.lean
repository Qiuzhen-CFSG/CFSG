module
public import Theory.GroupTheory.DihedralEightSections
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.GroupTheory.PrimeRankFixedJoin
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Endpoints

/-!
# Sylow-order screens for the secondary alternating-five centralizer

The actual central involution doubles the Sylow order of a centerless
component. Thus the Mathieu rows exceed the secondary Sylow order 128.
The symplectic unipotent order leaves only the binary derived group A6,
and the binary M22 cover already has Sylow order 256.
Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
variable {H : Type*} [Group H] [Finite H]

theorem symplectic_row_of_sylow_card_le_128 (P : Sylow 2 H)
    (hP : Nat.card P ≤ 128) (K : Subgroup H)
    (hK : ComponentRefinement.LieType.IsDerivedSymplecticFour K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨n,hn,F,_,_,hF,⟨e⟩⟩ := hK
  by_cases hn1 : n = 1
  · subst n
    exact ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (by simpa using hF))⟩
  have hn2 : 2 ≤ n := by omega
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn2
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e' := e.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two
    (by omega : 2 < Nat.card F))
  let Q := Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hn
  have hb := (sylow_card_section_le P K e'.toMonoidHom e'.surjective Q).trans hP
  change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) ≤ 128 at hb
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent] at hb
  have hh := Nat.pow_le_pow_left hfour 4
  norm_num at hh
  omega

theorem central_involution_sylow_bound (P : Sylow 2 H) (K : Subgroup H)
    (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (hZ : center K = ⊥) (Q : Sylow 2 K) : 2 * Nat.card Q ≤ Nat.card P := by
  let B := (Q : Subgroup K).map K.subtype
  have huK : u ∉ K := by
    intro h
    have hz : (⟨u,h⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (mem_center_iff.mp hu (k : H))
    rw [hZ] at hz
    have he : u = 1 := congrArg Subtype.val (mem_bot.mp hz)
    rw [he,orderOf_one] at hu2
    omega
  have hdis : Disjoint B (zpowers u) :=
    B.disjoint_zpowers_of_prime_order_not_mem u hu2 (fun h => huK (map_subtype_le _ h))
  have hn : zpowers u ≤ normalizer (B : Set H) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    apply zpowers_le.mpr
    intro b hb
    exact mem_center_iff.mp hu b
  have hp : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hu2]; rfl)
  have hj : IsPGroup 2 (B ⊔ zpowers u : Subgroup H) :=
    (Q.isPGroup'.map K.subtype).to_sup_of_normal_left' hp hn
  obtain ⟨P',hP'⟩ := hj.exists_le_sylow
  have hb := (card_le_of_le hP').trans_eq (Nat.card_congr (P'.equiv P).toEquiv)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint B (zpowers u) hn hdis,
    card_map_of_injective K.subtype_injective,Nat.card_zpowers,hu2] at hb
  simpa only [Nat.mul_comm] using hb

theorem mathieu_twenty_two_row_false (P : Sylow 2 H) (hP : Nat.card P ≤ 128)
    (K : Subgroup H) (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (e : K ≃* Sporadic.Mathieu.M22) : False := by
  have hZ : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hz : e x ∈ center Sporadic.Mathieu.M22 :=
      (centerCongr e ⟨x,hx⟩).property
    rw [Sporadic.Mathieu.m22_center_eq_bot] at hz
    exact mem_bot.mpr (e.injective (by simpa using mem_bot.mp hz))
  let Q : Sylow 2 K := Classical.choice inferInstance
  have hc : Nat.card Q = 128 := by
    rw [Q.card_eq_multiplicity,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    decide +kernel
  have hh := (central_involution_sylow_bound P K u hu hu2 hZ Q).trans hP
  omega

theorem mathieu_twenty_three_row_false (P : Sylow 2 H) (hP : Nat.card P ≤ 128)
    (K : Subgroup H) (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (e : K ≃* Sporadic.Mathieu.M23) : False := by
  have hZ : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hz : e x ∈ center Sporadic.Mathieu.M23 :=
      (centerCongr e ⟨x,hx⟩).property
    rw [Sporadic.Mathieu.M23Geometry.m23_center_eq_bot] at hz
    exact mem_bot.mpr (e.injective (by simpa using mem_bot.mp hz))
  let Q : Sylow 2 K := Classical.choice inferInstance
  have hc : Nat.card Q = 128 := by
    rw [Q.card_eq_multiplicity,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    decide +kernel
  have hh := (central_involution_sylow_bound P K u hu hu2 hZ Q).trans hP
  omega

theorem binary_mathieu_row_false_of_sylow_card_le_128 (P : Sylow 2 H)
    (hP : Nat.card P ≤ 128) (K : Subgroup H)
    (hcore : Nat.card (pCore 2 K) = 2)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) : False := by
  have hKcard : Nat.card K = 887040 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),
      Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order,hcore]
  let Q : Sylow 2 K := Classical.choice inferInstance
  have hQcard : Nat.card Q = 256 := by
    rw [Q.card_eq_multiplicity,hKcard]
    decide +kernel
  have hb := (sylow_card_section_le P K (MonoidHom.id K) Function.surjective_id Q).trans hP
  omega

end CFSG.Quasithin.Chapter2.SmallBlocks.AlternatingSecondaryCensus
