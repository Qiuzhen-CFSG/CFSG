module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsSmall
public import Theory.GroupTheory.CComponent.RadicalPairSpectrum
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderSpectrum

/-!
# The remaining Mathieu carriers in the moved-component obstruction

Two distinct components force mixed element orders from their independent
simple radical quotients. In M₂₂ the order 384 of every involution centralizer
excludes every required prime outside two and three. In M₂₃ its order 2688
forces both primes to be seven, but 49 does not divide the group order.
For M₂₄ the primes outside two and three occur singly in the group order;
products of distinct such primes are excluded by its native odd-order spectrum.
These arguments prove uniqueness in every subgroup of each actual carrier.

The applications below use the original normalized overcomponent's literal
quotient by its solvable radical. Together with J₁, M₁₁ and M₁₂, they reduce
the full sporadic alternative to J₂, J₄, HS, He and Ru.

Source: Aschbacher--Smith A.3.12 and 1.2.8(1), printed pp.47--48 and 506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
private theorem mathieu_twenty_two_components_equal (P : Subgroup Sporadic.Mathieu.M22) (B C : Subgroup P)
    (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  by_contra hn
  obtain ⟨p,r,hp,hr,hp2,hp3,hr2,hr3,hcard,horder,⟨g,hg⟩,_⟩ := hB.exists_prime_pair_of_ne hC hn
  obtain ⟨t,ht,hd⟩ := exists_involution_centralizer_prime_dvd_of_orderOf (g : Sporadic.Mathieu.M22) hp
    ((orderOf_coe g).trans hg)
  rw [Sporadic.Mathieu.M22FourNormalizers.involution_centralizer_card t ht] at hd
  have hs : p ∣ 2 ^ 7 * 3 := hd
  rcases hp.dvd_mul.mp hs with htwo | hthree
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow htwo))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hthree)

private theorem mathieu_twenty_three_components_equal (P : Subgroup Sporadic.Mathieu.M23) (B C : Subgroup P)
    (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  by_contra hn
  obtain ⟨p,r,hp,hr,hp2,hp3,hr2,hr3,hcard,horder,hpord,hrord⟩ := hB.exists_prime_pair_of_ne hC hn
  have key (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
      (h : ∃ g : P, orderOf g = 2*p) : p = 7 := by
    obtain ⟨g,hg⟩ := h
    obtain ⟨t,ht,hd⟩ := exists_involution_centralizer_prime_dvd_of_orderOf (g : Sporadic.Mathieu.M23) hp
      ((orderOf_coe g).trans hg)
    obtain ⟨e⟩ := Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.centralizer_equiv_representative ht
    rw [Nat.card_congr e.toEquiv,
      Sporadic.Mathieu.M23Geometry.involutionRepresentative_centralizer_card] at hd
    have hs : p ∣ 2 ^ 7 * 3 * 7 := hd
    rcases hp.dvd_mul.mp hs with hs | hs
    · rcases hp.dvd_mul.mp hs with htwo | hthree
      · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow htwo))).elim
      · exact (hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hthree)).elim
    · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hs
  have hd := hcard.trans P.card_subgroup_dvd_card
  rw [key p hp hp2 hp3 hpord, key r hr hr2 hr3 hrord, Sporadic.Mathieu.m23_order] at hd
  norm_num at hd

private theorem mathieu_twenty_four_components_equal (P : Subgroup Sporadic.Mathieu.M24) (B C : Subgroup P)
    (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  by_contra hn
  obtain ⟨p,r,hp,hr,hp2,hp3,hr2,hr3,hcard,horder,_⟩ := hB.exists_prime_pair_of_ne hC hn
  have hd := hcard.trans P.card_subgroup_dvd_card
  let := Fact.mk hp
  let := Fact.mk hr
  have hpS := (Sporadic.Mathieu.m24_prime_dvd_order_iff p).mp
    ((dvd_mul_right p r).trans hd)
  have hrS := (Sporadic.Mathieu.m24_prime_dvd_order_iff r).mp
    ((dvd_mul_left r p).trans hd)
  rcases (hpS.resolve_left hp2).resolve_left hp3 with rfl | rfl | rfl | rfl <;>
    rcases (hrS.resolve_left hr2).resolve_left hr3 with rfl | rfl | rfl | rfl
  all_goals rw [Sporadic.Mathieu.m24_order] at hd
  all_goals norm_num at hd
  all_goals
    obtain ⟨g,hg⟩ := horder
    have hs := Sporadic.Mathieu.M24OddCyclic.oddOrderSpectrum (g : Sporadic.Mathieu.M24)
      (by rw [orderOf_coe,hg]; norm_num)
    norm_num [orderOf_coe,hg] at hs

variable {G : Type*} [Group G] [Finite G]

/-- The actual M22 carrier has at most one C-component in every full-Sylow overgroup. -/
theorem mathieu_twenty_two_sylow_overgroup_component_unique
    (hm : Nonempty (G ≃* Sporadic.Mathieu.M22)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  apply SylowOvergroupComponentUnique.of_equiv e
  intro _ P _ B C hB hC
  exact mathieu_twenty_two_components_equal P B C hB hC

/-- Exclude M22 for the literal radical quotient of the original normalized overcomponent. -/
theorem moved_normalized_not_mathieu_twenty_two_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Sporadic.Mathieu.M22) := by
  dsimp only
  intro hmodel
  obtain ⟨_, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  exact hu (mathieu_twenty_two_sylow_overgroup_component_unique hmodel)

/-- The actual M23 carrier has at most one C-component in every full-Sylow overgroup. -/
theorem mathieu_twenty_three_sylow_overgroup_component_unique
    (hm : Nonempty (G ≃* Sporadic.Mathieu.M23)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  apply SylowOvergroupComponentUnique.of_equiv e
  intro _ P _ B C hB hC
  exact mathieu_twenty_three_components_equal P B C hB hC

/-- Exclude M23 for the literal radical quotient of the original normalized overcomponent. -/
theorem moved_normalized_not_mathieu_twenty_three_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Sporadic.Mathieu.M23) := by
  dsimp only
  intro hmodel
  obtain ⟨_, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  exact hu (mathieu_twenty_three_sylow_overgroup_component_unique hmodel)

/-- The actual M24 carrier has at most one C-component in every full-Sylow overgroup. -/
theorem mathieu_twenty_four_sylow_overgroup_component_unique
    (hm : Nonempty (G ≃* Sporadic.Mathieu.M24)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  apply SylowOvergroupComponentUnique.of_equiv e
  intro _ P _ B C hB hC
  exact mathieu_twenty_four_components_equal P B C hB hC

/-- Exclude M24 for the literal radical quotient of the original normalized overcomponent. -/
theorem moved_normalized_not_mathieu_twenty_four_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Sporadic.Mathieu.M24) := by
  dsimp only
  intro hmodel
  obtain ⟨_, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  exact hu (mathieu_twenty_four_sylow_overgroup_component_unique hmodel)

/-- All five Mathieu rows and the separate actual J₁ model are discharged;
the other five sporadic carrier equivalences remain explicit. -/
theorem sporadic_model_remaining_after_mathieu
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hspor : ChapterA.Section02.IsTheoremCSporadicModel G)
    (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .j2 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty (G ≃* name.Carrier) := by
  obtain ⟨name,hj,h11,h12,iso⟩ := sporadic_model_remaining_of_not_unique hspor hu
  cases name with
  | m11 => exact (h11 rfl).elim
  | m12 => exact (h12 rfl).elim
  | m22 => exact (hu (mathieu_twenty_two_sylow_overgroup_component_unique iso)).elim
  | m23 => exact (hu (mathieu_twenty_three_sylow_overgroup_component_unique iso)).elim
  | m24 => exact (hu (mathieu_twenty_four_sylow_overgroup_component_unique iso)).elim
  | j3 => exact (hj rfl).elim
  | j2 => exact ⟨.j2, Or.inl rfl, iso⟩
  | j4 => exact ⟨.j4, Or.inr (Or.inl rfl), iso⟩
  | hs => exact ⟨.hs, Or.inr (Or.inr (Or.inl rfl)), iso⟩
  | he => exact ⟨.he, Or.inr (Or.inr (Or.inr (Or.inl rfl))), iso⟩
  | ru => exact ⟨.ru, Or.inr (Or.inr (Or.inr (Or.inr rfl))), iso⟩

/-- Apply the five-row reduction to the original normalized overcomponent. -/
theorem moved_normalized_remaining_sporadic_quotient_after_mathieu
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ChapterA.Section02.IsTheoremCSporadicModel Q →
      ∃ name : ClassificationModels.SporadicName,
        (name = .j2 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty (Q ≃* name.Carrier) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact sporadic_model_remaining_after_mathieu hmodel hu

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
