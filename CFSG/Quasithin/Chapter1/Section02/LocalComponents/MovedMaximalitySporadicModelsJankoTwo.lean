module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsMathieu
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Hall--Janko in the moved-component obstruction

The certified double-coset cover places a proper full-Sylow overgroup in
one of the fixed locals, of orders 1920 and 1152. Two distinct components
would force two prime factors outside two and three, impossible in either
order. The whole-group case uses the inherited simplicity and perfection.

The final application uses the original normalized overcomponent's literal
quotient by its solvable radical. This discharges A.3.12(16) for the
uniqueness obstruction in 1.2.8(1), printed pp.47--48 and 506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open Sporadic.LeechRelated.J2

private theorem local_components_equal (J : Subgroup Carrier)
    (hcard : Nat.card J = 1920 ∨ Nat.card J = 1152)
    (P : Subgroup J) (B C : Subgroup P) (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  by_contra hn
  obtain ⟨p,r,hp,hr,hp2,hp3,hr2,hr3,hcardPR,_⟩ := hB.exists_prime_pair_of_ne hC hn
  have hd := hcardPR.trans P.card_subgroup_dvd_card
  rcases hcard with hc | hc
  · have key (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
        (hd : p ∣ Nat.card J) : p = 5 := by
      rw [hc] at hd
      have hs : p ∣ 2^7 * 3 * 5 := hd
      rcases hp.dvd_mul.mp hs with hs | hs
      · rcases hp.dvd_mul.mp hs with htwo | hthree
        · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow htwo))).elim
        · exact (hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hthree)).elim
      · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hs
    have hp5 := key p hp hp2 hp3 ((dvd_mul_right p r).trans hd)
    have hr5 := key r hr hr2 hr3 ((dvd_mul_left r p).trans hd)
    rw [hp5,hr5,hc] at hd
    norm_num at hd
  · have hpd := (dvd_mul_right p r).trans hd
    rw [hc] at hpd
    have hs : p ∣ 2^7 * 3^2 := hpd
    rcases hp.dvd_mul.mp hs with htwo | hthree
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow htwo))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hthree))

private theorem janko_two_unique [IsSimpleGroup Carrier] [Group.IsPerfect Carrier] :
    SylowOvergroupComponentUnique Carrier := by
  apply SylowOvergroupComponentUnique.of_proper_overgroups
  intro S P hSP hP B C hB hC
  have hidx : ¬ 2 ∣ P.index := fun h => S.not_dvd_index (h.trans (index_dvd_of_le hSP))
  obtain ⟨g,hg⟩ := exists_conj_overgroup_of_index_primeTo ExceptionalParabolics.Seed.s P
    (IsPGroup.of_card (n := 7) ExceptionalParabolics.PairNormalizer.card_s) hidx
  let e := MulAut.conj g
  let R := P.comap e.toMonoidHom
  have hR : R ≠ ⊤ := by
    intro ht
    apply hP
    have hm := congrArg (Subgroup.map e.toMonoidHom) ht
    change (P.comap e.toMonoidHom).map e.toMonoidHom =
      (⊤ : Subgroup Carrier).map e.toMonoidHom at hm
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hm
  have hu (J : Subgroup Carrier) (hc : Nat.card J = 1920 ∨ Nat.card J = 1152) :
      SylowOvergroupComponentUnique J := by
    intro _ U _ V W hV hW
    exact local_components_equal J hc U V W hV hW
  let f : R ≃* P := (e.subgroupMap R).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective P))
  apply (map_injective (f := f.symm.toMonoidHom) f.symm.injective)
  have hSR : ((S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective) : Subgroup Carrier) ≤ R := by
    change (S : Subgroup Carrier).map e.symm.toMonoidHom ≤ P.comap e.toMonoidHom
    rw [comap_equiv_eq_map_symm']
    exact map_mono hSP
  rcases SylowOvergroups.proper_overgroup_le R hg hR with h | h
  · exact SylowOvergroupComponentUnique.eq_of_le_overgroup _ hSR h
      (hu _ (Or.inl ExceptionalParabolics.FirstParabolic.card_l₁))
      (hB.map_equiv f.symm) (hC.map_equiv f.symm)
  · exact SylowOvergroupComponentUnique.eq_of_le_overgroup _ hSR h
      (hu _ (Or.inr ExceptionalParabolics.PairNormalizer.card_p₂))
      (hB.map_equiv f.symm) (hC.map_equiv f.symm)

variable {G : Type*} [Group G] [Finite G]

/-- Full-Sylow component uniqueness for the actual degree-100 Hall--Janko model. -/
theorem janko_two_sylow_overgroup_component_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Carrier)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  let := e.symm.isSimpleGroup
  let := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact SylowOvergroupComponentUnique.of_equiv e janko_two_unique

/-- Exclude J₂ for the literal radical quotient of the original normalized overcomponent. -/
theorem moved_normalized_not_janko_two_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Carrier) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact hu (janko_two_sylow_overgroup_component_unique hmodel)

/-- The full sporadic predicate now has only J₄, HS, He and Ru left. -/
theorem sporadic_model_remaining_after_janko_two [IsSimpleGroup G] [Group.IsPerfect G]
    (hspor : ChapterA.Section02.IsTheoremCSporadicModel G)
    (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty (G ≃* name.Carrier) := by
  obtain ⟨name,hn,iso⟩ := sporadic_model_remaining_after_mathieu hspor hu
  rcases hn with rfl | hn
  · exact (hu (janko_two_sylow_overgroup_component_unique iso)).elim
  · exact ⟨name,hn,iso⟩

/-- Apply the four-row reduction to the original normalized overcomponent. -/
theorem moved_normalized_remaining_sporadic_quotient_after_janko_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ChapterA.Section02.IsTheoremCSporadicModel Q →
      ∃ name : ClassificationModels.SporadicName,
        (name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty (Q ≃* name.Carrier) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact sporadic_model_remaining_after_janko_two hmodel hu

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
