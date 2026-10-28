module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.Cubics
public import Theory.GroupTheory.CubicAutomorphismLines

/-!
# Selecting an irreducible actual cubic residual

For one or two symmetric-three factors, the Sylow subgroup realizes every
ambient permutation of the factors. A Sylow-invariant cubic line is a
coordinate line: an independent factor involution separates the two
cubic directions. Thus either there is a normal cubic factor, or the full
elementary group of order nine is Sylow-irreducible. The selected subgroup
is normal and equals its commutator with the actual Thompson Sylow image.

Source: Aschbacher–Smith 15.4.12, printed pp.1160–1161.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (closure S)]

theorem cubicFactor_injective (d : Exceptional S) : Function.Injective (cubicFactor d) := by
  intro i j he
  by_contra hij
  have hi := cubicFactors_disjoint d hij
  rw [he, disjoint_self] at hi
  have hc := cubicFactor_card d j
  rw [hi, card_bot] at hc
  omega

def sylowStar : Subgroup (Star (S := S)) := (S : Subgroup H).map (starMap (closure S))

omit [IsElementaryAbelian 2 (closure S)] in
theorem sylowImage_le_sylowStar : sylowImage (S := S) ≤ sylowStar (S := S) :=
  map_mono (sSup_le fun _ h => h.1)

variable [Finite H]

omit [IsElementaryAbelian 2 (closure S)] in
private theorem sylow_covers_two_image {K : Type*} [Group K]
    (f : H →* K) (hp : IsPGroup 2 K) (h : H) : ∃ s : S, f s = f h := by
  let P := S.mapSurjective f.rangeRestrict_surjective
  have ht : (P : Subgroup f.range) = ⊤ :=
    (P.is_maximal' ((hp.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  have hm : (⟨f h,⟨h,rfl⟩⟩ : f.range) ∈ (P : Subgroup f.range) := ht.symm ▸ mem_top _
  obtain ⟨s,hs,he⟩ := hm
  exact ⟨⟨s,hs⟩,congrArg Subtype.val he⟩

omit [Finite H] in
theorem factorAction_isTwoGroup (d : Exceptional S) (hc : d.count = 1 ∨ d.count = 2) :
    IsPGroup 2 (Equiv.Perm (Fin d.count)) := by
  have hcard : Nat.card (Equiv.Perm (Fin d.count)) = (d.count).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rcases hc with hc | hc
  · exact IsPGroup.of_card (n := 0) (by rw [hcard,hc]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [hcard,hc]; rfl)

theorem cubicFactor_normal_of_sylow_normalized (d : Exceptional S)
    (hc : d.count = 1 ∨ d.count = 2) (i : Fin d.count)
    (hn : sylowStar (S := S) ≤ normalizer (cubicFactor d i : Set (Star (S := S)))) :
    (cubicFactor d i).Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (closure S : Set H)) g
  let f := (factorAction d).comp (starMap (closure S))
  obtain ⟨s,hs⟩ := sylow_covers_two_image (S := S) f (factorAction_isTwoGroup d hc) h
  have hfix : factorAction d (starMap (closure S) s) i = i := by
    apply cubicFactor_injective d
    rw [← cubicFactor_action]
    exact mem_normalizer_iff_map_conj_eq.mp
      (hn (mem_map_of_mem (starMap (closure S)) s.property))
  have he : factorAction d (starMap (closure S) h) i = i :=
    (congrArg (fun u : Equiv.Perm (Fin d.count) => u i) hs).symm.trans hfix
  change (cubicFactor d i).map (MulAut.conj (starMap (closure S) h)).toMonoidHom = _
  rw [cubicFactor_action,he]

theorem cubic_line_eq_factor (d : Exceptional S) (i j : Fin d.count) (hij : i ≠ j)
    (hijall : (Finset.univ : Finset (Fin d.count)) = {i,j})
    (C : Subgroup (Star (S := S))) (hC : C ≤ cubicProduct d Finset.univ)
    (hcard : Nat.card C = 3) (hn : sylowStar (S := S) ≤ normalizer (C : Set (Star (S := S)))) :
    C = cubicFactor d i ∨ C = cubicFactor d j := by
  classical
  let R := cubicProduct d Finset.univ
  have hR : R = cubicFactor d i ⊔ cubicFactor d j := by
    change cubicProduct d Finset.univ = _
    rw [cubicProduct,hijall,Finset.sup_insert,Finset.sup_singleton]
  have hI : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
      (Finset.univ : Finset (Fin d.count)).card = 2 := Or.inr (by rw [hijall,Finset.card_pair hij])
  let := cubicProduct_normal d
  let := cubicProduct_elementary d Finset.univ hI
  let : CommGroup R := IsMulCommutative.instCommGroup
  let Z := (cubicFactor d i).subgroupOf R
  let X := (cubicFactor d j).subgroupOf R
  let B := C.subgroupOf R
  change C ≤ R at hC
  have hiR : cubicFactor d i ≤ R := hR ▸ le_sup_left
  have hjR : cubicFactor d j ≤ R := hR ▸ le_sup_right
  have hZ : Nat.card Z = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hiR).toEquiv).trans (cubicFactor_card d i)
  have hX : Nat.card X = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hjR).toEquiv).trans (cubicFactor_card d j)
  have hB : Nat.card B = 3 := (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).trans hcard
  have hgen : Z ⊔ X = ⊤ := by
    change (cubicFactor d i).subgroupOf R ⊔ (cubicFactor d j).subgroupOf R = ⊤
    rw [← subgroupOf_sup hiR hjR,← hR,subgroupOf_self]
  obtain ⟨t,htj,htJ,ht1,ht2⟩ := exists_factor_involution d j
  let a : MulAut R := MulAut.conjNormal t
  have hfix : ∀ z ∈ Z, a z = z := by
    intro z hz
    apply Subtype.ext
    change t*(z : Star (S := S))*t⁻¹ = z
    have he : t*(z : Star (S := S)) = (z : Star (S := S))*t :=
      (factors_commute d hij (cubicFactor_le d i hz) htj).symm.eq
    rw [he, mul_inv_cancel_right]
  have hinv : ∀ x ∈ X, a x = x⁻¹ := by
    intro x hx
    apply Subtype.ext
    exact factor_involution_inverts d j htj ht1 ht2 hx
  have hstable : ∀ b ∈ B, a b ∈ B := by
    intro b hb
    exact (le_normalizer_iff.mp hn) t (sylowImage_le_sylowStar htJ) b hb
  rcases Theory.GroupTheory.CubicAutomorphismLines.invariant_line_eq Z X B hZ hX hB hgen a hfix hinv hstable with he | he
  · left
    have hh := congrArg (fun U : Subgroup R => U.map R.subtype) he
    simpa only [B,Z,map_subgroupOf_eq_of_le hC,map_subgroupOf_eq_of_le hiR] using hh
  · right
    have hh := congrArg (fun U : Subgroup R => U.map R.subtype) he
    simpa only [B,X,map_subgroupOf_eq_of_le hC,map_subgroupOf_eq_of_le hjR] using hh

theorem exists_irreducible_cubicProduct (d : Exceptional S) (hc : d.count = 1 ∨ d.count = 2) :
    ∃ I : Finset (Fin d.count), (I.card = 1 ∨ I.card = 2) ∧ (cubicProduct d I).Normal ∧
      ∀ C : Subgroup (Star (S := S)), C ≤ cubicProduct d I →
        sylowStar (S := S) ≤ normalizer (C : Set (Star (S := S))) →
          C = ⊥ ∨ C = cubicProduct d I := by
  classical
  by_cases hn : ∃ i, (cubicFactor d i).Normal
  · obtain ⟨i,hi⟩ := hn
    refine ⟨{i},Or.inl (Finset.card_singleton i),?_,?_⟩
    · simpa only [cubicProduct,Finset.sup_singleton] using hi
    · intro C hC _
      have he : cubicProduct d {i} = cubicFactor d i := Finset.sup_singleton
      rw [he] at hC ⊢
      let : Fact (Nat.card (cubicFactor d i)).Prime := ⟨cubicFactor_card d i ▸ Nat.prime_three⟩
      rcases (C.subgroupOf (cubicFactor d i)).eq_bot_or_eq_top_of_prime_card with hb | ht
      · left
        have hh := congrArg (fun U : Subgroup (cubicFactor d i) => U.map (cubicFactor d i).subtype) hb
        simpa only [map_subgroupOf_eq_of_le hC,Subgroup.map_bot] using hh
      · right
        have hh := congrArg (fun U : Subgroup (cubicFactor d i) => U.map (cubicFactor d i).subtype) ht
        rw [map_subgroupOf_eq_of_le hC,← MonoidHom.range_eq_map,range_subtype] at hh
        exact hh
  · have hI : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
        (Finset.univ : Finset (Fin d.count)).card = 2 := by simpa only [Finset.card_univ,Fintype.card_fin] using hc
    refine ⟨Finset.univ,hI,cubicProduct_normal d,?_⟩
    intro C hC hnorm
    have hcard := card_dvd_of_le hC
    rw [cubicProduct_card d Finset.univ hI] at hcard
    obtain ⟨k,hk,hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hcard
    have hk2 : k ≤ 2 := by rcases hI with hI | hI <;> omega
    interval_cases k
    · left
      exact card_eq_one.mp hkcard
    · exfalso
      have hc3 : Nat.card C = 3 := hkcard
      rcases hI with hI | hI
      · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hI
        have he : cubicProduct d Finset.univ = cubicFactor d i := by rw [cubicProduct,hi,Finset.sup_singleton]
        exact hn ⟨i, he ▸ cubicProduct_normal d⟩
      · obtain ⟨i,j,hij,hijall⟩ := Finset.card_eq_two.mp hI
        rcases cubic_line_eq_factor d i j hij hijall C hC hc3 hnorm with he | he
        · exact hn ⟨i,cubicFactor_normal_of_sylow_normalized d hc i (he ▸ hnorm)⟩
        · exact hn ⟨j,cubicFactor_normal_of_sylow_normalized d hc j (he ▸ hnorm)⟩
    · right
      apply eq_of_le_of_card_ge hC
      rw [cubicProduct_card d Finset.univ hI,hkcard]
      exact Nat.pow_le_pow_right (by decide) (by rcases hI with hI | hI <;> omega)

theorem selected_commutator (d : Exceptional S) (I : Finset (Fin d.count))
    (hn : (cubicProduct d I).Normal) :
    ⁅cubicProduct d I,sylowImage (S := S)⁆ = cubicProduct d I := by
  let := hn
  apply le_antisymm (commutator_le_left _ _)
  apply Finset.sup_le
  intro i hi
  exact (cubicFactor_le_commutator d i).trans
    (commutator_mono (Finset.le_sup hi) le_rfl)

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
