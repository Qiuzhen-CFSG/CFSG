module

public import Theory.GroupTheory.PGroup.C4SquareCubicInvolutions
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Inside geometry from the cubic core's involution cover

The cubic involution dichotomy gives either only central core involutions
or two elementary sixteens meeting in the central omega four. In the latter
case, each inside elementary eight has centralizer one of those sixteens. Its normalizer is the core if it contains the central
omega, and otherwise is that elementary sixteen.

The distinguished normalizer cannot embed in the core: the preimages of
the two elementary sixteens each have order at most eight, while every
element outside its C₄-square base is an involution. These two preimages
and the base would cover a group of order 32 with total size strictly
less than 32. This supplies the non-embedding clause of the order-64 case.
The branch without non-base core involutions has no inside elementary eight.

Source: MacWilliams, Trans. AMS 150 (1970), Lemma 3 and Styles 2–3,
printed pp.380–384, DOI 10.1090/S0002-9947-1970-0276324-3.
-/
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace C4SquareCubicInvertingExtension

variable {P : Type*} [Group P] [Finite P]
  {C R X Y : Subgroup P} {a : MulAut P} {t : P}
  (h : C4SquareCubicInvertingExtension C R a t)
  (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
  (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
  (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
  (e : C ≃* C4SquareExtension.Model)

include h hC hno hZ e in
/-- An inside elementary eight in an elementary sixteen has that full centralizer. -/
public theorem elementary_eight_centralizer_eq (A E : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcardA : Nat.card A = 16) (hAR : A ≤ R)
    (hE : IsElementaryAbelian 2 E) (hcardE : Nat.card E = 8) (hEA : E ≤ A) :
    centralizer (E : Set P) = A := by
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 E := hE
  have hn : ¬ E ≤ C := by
    intro hEC
    have hEW : E ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
      intro x hx
      exact hC.mem_omega_center_of_square_eq_one hno hZ (hEC hx)
        (elemPow_eq_one_of_isElementaryAbelian x hx)
    have hh := card_le_of_le hEW
    rw [card_map_of_injective (center P).subtype_injective, hZ, hcardE] at hh
    omega
  obtain ⟨u, hu, huC⟩ := SetLike.not_le_iff_exists.mp hn
  apply le_antisymm
  · rw [← h.centralizer_eq_of_elementary_sixteen hC hno hZ e A hA hcardA u
      (hEA hu) (hAR (hEA hu)) huC]
    exact centralizer_le (Set.singleton_subset_iff.mpr hu)
  · exact A.le_centralizer.trans (centralizer_le hEA)

include h hC hno hZ e in
/-- The normalizer of an inside elementary eight in an elementary sixteen lies in the core. -/
public theorem elementary_eight_normalizer_le_core (A E : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcardA : Nat.card A = 16) (hAR : A ≤ R)
    (hWA : (omega₁ (center P) (p := 2)).map (center P).subtype ≤ A)
    (hE : IsElementaryAbelian 2 E) (hcardE : Nat.card E = 8) (hEA : E ≤ A) :
    normalizer (E : Set P) ≤ R := by
  have hc := h.elementary_eight_centralizer_eq hC hno hZ e A E hA hcardA hAR hE hcardE hEA
  have hn := normalizer_le_normalizer_centralizer E
  rw [hc, h.normalizer_elementary_sixteen_eq_core hno A hA hcardA
    (h.core_le_normalizer_of_omega_le hC hno hZ e A hAR hWA)] at hn
  exact hn

include h hC hno hZ e in
/-- Style 2: an elementary eight containing the central omega has normalizer the core. -/
public theorem elementary_eight_normalizer_eq_core_of_omega_le (A E : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcardA : Nat.card A = 16) (hAR : A ≤ R)
    (hE : IsElementaryAbelian 2 E) (hcardE : Nat.card E = 8) (hEA : E ≤ A)
    (hWE : (omega₁ (center P) (p := 2)).map (center P).subtype ≤ E) :
    normalizer (E : Set P) = R := by
  exact le_antisymm (h.elementary_eight_normalizer_le_core hC hno hZ e A E
    hA hcardA hAR (hWE.trans hEA) hE hcardE hEA)
    (h.core_le_normalizer_of_omega_le hC hno hZ e E (hEA.trans hAR) hWE)

include h hC hno hZ e in
/-- Style 3: an elementary eight missing part of the central omega has elementary normalizer sixteen. -/
public theorem elementary_eight_normalizer_eq_sixteen_of_not_omega_le (A E : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcardA : Nat.card A = 16) (hAR : A ≤ R)
    (hWA : (omega₁ (center P) (p := 2)).map (center P).subtype ≤ A)
    (hE : IsElementaryAbelian 2 E) (hcardE : Nat.card E = 8) (hEA : E ≤ A)
    (hWE : ¬ (omega₁ (center P) (p := 2)).map (center P).subtype ≤ E) :
    normalizer (E : Set P) = A := by
  let : IsElementaryAbelian 2 E := hE
  let : IsElementaryAbelian 2 A := hA
  let W := (omega₁ (center P) (p := 2)).map (center P).subtype
  let K := E ⊓ W
  have hc := h.elementary_eight_centralizer_eq hC hno hZ e A E hA hcardA hAR hE hcardE hEA
  apply le_antisymm
  · intro y hy
    by_contra hyA
    have hyR := h.elementary_eight_normalizer_le_core hC hno hZ e A E
      hA hcardA hAR hWA hE hcardE hEA hy
    have hcomm (z : E) : ⁅y, (z : P)⁆ ∈ K := by
      refine ⟨?_, h.core_commutator_mem_omega hC hno hZ e y z hyR (hAR (hEA z.property))⟩
      exact E.mul_mem ((hy z).mp z.property) (E.inv_mem z.property)
    let f : E →* K := {
      toFun z := ⟨⁅y, (z : P)⁆, hcomm z⟩
      map_one' := Subtype.ext (by simp)
      map_mul' z v := by
        apply Subtype.ext
        change ⁅y, (z : P) * (v : P)⁆ = ⁅y, (z : P)⁆ * ⁅y, (v : P)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hz : ⁅y, (v : P)⁆ ∈ center P := map_subtype_le _ (hcomm v).2
        calc
          _ = ⁅y, (z : P)⁆ * ((z : P) * ⁅y, (v : P)⁆) * (z : P)⁻¹ := by group
          _ = ⁅y, (z : P)⁆ * ⁅y, (v : P)⁆ := by rw [(mem_center_iff.mp hz) z]; group }
    have hk : f.ker.map E.subtype = K := by
      apply le_antisymm
      · rintro z ⟨v, hv, rfl⟩
        refine ⟨v.property, ?_⟩
        by_contra hvW
        have hvC : (v : P) ∉ C := by
          intro hvC
          exact hvW (hC.mem_omega_center_of_square_eq_one hno hZ hvC
            (elemPow_eq_one_of_isElementaryAbelian (v : P) v.property))
        have hcv := h.centralizer_eq_of_elementary_sixteen hC hno hZ e A hA hcardA v
          (hEA v.property) (hAR (hEA v.property)) hvC
        apply hyA
        rw [← hcv]
        exact mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val (show f v = 1 from hv)))
      · intro z hz
        refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
        apply MonoidHom.mem_ker.mpr
        apply Subtype.ext
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (mem_center_iff.mp (map_subtype_le _ hz.2) y)
    have hkcard : Nat.card f.ker = Nat.card K := by
      calc
        Nat.card f.ker = Nat.card (f.ker.map E.subtype) :=
          (card_map_of_injective E.subtype_injective).symm
        _ = Nat.card K := congrArg (fun H : Subgroup P => Nat.card H) hk
    have hKcard : Nat.card K ≤ 2 := by
      have hwcard : Nat.card W = 4 := by
        rw [card_map_of_injective (center P).subtype_injective, hZ]
      have hd : Nat.card K ∣ 2 ^ 2 := by
        simpa only [hwcard, show (2 : ℕ)^2 = 4 by decide] using
          (card_dvd_of_le (show K ≤ W from inf_le_right))
      have hn4 : Nat.card K ≠ 4 := by
        intro hfour
        have heq : K = W := eq_of_le_of_card_ge inf_le_right (by rw [hfour, hwcard])
        exact hWE (show W ≤ E from heq ▸ (show K ≤ E from inf_le_left))
      have hkLe : Nat.card K ≤ 4 := Nat.le_of_dvd (by decide) (by simpa using hd)
      interval_cases hkc : Nat.card K <;> simp_all
    have hrange : Nat.card f.range ≤ Nat.card K :=
      Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    have hm := f.ker.index_mul_card
    rw [index_ker, hkcard, hcardE] at hm
    nlinarith
  · rw [← hc]
    exact centralizer_le_normalizer _

include h hC hno hZ e in
omit [IsMulCommutative C] in
/-- The distinguished normalizer cannot embed into a core with a split involution cover. -/
public theorem normalizer_centralizer_not_embed_core_of_split (s : SplitInvolutionCover R X Y)
    (f : normalizer (centralizer ({t} : Set P) : Set P) →* R) :
    ¬ Function.Injective f := by
  intro hf
  let N := normalizer (centralizer ({t} : Set P) : Set P)
  let g : N →* P := R.subtype.comp f
  have hg : Function.Injective g := R.subtype_injective.comp hf
  let B := C.subgroupOf N
  let U := X.comap g
  let V := Y.comap g
  have hB : Nat.card B = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (h.base_le_normalizer_centralizer hC hno hZ e)).toEquiv,
      Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hN : Nat.card N = 32 := h.normalizer_centralizer_card hC hno hZ e
  have bound (A : Subgroup P) (hA : IsElementaryAbelian 2 A) (hcA : Nat.card A = 16) :
      Nat.card (A.comap g) ≤ 8 := by
    let : IsElementaryAbelian 2 A := hA
    let D := A.comap g
    let j : D → A := fun x => ⟨g x, x.property⟩
    have hj : Function.Injective j := by
      intro x y he
      exact Subtype.ext (hg (congrArg (fun z : A => (z : P)) he))
    have hbound : Nat.card D ≤ 16 := by
      rw [← hcA]
      exact Nat.card_le_card_of_injective j hj
    let : IsElementaryAbelian 2 D := {
      toIsMulCommutative := A.comap_injective_isMulCommutative hg
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        apply hg
        change g ((x : N) ^ 2) = g 1
        rw [map_pow, map_one]
        exact elemPow_eq_one_of_isElementaryAbelian (g x) x.property) }
    have hne : Nat.card D ≠ 16 := h.normalizer_centralizer_no_sixteen hC hno hZ e D inferInstance
    have hd : Nat.card D ∣ 32 := by simpa only [hN] using D.card_subgroup_dvd_card
    interval_cases hdcard : Nat.card D <;> simp_all
  have hU : Nat.card U ≤ 8 := bound X s.left_elementary s.left_card
  have hV : Nat.card V ≤ 8 := bound Y s.right_elementary s.right_card
  have cover : (B : Set N) ∪ (U : Set N) ∪ (V : Set N) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    by_cases hnC : (n : P) ∈ C
    · exact Or.inl (Or.inl hnC)
    · have htN : t ∈ N := (centralizer ({t} : Set P)).le_normalizer
        (mem_centralizer_singleton_iff.mpr rfl)
      have hnR : (n : P) ∉ R := by
        intro hnR
        apply hnC
        rw [← h.normalizer_inf_core_eq_base hC hno hZ e]
        exact ⟨n.property, hnR⟩
      have hnt : (n : P) * t ∈ C := by
        rw [← h.normalizer_inf_core_eq_base hC hno hZ e]
        exact ⟨N.mul_mem n.property htN, (R.mul_mem_iff_of_index_two h.core_index).mpr
          (iff_of_false hnR h.outside_not_mem)⟩
      have ht2 : t * t = 1 := by simpa only [pow_two] using
        (show t ^ 2 = 1 from h.outside_order ▸ pow_orderOf_eq_one t)
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have hn2 : (n : P) ^ 2 = 1 := by
        have hh := h.outside_inverts _ hnt
        rw [hti, mul_inv_rev, hti] at hh
        have htn : t * (n : P) * t * t = t * (n : P)⁻¹ := by
          simpa only [mul_assoc] using hh
        have hni : (n : P) = (n : P)⁻¹ := by
          apply mul_left_cancel (a := t)
          simpa only [mul_assoc, ht2, mul_one] using htn
        rw [pow_two]
        nth_rw 1 [hni]
        exact inv_mul_cancel _
      have hng : g n ^ 2 = 1 := by
        rw [← map_pow, show n ^ 2 = 1 from Subtype.ext hn2, map_one]
      rcases s.cover (g n) (f n).property hng with hx | hy
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hy
  have hdis : ¬ Disjoint (B : Set N) (U : Set N) := by
    intro hd
    exact Set.disjoint_left.mp hd B.one_mem U.one_mem
  have hlt := Set.ncard_union_lt (Set.toFinite (B : Set N)) (Set.toFinite (U : Set N)) hdis
  have hle := Set.ncard_union_le ((B : Set N) ∪ (U : Set N)) (V : Set N)
  rw [cover, Set.ncard_univ] at hle
  change ((B : Set N) ∪ (U : Set N)).ncard < Nat.card B + Nat.card U at hlt
  change Nat.card N ≤ ((B : Set N) ∪ (U : Set N)).ncard + Nat.card V at hle
  omega

include h hC hno hZ e in
/-- The nonsplit branch has no inside elementary eights and only central inside involutions. -/
public theorem geometry_of_core_square_one_mem_base
    (hinside : ∀ u ∈ R, u ^ 2 = 1 → u ∈ C) : ElementaryEightIndexTwoGeometry R t := by
  apply h.geometry_of_core_profiles hC hno hZ e
  · intro u huR hu2
    exact Or.inl (hC.involution_mem_ambient_center hno hZ
      (hinside u huR (hu2 ▸ pow_orderOf_eq_one u)) hu2)
  · intro E hE hcard hER
    let : IsElementaryAbelian 2 E := hE
    have hle : E ≤ (omega₁ (center P) (p := 2)).map (center P).subtype := by
      intro u hu
      have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
      exact hC.mem_omega_center_of_square_eq_one hno hZ (hinside u (hER hu) hu2) hu2
    have hc := card_le_of_le hle
    rw [card_map_of_injective (center P).subtype_injective, hZ, hcard] at hc
    omega

include h hC hno hZ e in
/-- A split involution cover supplies all remaining inside profiles. -/
public theorem geometry_of_split_involution_cover (s : SplitInvolutionCover R X Y) :
    ElementaryEightIndexTwoGeometry R t := by
  apply h.geometry_of_core_profiles hC hno hZ e
  · exact h.inside_centralizer_profile_of_split hC hno hZ e s
  · intro E hE hcard hER
    have one_side (A : Subgroup P) (hA : IsElementaryAbelian 2 A)
        (hcA : Nat.card A = 16) (hAR : A ≤ R)
        (hWA : (omega₁ (center P) (p := 2)).map (center P).subtype ≤ A)
        (hEA : E ≤ A) :
        (Nat.card (normalizer (E : Set P)) = 64 ∧
          ∀ f : normalizer (centralizer ({t} : Set P) : Set P) →*
              normalizer (E : Set P), ¬ Function.Injective f) ∨
        (IsElementaryAbelian 2 (normalizer (E : Set P)) ∧
          Nat.card (normalizer (E : Set P)) = 16) := by
      by_cases hWE : (omega₁ (center P) (p := 2)).map (center P).subtype ≤ E
      · left
        have hn := h.elementary_eight_normalizer_eq_core_of_omega_le hC hno hZ e A E
          hA hcA hAR hE hcard hEA hWE
        rw [hn]
        exact ⟨h.core_card, h.normalizer_centralizer_not_embed_core_of_split hC hno hZ e s⟩
      · right
        rw [h.elementary_eight_normalizer_eq_sixteen_of_not_omega_le hC hno hZ e A E
          hA hcA hAR hWA hE hcard hEA hWE]
        exact ⟨hA, hcA⟩
    right
    rcases s.elementary_le_left_or_right E hE hER with hEX | hEY
    · exact one_side X s.left_elementary s.left_card s.left_le
        (s.inf_eq ▸ (show X ⊓ Y ≤ X from inf_le_left)) hEX
    · exact one_side Y s.right_elementary s.right_card s.right_le
        (s.inf_eq ▸ (show X ⊓ Y ≤ Y from inf_le_right)) hEY

include h hC hno hZ e in
/-- The split/nonsplit involution dichotomy completes the geometry. -/
public theorem geometry_of_involution_dichotomy
    (hdichotomy : (∀ u ∈ R, u ^ 2 = 1 → u ∈ C) ∨
      ∃ X Y : Subgroup P, SplitInvolutionCover R X Y) :
    ElementaryEightIndexTwoGeometry R t := by
  rcases hdichotomy with hbase | ⟨X, Y, hsplit⟩
  · exact h.geometry_of_core_square_one_mem_base hC hno hZ e hbase
  · exact h.geometry_of_split_involution_cover hC hno hZ e hsplit

include h hC hno hZ e in
/-- The cubic C₄-square inverting extension has the full elementary-eight
index-two geometry, including the inside centralizers and normalizer profiles. -/
public theorem geometry (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) : ElementaryEightIndexTwoGeometry R t := by
  exact h.geometry_of_involution_dichotomy hC hno hZ e
    (h.core_involution_dichotomy hC hno hZ e ha hfree)

end C4SquareCubicInvertingExtension
