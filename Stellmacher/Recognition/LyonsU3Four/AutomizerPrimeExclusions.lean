module

public import Stellmacher.Recognition.LyonsU3Four.AutomizerBounds
public import Stellmacher.Recognition.LyonsU3Four.SquareRoots
public import Theory.GroupAction.Invariant

/-!
# The factors three and seven in the Sylow automizer

The center orbit has length three and its stabilizer contains S C_G(S), so
three divides the automizer index. An automorphism of order seven would fix
the center and at least six square roots of each central involution. Already
one such root fiber, together with the center, gives at least ten fixed
points. Its fixed subgroup has order a power of two dividing 64 and is
congruent to 64 modulo seven; this forces it to be all of S, a contradiction.
Cauchy's theorem excludes seven from the full automorphism-group order and
hence from the actual automizer index.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
printed p. 372. Counting the whole fixed subgroup avoids choosing a linear
model for the automorphism of order seven.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public theorem mulAut_orderOf_ne_seven
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (a : MulAut S) : orderOf a ≠ 7 := by
  classical
  intro ha
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let A := Subgroup.zpowers a
  have hp : IsPGroup 7 A := IsPGroup.of_card (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using ha)
  let Z := Subgroup.center S
  let : IsInvariant A S Z := isInvariant_of_characteristic Z
  have hZfixed : FixedPoints.subgroup A Z = ⊤ := by
    have hm := hp.card_modEq_card_fixedPoints Z
    change Nat.card Z % 7 = Nat.card (FixedPoints.subgroup A Z) % 7 at hm
    have hb := Subgroup.card_le_card_group (H := FixedPoints.subgroup A Z)
    have hZ : Nat.card Z = 4 := h.center_card
    apply Subgroup.eq_top_of_card_eq
    rw [hZ] at hm hb ⊢
    omega
  have hzfix (b : A) (z : Z) : b • (z : S) = z := by
    have hz : z ∈ FixedPoints.subgroup A Z := by rw [hZfixed]; trivial
    exact congrArg Subtype.val (hz b)
  have hzexists : ∃ z : Z, z ≠ 1 := by
    by_contra! he
    have : Subsingleton Z := ⟨fun x y => (he x).trans (he y).symm⟩
    have hc : Nat.card Z = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hc4 : Nat.card Z = 4 := h.center_card
    omega
  obtain ⟨z, hz⟩ := hzexists
  have hz1 : (z : S) ≠ 1 := fun he => hz (Subtype.ext he)
  let R := {s : S // s ^ 2 = (z : S)}
  let : MulAction A R :=
    { smul b s := ⟨b • (s : S), by
        change ((b : MulAut S) (s : S)) ^ 2 = (z : S)
        rw [← map_pow, s.property]
        exact hzfix b z⟩
      one_smul s := Subtype.ext (one_smul A (s : S))
      mul_smul b c s := Subtype.ext (mul_smul b c (s : S)) }
  have hR : Nat.card R = 20 := square_roots_card S h z.property hz1
  have hRlow : 6 ≤ Nat.card (MulAction.fixedPoints A R) := by
    have hm := hp.card_modEq_card_fixedPoints R
    change Nat.card R % 7 = Nat.card (MulAction.fixedPoints A R) % 7 at hm
    rw [hR] at hm
    omega
  let F := FixedPoints.subgroup A S
  let j : Z ⊕ MulAction.fixedPoints A R → F :=
    Sum.elim (fun w => ⟨w, fun b => hzfix b w⟩)
      (fun s => ⟨s.val.val, fun b => congrArg Subtype.val (s.property b)⟩)
  have hj : Function.Injective j := by
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hexy : (x : S) = (y : S) := congrArg (fun t : F => (t : S)) he
        exact congrArg Sum.inl (Subtype.ext hexy)
      | inr y =>
        exfalso
        have hexy : (x : S) = y.val.val := congrArg Subtype.val he
        have hx2 : (x : S) ^ 2 = 1 := by
          let _ := h.center_elementary
          exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : S) x.property
        exact hz1 (y.val.property.symm.trans (hexy ▸ hx2))
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        have hexy : x.val.val = (y : S) := congrArg Subtype.val he
        have hy2 : (y : S) ^ 2 = 1 := by
          let _ := h.center_elementary
          exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (y : S) y.property
        exact hz1 (x.val.property.symm.trans (hexy ▸ hy2))
      | inr y =>
        have hexy : x.val.val = y.val.val := congrArg (fun t : F => (t : S)) he
        exact congrArg Sum.inr (Subtype.ext (Subtype.ext hexy))
  have hlow := Nat.card_le_card_of_injective j hj
  rw [Nat.card_sum, show Nat.card Z = 4 from h.center_card] at hlow
  have hm := hp.card_modEq_card_fixedPoints S
  change Nat.card S % 7 = Nat.card F % 7 at hm
  rw [h.card] at hm
  have hdvd : Nat.card F ∣ 2 ^ 6 := by
    change Nat.card F ∣ 64
    rw [← h.card]
    exact F.card_subgroup_dvd_card
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hF : Nat.card F = 64 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at he <;> omega
  have htop : F = ⊤ := F.eq_top_of_card_eq (hF.trans h.card.symm)
  have ha1 : a = 1 := by
    apply MulEquiv.ext
    intro s
    have hs : s ∈ F := by rw [htop]; trivial
    exact hs ⟨a, Subgroup.mem_zpowers a⟩
  simp [ha1] at ha

public theorem three_dvd_automizerIndex
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : 3 ∣ automizerIndex S := by
  classical
  let N := Subgroup.normalizer (S : Set G)
  let Z := Subgroup.center S
  let : MulDistribMulAction N S := MulDistribMulAction.compHom S
    (S : Subgroup G).normalizerMonoidHom
  have hzexists : ∃ z : Z, z ≠ 1 := by
    by_contra! he
    have : Subsingleton Z := ⟨fun x y => (he x).trans (he y).symm⟩
    have hc : Nat.card Z = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hc4 : Nat.card Z = 4 := h.center_card
    omega
  obtain ⟨z, hz⟩ := hzexists
  have hz1 : (z : S) ≠ 1 := fun he => hz (Subtype.ext he)
  have horbit (x : S) : x ∈ MulAction.orbit N (z : S) ↔ x ∈ Z ∧ x ≠ 1 := by
    constructor
    · rintro ⟨n, rfl⟩
      let a := (S : Subgroup G).normalizerMonoidHom n
      constructor
      · exact (Subgroup.characteristic_iff_map_le.mp inferInstance a)
          (Subgroup.mem_map_of_mem a.toMonoidHom z.property)
      · intro he
        apply hz1
        exact a.injective (he.trans (map_one a).symm)
    · rintro ⟨hx, hx1⟩
      obtain ⟨n, hn, he⟩ := centerImage_nonidentity_normalizer_conjugate S h
        (show ((z : S) : G) ∈ centerImage S from ⟨z, z.property, rfl⟩)
        (show (x : G) ∈ centerImage S from ⟨x, hx, rfl⟩)
        (fun he => hz1 (Subtype.ext he)) (fun he => hx1 (Subtype.ext he))
      refine ⟨⟨n⁻¹, Subgroup.inv_mem _ hn⟩, ?_⟩
      apply Subtype.ext
      change n⁻¹ * ((z : S) : G) * (n⁻¹)⁻¹ = (x : G)
      simpa only [inv_inv] using he
  have hcard : Nat.card (MulAction.orbit N (z : S)) = 3 := by
    let e : MulAction.orbit N (z : S) ≃ {w : Z // w ≠ 1} :=
      { toFun := fun x => ⟨⟨x, ((horbit x).mp x.property).1⟩,
          fun he => ((horbit x).mp x.property).2 (congrArg Subtype.val he)⟩
        invFun := fun w => ⟨w.val.val, (horbit w.val.val).mpr
          ⟨w.val.property, fun he => w.property (Subtype.ext he)⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    change Nat.card ↥(({1} : Set Z)ᶜ) = 3
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
    rw [show Nat.card Z = 4 from h.center_card]
  have hle : ((S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G)).subgroupOf N ≤
      MulAction.stabilizer N (z : S) := by
    have hcen : (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G) ≤
        Subgroup.centralizer ({((z : S) : G)} : Set G) := by
      apply sup_le
      · intro s hs
        rw [Subgroup.mem_centralizer_iff]
        rintro t (rfl : t = _)
        exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.property) ⟨s, hs⟩)).symm
      · intro s hs
        rw [Subgroup.mem_centralizer_iff]
        rintro t (rfl : t = _)
        exact Subgroup.mem_centralizer_iff.mp hs _ (z : S).property
    intro n hn
    apply Subtype.ext
    change (n : G) * ((z : S) : G) * (n : G)⁻¹ = ((z : S) : G)
    have hc := Subgroup.mem_centralizer_iff.mp (hcen hn) _ (Set.mem_singleton _)
    change ((z : S) : G) * (n : G) = (n : G) * ((z : S) : G) at hc
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hd := Subgroup.index_dvd_of_le hle
  rw [MulAction.index_stabilizer, show (MulAction.orbit N (z : S)).ncard = 3 from hcard] at hd
  exact hd

public theorem not_seven_dvd_card_mulAut
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ 7 ∣ Nat.card (MulAut S) := by
  intro hd
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ := Fintype.ofFinite (MulAut S)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := MulAut S) 7
    (by simpa only [Nat.card_eq_fintype_card] using hd)
  exact mulAut_orderOf_ne_seven S h a ha

public theorem not_seven_dvd_automizerIndex
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) : ¬ 7 ∣ automizerIndex S := by
  intro hd
  exact not_seven_dvd_card_mulAut S h (hd.trans (automizerIndex_dvd_card_mulAut S))

end Stellmacher.Recognition.LyonsU3Four
