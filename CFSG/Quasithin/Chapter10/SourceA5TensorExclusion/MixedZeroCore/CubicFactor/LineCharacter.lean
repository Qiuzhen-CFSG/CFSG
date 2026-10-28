module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.CubicFactor.Reduction
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction

/-!
# The first cubic character of the original Cartan quotient

Conjugation on the three nonidentity elements of the original tensor line
constructs an actual symmetric-three character of A∨T. Its kernel is the
literal line centralizer, the order-nine Cartan maps onto A₃, and the Hall
cubic is killed. Line movement makes the character surjective, so it kills
O₂(A∨T) and descends through that exact quotient.

This is the first character used by the mixed Cartan-pair construction;
the second character and the exchange-sign condition are separate steps.
The final source discharge stays with qt-d-tensor-mixed-zero-core.
Source: Aschbacher–Smith, original 9.3.1, printed p.732 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The literal Cartan--Sylow join preserves the original four-element line. -/
theorem cartanJoin_normalizes_tensorLine (A : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) :
    A ⊔ (T : Subgroup G) ≤ normalizer (m.tensorLine : Set G) :=
  sup_le (hAB.trans m.borel_normalizes_tensorLine) m.tensorLine_normalized

private theorem tensorLineKleinFour : IsKleinFour m.tensorLine where
  card_four := m.card_tensorLine
  exponent_two := by
    let := m.tensorLine_elementary
    let : Nontrivial m.tensorLine := Finite.one_lt_card_iff_nontrivial.mp (by rw [m.card_tensorLine]; decide)
    exact IsElementaryAbelian.exponent_eq_prime (p := 2)

/-- The first cubic character is conjugation on the three nonidentity points
of the original tensor line. -/
def tensorLineCubicCharacter (A : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) :
    (A ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 3) :=
  let := m.tensorLineKleinFour
  (IsKleinFour.autEquivPermThree m.tensorLine).toMonoidHom.comp
    (m.tensorLine.normalizerMonoidHom.comp
      (inclusion (m.cartanJoin_normalizes_tensorLine A hAB)))

/-- Its kernel is the literal centralizer, not an abstract subgroup marking. -/
theorem tensorLineCubicCharacter_eq_one_iff (A : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (x : (A ⊔ (T : Subgroup G) : Subgroup G)) :
    m.tensorLineCubicCharacter A hAB x = 1 ↔
      (x : G) ∈ centralizer (m.tensorLine : Set G) := by
  let := m.tensorLineKleinFour
  change IsKleinFour.autEquivPermThree m.tensorLine
    (m.tensorLine.normalizerMonoidHom _) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  change _ ∈ m.tensorLine.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- Restriction to the original torus has exactly its given Hall cubic as kernel. -/
theorem tensorLineCubicCharacter_cartan_kernel (A B : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G)) :
    ((m.tensorLineCubicCharacter A hAB).comp
      (inclusion (show A ≤ A ⊔ (T : Subgroup G) from le_sup_left))).ker = B.subgroupOf A := by
  ext a
  change m.tensorLineCubicCharacter A hAB (inclusion le_sup_left a) = 1 ↔ (a : G) ∈ B
  rw [m.tensorLineCubicCharacter_eq_one_iff, hBC]
  exact ⟨fun h => ⟨a.property,h⟩, fun h => h.2⟩

/-- The order-nine torus acts through the whole alternating cubic. -/
theorem tensorLineCubicCharacter_cartan_image (A B : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G)) :
    (A.subgroupOf (A ⊔ (T : Subgroup G))).map (m.tensorLineCubicCharacter A hAB) =
      alternatingGroup (Fin 3) := by
  let q := m.tensorLineCubicCharacter A hAB
  let f := q.comp (inclusion (show A ≤ A ⊔ (T : Subgroup G) from le_sup_left))
  have hk : Nat.card f.ker = 3 := by
    rw [m.tensorLineCubicCharacter_cartan_kernel A B hAB hBC,
      Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv,hB3]
  have hr : Nat.card f.range = 3 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hk,hA9] at hh
    omega
  have he : f.range = (A.subgroupOf (A ⊔ (T : Subgroup G))).map q := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inclusion le_sup_left a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [←he]
  apply eq_of_le_of_card_ge
  · intro x hx
    have hc : x ^ 3 = 1 := by
      have hh : (⟨x,hx⟩ : f.range)^3 = 1 := by
        simpa only [hr] using (pow_card_eq_one' (x := (⟨x,hx⟩ : f.range)))
      exact congrArg Subtype.val hh
    have heven : ∀ x : Equiv.Perm (Fin 3), x^3=1 → x ∈ alternatingGroup (Fin 3) := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    exact heven x hc
  · rw [hr,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- The actual Hall cubic has trivial first character. -/
theorem tensorLineCubicCharacter_hall_image (A B : Subgroup G)
    (hAB : A ≤ sourceOrbitBorel T L)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G)) :
    (B.subgroupOf (A ⊔ (T : Subgroup G))).map (m.tensorLineCubicCharacter A hAB) = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro b hb
  exact (m.tensorLineCubicCharacter_eq_one_iff A hAB b).mpr ((hBC ▸ hb).2)

/-- Movement of the original line makes its degree-three character onto. -/
theorem tensorLineCubicCharacter_surjective
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    Function.Surjective (m.tensorLineCubicCharacter A hAB) := by
  let q := m.tensorLineCubicCharacter A hAB
  have hA : alternatingGroup (Fin 3) ≤ q.range := by
    rw [← m.tensorLineCubicCharacter_cartan_image A B hAB hA9 hBA hB3 hBC]
    rintro _ ⟨a,_,rfl⟩
    exact ⟨a,rfl⟩
  have hthree : 3 ∣ Nat.card q.range := by
    have hh := card_dvd_of_le hA
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc] at hh
    exact hh
  let f := q.comp (inclusion (show (T : Subgroup G) ≤ A ⊔ (T : Subgroup G) from le_sup_right))
  have hp : IsPGroup 2 f.range := T.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hn : f.range ≠ ⊥ := by
    intro he
    obtain ⟨t,ht,htc⟩ := Set.not_subset.mp (m.sylow_moves_tensorLine_of_old_residual_moves hH hmove)
    apply htc
    apply (m.tensorLineCubicCharacter_eq_one_iff A hAB (inclusion le_sup_right ⟨t,ht⟩)).mp
    have hh : f ⟨t,ht⟩ ∈ f.range := ⟨⟨t,ht⟩,rfl⟩
    have hone : f ⟨t,ht⟩ = 1 := by simpa only [he,mem_bot] using hh
    exact hone
  have htwo : 2 ∣ Nat.card q.range :=
    (hp.card_eq_or_dvd.resolve_left (fun h => hn (card_eq_one.mp h))).trans
      (card_dvd_of_le (show f.range ≤ q.range from fun _ ⟨t,ht⟩ => ⟨inclusion le_sup_right t,ht⟩))
  have hle := Nat.card_le_card_of_injective q.range.subtype q.range.subtype_injective
  have hS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [hS] at hle
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  rw [hS]
  change Nat.card q.range = 6
  have hd : 6 ∣ Nat.card q.range :=
    (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hd)

/-- The original Cartan two-core is killed by the line character. -/
theorem tensorLineCubicCharacter_twoCore_le_kernel
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G) ≤ (m.tensorLineCubicCharacter A hAB).ker := by
  let q := m.tensorLineCubicCharacter A hAB
  have hq := m.tensorLineCubicCharacter_surjective hH A B hAB hA9 hBA hB3 hBC hmove
  have hz : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (IsPGroup.ker_isPGroup_of_injective Function.injective_id)
    exact hh.symm.trans MonoidHom.ker_id
  have hn : ((pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)).map q).Normal :=
    (inferInstance : (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)).Normal).map q hq
  have hc : (pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)).map q ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hn,pCore_isPGroup.map q⟩
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp (hz ▸ hc))

/-- The first cubic character descends through the actual two-core quotient.
Its value on every original element still detects exactly line centralization. -/
theorem exists_tensorLine_quotient_character
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    ∃ q : ((A ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)) →* Equiv.Perm (Fin 3),
      Function.Surjective q ∧
      (q.comp (QuotientGroup.mk' _)) = m.tensorLineCubicCharacter A hAB ∧
      ∀ x : (A ⊔ (T : Subgroup G) : Subgroup G),
        q (QuotientGroup.mk' _ x) = 1 ↔ (x : G) ∈ centralizer (m.tensorLine : Set G) := by
  let f := m.tensorLineCubicCharacter A hAB
  let q := QuotientGroup.lift _ f
    (m.tensorLineCubicCharacter_twoCore_le_kernel hH A B hAB hA9 hBA hB3 hBC hmove)
  refine ⟨q,?_,rfl,?_⟩
  · intro y
    obtain ⟨x,hx⟩ := m.tensorLineCubicCharacter_surjective hH A B hAB hA9 hBA hB3 hBC hmove y
    exact ⟨QuotientGroup.mk' _ x,hx⟩
  · intro x
    exact m.tensorLineCubicCharacter_eq_one_iff A hAB x

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
