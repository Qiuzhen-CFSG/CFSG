module
public import Stellmacher.SectionThree.TwoGroupSeriesAction
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Stellmacher.SectionThree.KleinActionCoreQuotient

/-!
# The S3 core quotient from a normal elementary eight

Let `Q = O₂(G)` have order 64 in a finite characteristic-two group with Sylow
two-subgroup of order 128. Suppose normal subgroups `Z ≤ U ≤ Q` have orders
two and eight, `U` is elementary abelian, `[U,Q] ≤ Z`, and `C_Q(U)` has order
sixteen. Then the actual quotient `G/Q` is isomorphic to the symmetric group
on three letters. The characteristic-two hypothesis is stated directly as
`C_G(Q) ≤ Q`, the body of the native `IsCharacteristicTwoType` predicate.

Conjugation acts on the literal Klein-four quotient `U/Z`. Its kernel `K`
contains `Q`. To prove the reverse containment, write `C = C_Q(U)`. Normality
and order two make `Z` central. The Three Subgroups Lemma puts `[K,Q]` in `C`,
while `C/U` is a normal subgroup of order two in `G/U`, giving `[K,C] ≤ U`.
Thus `K` acts trivially on every factor of the normal series
`Q ≥ C ≥ U ≥ Z ≥ 1`. The series-action theorem makes its image on `Q` a
two-group; the action kernel lies in `Q` by characteristic two. Hence `K` is
a normal two-group and equals `Q`. The faithful Klein-action recognition
then uses the core and Sylow orders to identify the quotient with S3.

This is the terminal quotient recognition in Stellmacher (9.1), Journal of
Algebra 190 (1997), p.48. All subgroup, cardinality, and action inputs remain
explicit; no graph hypothesis or local classification conclusion is assumed.
-/

namespace Stellmacher.SectionThree
open Subgroup
open scoped commutatorElement
universe u

private theorem invariant_normal_subgroup
    {G : Type u} [Group G] (K Q H : Subgroup G) [Q.Normal] [H.Normal]
    (_hHQ : H ≤ Q)
    (act : MulDistribMulAction K Q)
    (hact : ∀ k : K, ∀ q : Q, (k • q : Q).val = (k : G) * (q : G) * (k : G)⁻¹) :
    IsInvariant K Q (H.subgroupOf Q) := by
  constructor
  intro k q
  change (q : G) ∈ H ↔ (k • q : Q).val ∈ H
  rw [hact]
  exact mem_normalizer_iff.mp (le_normalizer_of_normal (H := H) (K := K) k.property) q

private theorem kernel_eq_core
    {G : Type u} [Group G] [Finite G]
    (U Z : Subgroup G) [U.Normal] [Z.Normal]
    (hUQ : U ≤ pCore 2 G) (hZU : Z ≤ U)
    (hUcard : Nat.card U = 8) (hZcard : Nat.card Z = 2)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hCcard : Nat.card (pCore 2 G ⊓ centralizer (U : Set G) : Subgroup G) = 16)
    (hUcomm : IsMulCommutative U)
    (hcomm : ⁅U,pCore 2 G⁆ ≤ Z)
    (K : Subgroup G) [K.Normal]
    (hQK : pCore 2 G ≤ K) (hKU : ⁅K,U⁆ ≤ Z) : K = pCore 2 G := by
  let Q := pCore 2 G
  let C := Q ⊓ centralizer (U : Set G)
  let _ : Q.Normal := pCore_normal
  let _ : C.Normal := inferInstance
  let _ : IsMulCommutative U := hUcomm
  have hZcent : Z ≤ center G := central_of_normal_card_two Z hZcard
  have hUC : U ≤ C := le_inf hUQ (Subgroup.le_centralizer (H := U))
  have hCQ : C ≤ Q := inf_le_left
  have hZQ : Z ≤ Q := hZU.trans hUQ
  have hKQ : ⁅K,Q⁆ ≤ C := by
    apply le_inf (commutator_le_right K Q)
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact (show ⁅Q,U⁆ ≤ Z by rwa [commutator_comm]).trans
        (hZcent.trans (center_le_centralizer _))
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      exact (show ⁅U,K⁆ ≤ Z by rwa [commutator_comm]).trans
        (hZcent.trans (center_le_centralizer _))
  have hKC : ⁅K,C⁆ ≤ U := by
    let q := QuotientGroup.mk' U
    have hCimage : Nat.card (C.map q) = 2 := by
      have hh := (U.subgroupOf C).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv, hUcard] at hh
      change 8 * U.relIndex C = Nat.card C at hh
      rw [show Nat.card C = 16 from hCcard] at hh
      have hi : U.relIndex C = 2 := by omega
      rw [← relIndex_ker C q, QuotientGroup.ker_mk', hi]
    have hc : C.map q ≤ center (G ⧸ U) :=
      central_of_normal_card_two (C.map q) hCimage
    have hk : q.ker = U := QuotientGroup.ker_mk' U
    rw [← hk]
    apply (map_eq_bot_iff ⁅K,C⁆).mp
    rw [map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp (hc.trans (center_le_centralizer _))
  let act : MulDistribMulAction K Q :=
    conjMulDistribMulActionOfLeNormalizer K Q le_normalizer_of_normal
  let _ := act
  have hact (k : K) (q : Q) : (k • q : Q).val = (k : G) * (q : G) * (k : G)⁻¹ := rfl
  let Cq := C.subgroupOf Q
  let Uq := U.subgroupOf Q
  let Zq := Z.subgroupOf Q
  let terms : Fin 5 → Subgroup Q := ![⊤, Cq, Uq, Zq, ⊥]
  let next : Fin 5 → Fin 5 := ![1,2,3,4,4]
  have hstab : StabilizesNormalSeries (G := Q) (A := K) terms next := by
    refine ⟨⟨0,4,rfl,rfl,⟨4,rfl⟩⟩,?_,?_,?_,?_⟩
    · intro i
      fin_cases i <;> dsimp only [terms,next]
      · exact le_top
      · exact subgroupOf_mono Q hUC
      · exact subgroupOf_mono Q hZU
      · exact bot_le
      · exact le_rfl
    · intro i
      fin_cases i <;> dsimp [terms] <;> infer_instance
    · intro i
      fin_cases i
      · constructor; intro k q; simp [terms]
      · exact invariant_normal_subgroup K Q C hCQ act hact
      · exact invariant_normal_subgroup K Q U hUQ act hact
      · exact invariant_normal_subgroup K Q Z hZQ act hact
      · constructor; intro k q
        change q = 1 ↔ k • q = 1
        constructor
        · rintro rfl; exact smul_one k
        · intro hh
          have hh' := congrArg (fun x : Q => k⁻¹ • x) hh
          simpa only [inv_smul_smul, smul_one] using hh'
    · intro i k q hq
      fin_cases i
      · change (k • q) * q⁻¹ ∈ Cq
        change (k : G) * (q : G) * (k : G)⁻¹ * (q : G)⁻¹ ∈ C
        exact hKQ (commutator_mem_commutator k.property q.property)
      · change (k • q) * q⁻¹ ∈ Uq
        change (k : G) * (q : G) * (k : G)⁻¹ * (q : G)⁻¹ ∈ U
        exact hKC (commutator_mem_commutator k.property hq)
      · change (k • q) * q⁻¹ ∈ Zq
        change (k : G) * (q : G) * (k : G)⁻¹ * (q : G)⁻¹ ∈ Z
        exact hKU (commutator_mem_commutator k.property hq)
      · change (k • q) * q⁻¹ ∈ (⊥ : Subgroup Q)
        apply mem_bot.mpr
        apply Subtype.ext
        change (k : G) * (q : G) * (k : G)⁻¹ * (q : G)⁻¹ = 1
        have hc : (k : G) * (q : G) = (q : G) * (k : G) :=
          mem_center_iff.mp (hZcent hq) k
        rw [hc, mul_inv_cancel_right, mul_inv_cancel]
      · change (k • q) * q⁻¹ ∈ (⊥ : Subgroup Q)
        have hq1 : q = 1 := hq
        simp [hq1]
  let f := MulDistribMulAction.toMulAut K Q
  have himage : IsPGroup 2 f.range :=
    isPGroup_range_of_stabilizes_two_group_series (pCore_isPGroup (p := 2) (G := G)) terms next hstab
  have hkerle : f.ker.map K.subtype ≤ Q := by
    rintro x ⟨k,hk,rfl⟩
    apply hchar
    intro q hq
    have hh := DFunLike.congr_fun hk (⟨q,hq⟩ : Q)
    have hh' := congrArg (fun y : Q => (y : G)) hh
    change (k : G) * q * (k : G)⁻¹ = q at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hker : IsPGroup 2 f.ker :=
    ((pCore_isPGroup (p := 2) (G := G)).to_le hkerle).of_equiv
      (f.ker.equivMapOfInjective K.subtype K.subtype_injective).symm
  have hKp : IsPGroup 2 K := by
    have hh := himage.comap_of_ker_isPGroup f hker
    rw [show f.range.comap f = ⊤ from by ext k; simp] at hh
    exact hh.of_equiv topEquiv
  exact le_antisymm (le_sSup ⟨inferInstance, hKp⟩) hQK

/-- The normal elementary-eight configuration identifies the actual two-core
quotient of a characteristic-two group with S3. -/
public theorem quotient_s3_of_normal_elementary_eight
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (hPcard : Nat.card P = 128) (hQcard : Nat.card (pCore 2 G) = 64)
    (U Z : Subgroup G) [U.Normal] [Z.Normal] [IsElementaryAbelian 2 U]
    (hZU : Z ≤ U) (hUQ : U ≤ pCore 2 G)
    (hUcard : Nat.card U = 8) (hZcard : Nat.card Z = 2)
    (hcomm : ⁅U,pCore 2 G⁆ ≤ Z)
    (hCcard : Nat.card (pCore 2 G ⊓ centralizer (U : Set G) : Subgroup G) = 16)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  let N := Z.subgroupOf U
  let _ : N.Normal := inferInstance
  let W := U ⧸ N
  have hWcard : Nat.card W = 4 := by
    have hh := N.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv, hZcard,
      index_eq_card, hUcard] at hh
    change 2 * Nat.card W = 8 at hh
    omega
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; decide)
  have hexp : Monoid.exponent W ∣ 2 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro w
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N w
    rw [← map_pow]
    have hu : u ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property)
    rw [hu,map_one]
  let _ : IsKleinFour W := {
    card_four := hWcard
    exponent_two := (Nat.prime_two.eq_one_or_self_of_dvd _ hexp).resolve_left
      (by have hh := Monoid.one_lt_exponent (G := W); omega) }
  obtain ⟨r,hr⟩ := exists_quotient_conjugation_action (⊤ : Subgroup G) U Z
    le_normalizer_of_normal le_normalizer_of_normal (inferInstance : N.Normal)
  let rho : G →* MulAut W := r.comp topEquiv.symm.toMonoidHom
  have hQK : pCore 2 G ≤ rho.ker := by
    have hh := quotient_conjugation_action_kills_commutator_layer
      (⊤ : Subgroup G) U Z (pCore 2 G) (inferInstance : N.Normal)
      le_normalizer_of_normal hcomm r hr
    intro q hq
    exact hh hq
  have hKU : ⁅rho.ker,U⁆ ≤ Z := by
    apply commutator_le.mpr
    intro k hk u hu
    have hh := DFunLike.congr_fun hk (QuotientGroup.mk' N ⟨u,hu⟩)
    change r (topEquiv.symm k) (QuotientGroup.mk' N ⟨u,hu⟩) =
      QuotientGroup.mk' N ⟨u,hu⟩ at hh
    rw [hr] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    change (k * u * k⁻¹) / u ∈ Z at hz
    simpa only [commutatorElement_def,div_eq_mul_inv] using hz
  have hker : rho.ker = pCore 2 G := kernel_eq_core U Z hUQ hZU hUcard hZcard hchar
    hCcard inferInstance hcomm rho.ker hQK hKU
  exact quotient_s3_of_klein_action_kernel_eq_pCore P hPcard hQcard rho hker

end Stellmacher.SectionThree
