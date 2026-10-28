module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Fusion
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.Frattini.PGroup
public import Mathlib.Data.Fintype.Perm

/-!
# An intrinsic line for a Mathieu 23 Sylow pair

Let X = RS be the join of an M23 Sylow two-subgroup S and the odd complement R.
The actual order of M23 forces R to be elementary abelian of order nine. If X
has a characteristic subgroup Z of order four, conjugation gives a map from R
into the permutations of Z. Its kernel is nontrivial since nine does not divide
24. The kernel is proper since otherwise R centralizes an involution of Z,
whereas every involution centralizer in the Witt-design M23 has order 2688.
Thus the kernel has order three. It is preserved by every ambient automorphism
preserving S and R, and maps injectively to the Frattini quotient of R.

The characteristic subgroup is an explicit hypothesis. The geometric fact
needed to apply this argument, |Z(O₂(RS))| = 4, is not asserted here. The proof
uses the full pair automizer and does not assume every M23 automorphism is inner.
In particular it does not discard the field involution of the semilinear local
configuration.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Table 5.3d. The involution data
come from the concrete Witt-design development for Lemma 5.2.21.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry

/-- The source odd complement is E₉ in the actual M23 carrier. -/
public theorem m23_pair_elementary_nine {S : Sylow 2 M23} {R : Subgroup M23}
    (h : PairInput S R) : IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
  rcases h.oddComplement with ⟨he, hc⟩ | ⟨_, hc, _⟩
  · exact ⟨he, hc⟩
  · have hd := R.card_subgroup_dvd_card
    rw [hc, m23_order] at hd
    norm_num at hd

private theorem involution_centralizer_card {t : M23} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set M23)) = 2688 := by
  rw [card_centralizer_eq_of_isConj t involutionRepresentative
    (involutions_isConj _ _ ht involutionRepresentative_order)]
  exact involutionRepresentative_centralizer_card

private theorem no_nine_centralizes_involution (R : Subgroup M23)
    (hR : Nat.card R = 9) {t : M23} (ht : orderOf t = 2) :
    ¬ R ≤ centralizer ({t} : Set M23) := by
  intro hle
  have hd := card_dvd_of_le hle
  rw [hR, involution_centralizer_card ht] at hd
  norm_num at hd

variable {G : Type*} [Group G] (S R : Subgroup G)

private theorem pair_map_sup {a : MulAut R} {b : MulAut G}
    (hS : ∀ x, b x ∈ S ↔ x ∈ S) (hR : ∀ x : R, (a x : G) = b x) :
    (R ⊔ S).map b.toMonoidHom = R ⊔ S := by
  have hr : R.map b.toMonoidHom = R := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change b x ∈ R
      rw [← hR ⟨x, hx⟩]
      exact (a ⟨x, hx⟩).property
    · intro x hx
      refine ⟨a.symm ⟨x, hx⟩, (a.symm ⟨x, hx⟩).property, ?_⟩
      change b (a.symm ⟨x, hx⟩) = x
      rw [← hR]
      exact congrArg Subtype.val (a.apply_symm_apply ⟨x, hx⟩)
  have hs : S.map b.toMonoidHom = S := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hS x).mpr hx
    · intro x hx
      refine ⟨b.symm x, ?_, b.apply_symm_apply x⟩
      exact (hS _).mp (by simpa using hx)
  rw [Subgroup.map_sup, hr, hs]

private noncomputable def characteristicAction
    (Z : Subgroup (R ⊔ S : Subgroup G)) [Z.Characteristic] :
    R →* Equiv.Perm Z :=
  (MulAut.toPerm Z).comp
    ((MulAut.conjNormal (H := Z)).comp (inclusion le_sup_left))

private theorem mem_characteristicAction_ker
    (Z : Subgroup (R ⊔ S : Subgroup G)) [Z.Characteristic] (r : R) :
    r ∈ (characteristicAction S R Z).ker ↔
      ∀ z : Z, (r : G) * (z.val : G) = (z.val : G) * r := by
  constructor
  · intro hr z
    have hz := congrArg (fun e : Equiv.Perm Z => ((e z).val : G)) hr
    change (r : G) * (z.val : G) * (r : G)⁻¹ = (z.val : G) at hz
    exact mul_inv_eq_iff_eq_mul.mp hz
  · intro hr
    apply Equiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change (r : G) * (z.val : G) * (r : G)⁻¹ = (z.val : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hr z)

private theorem characteristicAction_ker_invariant
    (Z : Subgroup (R ⊔ S : Subgroup G)) [Z.Characteristic]
    (a : MulAut R) (ha : a ∈ pairAutomizer S R) {r : R}
    (hr : r ∈ (characteristicAction S R Z).ker) :
    a r ∈ (characteristicAction S R Z).ker := by
  obtain ⟨b, hbS, hba⟩ := ha
  let bX : MulAut (R ⊔ S : Subgroup G) :=
    (b.subgroupMap (R ⊔ S)).trans (MulEquiv.subgroupCongr (pair_map_sup S R hbS hba))
  let bZ : MulAut Z := MulAut.characteristic Z bX
  apply (mem_characteristicAction_ker S R Z _).mpr
  intro z
  obtain ⟨w, rfl⟩ := bZ.surjective z
  have hw := (mem_characteristicAction_ker S R Z r).mp hr w
  have hbz : ((bZ w).val : G) = b (w.val : G) := rfl
  rw [hbz, hba]
  simpa only [map_mul] using congrArg b hw

private theorem characteristicAction_ker_ne_bot [Finite G]
    (Z : Subgroup (R ⊔ S : Subgroup G)) [Z.Characteristic]
    (hR : Nat.card R = 9) (hZ : Nat.card Z = 4) :
    (characteristicAction S R Z).ker ≠ ⊥ := by
  intro hbot
  have hd := card_dvd_of_injective (characteristicAction S R Z)
    ((MonoidHom.ker_eq_bot_iff _).mp hbot)
  rw [hR, Nat.card_perm, hZ] at hd
  norm_num at hd

private theorem characteristicAction_ker_ne_top
    (S R : Subgroup M23) (Z : Subgroup (R ⊔ S : Subgroup M23)) [Z.Characteristic]
    (hR : Nat.card R = 9) (hZ : Nat.card Z = 4) :
    (characteristicAction S R Z).ker ≠ ⊤ := by
  intro htop
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZ]; norm_num)
  let t : M23 := z.val.val
  have ht : orderOf t = 2 := by
    change orderOf (((R ⊔ S).subtype.comp Z.subtype) z) = 2
    rw [orderOf_injective ((R ⊔ S).subtype.comp Z.subtype)
      ((R ⊔ S).subtype_injective.comp Z.subtype_injective), hz]
  apply no_nine_centralizes_involution R hR ht
  intro r hr
  apply mem_centralizer_singleton_iff.mpr
  have hk : (⟨r, hr⟩ : R) ∈ (characteristicAction S R Z).ker := by rw [htop]; trivial
  exact (mem_characteristicAction_ker S R Z _).mp hk z

private theorem kernel_card_three [Finite G]
    (K : Subgroup R) (hR : Nat.card R = 9) (hKb : K ≠ ⊥) (hKt : K ≠ ⊤) :
    Nat.card K = 3 := by
  have hd : Nat.card K ∣ 3 ^ 2 := by simpa only [hR, Nat.reducePow] using K.card_subgroup_dvd_card
  obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  interval_cases k
  · exact (hKb (card_eq_one.mp hc)).elim
  · exact hc
  · exact (hKt ((K.card_eq_iff_eq_top).mp (hc.trans hR.symm))).elim

private theorem quotient_line_of_invariant [Finite G]
    (hPhi : frattini R = ⊥) (K : Subgroup R) (hKcard : Nat.card K = 3) (hKb : K ≠ ⊥) (hKt : K ≠ ⊤)
    (hK : ∀ a ∈ pairAutomizer S R, ∀ x ∈ K, a x ∈ K) :
    ∃ A : Subgroup (R ⧸ frattini R), Nat.card A = 3 ∧ A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ a ∈ pairAutomizer S R, ∀ x ∈ A, quotientAut (frattini R) a x ∈ A := by
  let q := QuotientGroup.mk' (frattini R)
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk', hPhi])
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  refine ⟨K.map q, (card_map_of_injective hqi).trans hKcard, ?_, ?_, ?_⟩
  · intro hb
    apply hKb
    apply map_injective hqi
    simpa only [Subgroup.map_bot] using hb
  · intro ht
    apply hKt
    apply map_injective hqi
    simpa only [map_top_of_surjective q hqs] using ht
  · intro a ha x hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [quotientAut_apply_mk]
    exact mem_map_of_mem q (hK a ha r hr)

/-- The characteristic four-group gives an actual invariant subgroup of order three. -/
public theorem m23_pair_invariant_line_of_characteristic_four
    {S : Sylow 2 M23} {R : Subgroup M23} (h : PairInput S R)
    (Z : Subgroup (R ⊔ (S : Subgroup M23) : Subgroup M23)) [Z.Characteristic]
    (hZ : Nat.card Z = 4) :
    ∃ A : Subgroup (R ⧸ frattini R), Nat.card A = 3 ∧ A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ a ∈ pairAutomizer (S : Subgroup M23) R, ∀ x ∈ A,
        quotientAut (frattini R) a x ∈ A := by
  obtain ⟨he, hR⟩ := m23_pair_elementary_nine h
  let _ := he
  let _ : Fact (IsPGroup 3 R) := ⟨IsElementaryAbelian.isPGroup 3 R⟩
  have hKb := characteristicAction_ker_ne_bot _ _ Z hR hZ
  have hKt := characteristicAction_ker_ne_top _ _ Z hR hZ
  exact quotient_line_of_invariant (S : Subgroup M23) R
    (frattini_eq_bot_of_isElementaryAbelian (p := 3)) _
    (kernel_card_three R _ hR hKb hKt) hKb hKt
    (fun a ha _ hr => characteristicAction_ker_invariant _ _ Z a ha hr)

/-- Conditional only on a characteristic subgroup of order four in the actual pair product. -/
public theorem m23_pairReducible_of_characteristic_four
    {S : Sylow 2 M23} {R : Subgroup M23} (h : PairInput S R)
    (Z : Subgroup (R ⊔ (S : Subgroup M23) : Subgroup M23)) [Z.Characteristic]
    (hZ : Nat.card Z = 4) : PairReducible (S : Subgroup M23) R := by
  obtain ⟨A, _, hAb, hAt, hA⟩ := m23_pair_invariant_line_of_characteristic_four h Z hZ
  exact pairReducible_of_invariant _ _ ⟨A, hAb, hAt, hA⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
