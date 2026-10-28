module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.ResidualLift
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift
public import Theory.GroupTheory.TINormalizerControl
public import Theory.GroupTheory.Commutator.FixedCoprimeLayer
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Lifting and centralizing the five-subgroup in the unitary branch

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 8.2.9, printed p.720 (PDF p.737).

We work intrinsically in the source H. Thus M below denotes the subgroup
H ∩ M of H, and every plus image uses precisely H → H/O₂(H). A subgroup D
of order five in the image of M lifts inside M with the same order. TI then
gives normalization of V; centralization of I⁺ and the actual two-conjugate
construction give normalization of I and P = O₂(I).

The rank-three U has 168 automorphisms, so X fixes it. Given [P,X] ≤ U,
two applications of the fixed-coprime-layer lemma show that X fixes P and I.
This also gives fixation of V ≤ I without a separate quotient action on V.
The second application uses [I,X] ≤ I ∩ O₂(H) ≤ O₂(I), not solvability of I.

The complete unitary exclusion is still to be assembled. The marked U₃(4)
placement must construct D of order five centralizing I⁺ inside the image
of M. The corrected cocode representation must supply [P,X] ≤ U, using
the actual quotient action and F₄ scalar structure described in
Normalizer/TensorDimension.lean. The final application of full 4.4.3 and
Remark 4.4.2, including exclusion of their exceptions, is also still needed.
The theorem below explicitly retains the two model premises and does not
claim Lemma 8.2.9 or assume the existence of a five-subgroup upstairs.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion
variable {H : Type*} [Group H] [Finite H]

/-- The rank-three binary U admits no nontrivial action of a group of order five. -/
theorem five_centralizes_eight (X U : Subgroup H) [IsElementaryAbelian 2 U]
    (hX : Nat.card X = 5) (hU : Nat.card U = 8)
    (hN : X ≤ normalizer (U : Set H)) : X ≤ centralizer (U : Set H) := by
  let f : X →* MulAut U := U.normalizerMonoidHom.comp (inclusion hN)
  have hd : Nat.card f.range ∣ 5 := hX ▸ card_range_dvd f
  have hcard : Nat.card f.range = 1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hh | hh
    · exact hh
    · have hh' := f.range.card_subgroup_dvd_card
      rw [hh, card_mulAut_of_elementary_eight U hU] at hh'
      norm_num at hh'
  have hbot : f.range = ⊥ := card_eq_one.mp hcard
  intro x hx u hu
  have hfx : f ⟨x, hx⟩ = 1 := mem_bot.mp (hbot ▸ (show f ⟨x, hx⟩ ∈ f.range from ⟨⟨x, hx⟩, rfl⟩))
  have he := congrArg (fun a : MulAut U => (a ⟨u, hu⟩ : H)) hfx
  change x * u * x⁻¹ = u at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm


/-- The literal lift can be chosen inside the indicated subgroup of H. -/
theorem lift_five_subgroup (M : Subgroup H)
    (D : Subgroup (H ⧸ pCore 2 H)) (hD : Nat.card D = 5)
    (hDM : D ≤ M.map (QuotientGroup.mk' (pCore 2 H))) :
    ∃ X : Subgroup H, X ≤ M ∧ Nat.card X = 5 ∧
      X.map (QuotientGroup.mk' (pCore 2 H)) = D := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let K := M ⊓ D.comap q
  let f : K →* D := (q.comp K.subtype).codRestrict D (fun x => x.property.2)
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨m, hm, he⟩ := hDM d.property
    exact ⟨⟨m, hm, by change q m ∈ D; rw [he]; exact d.property⟩, Subtype.ext he⟩
  have hk : IsPGroup 2 f.ker := by
    have hb : f.ker.map K.subtype ≤ pCore 2 H := by
      rintro _ ⟨x, hx, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hx
    exact (pCore_isPGroup.to_le hb).of_equiv
      (f.ker.equivMapOfInjective K.subtype K.subtype_injective).symm
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card f.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime f hf hcop
    (⊤ : Subgroup D) ((IsPGroup.of_card (p := 5) (n := 1) (by simpa using hD)).to_subgroup ⊤)
  refine ⟨A.map K.subtype, (map_subtype_le A).trans inf_le_left, ?_, ?_⟩
  · rw [card_map_of_injective K.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).toEquiv]
    exact hD
  · have hh := congrArg (Subgroup.map D.subtype) hA
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    have hc : D.subtype.comp f = q.comp K.subtype := by ext; rfl
    rw [hc] at hh
    simpa only [map_map] using hh

/-- Quotient centralization and normalization of V give normalization of its
actual two-conjugate subgroup. The two-core normalizes both conjugates. -/
theorem normalizes_pair_of_quotient_centralization
    (T : Sylow 2 H) (V I X : Subgroup H) (h : H)
    (hh : h ∈ I) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hXV : X ≤ normalizer (V : Set H))
    (hXC : X.map (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))) :
    X ≤ normalizer (I : Set H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hQI : pCore 2 H ≤ normalizer (I : Set H) := by
    rw [← hgen]
    exact twoCore_normalizes_twoConjugate T V h hTV
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj x).injective])
  rw [← hgen, Subgroup.map_sup]
  apply sup_le
  · rw [mem_normalizer_iff_map_conj_eq.mp (hXV hx)]
    exact le_sup_left
  · rw [hgen]
    rintro _ ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    let d := x * h⁻¹ * x⁻¹ * h
    have hd : d ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q d = 1
      have hc := hXC (mem_map_of_mem q hx) (q h⁻¹) (mem_map_of_mem q (I.inv_mem hh))
      rw [map_inv] at hc
      dsimp only [d]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      simp [mul_assoc]
    have hxi : x * v * x⁻¹ ∈ V := (mem_normalizer_iff.mp (hXV hx) v).mp hv
    have hwi : h⁻¹ * (x * v * x⁻¹) * h ∈ I := by
      apply hgen ▸ mem_sup_right
      exact ⟨x * v * x⁻¹, hxi, by simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]⟩
    have hf := (mem_normalizer_iff.mp (hQI hd) _).mp hwi
    convert hf using 1
    dsimp [d, MulAut.conj_apply]
    group


omit [Finite H] in
/-- The commutators lie in I ∩ O₂(H), which is a normal two-subgroup
of I and hence lies in its intrinsic two-core. -/
theorem pair_commutator_le_core (I X : Subgroup H)
    (hXI : X ≤ normalizer (I : Set H))
    (hXC : X.map (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))) :
    ⁅I, X⁆ ≤ I.pCoreIn 2 := by
  have hbound : ⁅I, X⁆ ≤ I ⊓ pCore 2 H := by
    apply le_inf (le_normalizer_iff_commutator_le_left.mp hXI)
    let q := QuotientGroup.mk' (pCore 2 H)
    apply commutator_le.mpr
    intro i hi x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅i, x⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hXC (mem_map_of_mem q hx) (q i) (mem_map_of_mem q hi))
  apply hbound.trans
  apply le_pCoreIn_of_normalizes (pCore_isPGroup.to_le inf_le_right) inf_le_left
  exact (le_inf I.le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf


/-- Group-theoretic consumer of the marked unitary and tensor calculations.
Here M denotes the source H ∩ M inside H. The subgroup D belongs to the
literal quotient H/O₂(H). The remaining layer premise is to be supplied by
the corrected marked cocode representation, not the printed binary tensor.
No existence of an order-five subgroup in H is assumed. -/
theorem exists_five_centralizing_pair
    (T : Sylow 2 H) (M V I U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (h : H) (hh : h ∈ I)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hUV : U ≤ V) (hU : Nat.card U = 8)
    (D : Subgroup (H ⧸ pCore 2 H)) (hD : Nat.card D = 5)
    (hDM : D ≤ M.map (QuotientGroup.mk' (pCore 2 H)))
    (hDC : D ≤ centralizer
      (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)))
    (hlayer : ∀ X : Subgroup H, X ≤ M → Nat.card X = 5 →
      X ≤ normalizer (I : Set H) →
      X.map (QuotientGroup.mk' (pCore 2 H)) ≤ centralizer
        (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) →
      ⁅I.pCoreIn 2, X⁆ ≤ U) :
    ∃ X : Subgroup H, X ≤ M ∧ Nat.card X = 5 ∧
      X.map (QuotientGroup.mk' (pCore 2 H)) = D ∧
      X ≤ normalizer (V : Set H) ∧
      X ≤ normalizer (I.pCoreIn 2 : Set H) ∧
      X ≤ centralizer (U : Set H) ∧ X ≤ centralizer (I : Set H) := by
  obtain ⟨X, hXM, hX, hXD⟩ := lift_five_subgroup M D hD hDM
  have hXC : X.map (QuotientGroup.mk' (pCore 2 H)) ≤ centralizer
      (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := hXD ▸ hDC
  have hUne : U ≠ ⊥ := by
    intro hb
    have hc := card_eq_one.mpr hb
    rw [hU] at hc
    norm_num at hc
  have hXV : X ≤ normalizer (V : Set H) :=
    (le_inf hXM le_normalizer_of_normal).trans
      (inf_normalizer_le_of_trivial_intersections hTI hUne hUV)
  have hXI := normalizes_pair_of_quotient_centralization T V I X h hh hTV hgen hXV hXC
  have hXP := hXI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hXU := five_centralizes_eight X U hX hU le_normalizer_of_normal
  have hcop : Nat.Coprime 2 (Nat.card X) := by rw [hX]; decide
  have hXPfix := le_centralizer_of_fixed_coprime_prime_layer X (I.pCoreIn 2) U
    (IsElementaryAbelian.isPGroup 2 U) hcop hXU (hlayer X hXM hX hXI hXC)
  have hXIfix := le_centralizer_of_fixed_coprime_prime_layer X I (I.pCoreIn 2)
    (isPGroup_pCoreIn 2 I) hcop hXPfix (pair_commutator_le_core I X hXI hXC)
  exact ⟨X, hXM, hX, hXD, hXV, hXP, hXU, hXIfix⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion
