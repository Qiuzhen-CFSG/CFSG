module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalThreeSpace
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic

/-!
# The original elementary sixteen and its action kernel

The actual quotient U/⟨z⟩ has order eight, hence U has order sixteen.
Full action on the quotient carries an involution in Z_S to every nonzero
coset. The central kernel has exponent two, so every element of U squares
to one and U is elementary abelian.

The three-subgroup lemma then makes [V,U] centralize the quotient-action
kernel. The commutator and the central line generate Z_S, whose H-conjugate
closure is U. Thus the kernel C_H(U/⟨z⟩) is exactly C_H(U). This establishes
the four-space and kernel paragraphs of 6.2.11 without 6.2.12 or LocalAnalysis.
The L₂(4)-block and ambient A₇ contradiction remain to be proved.

Source: Aschbacher--Smith, 6.2.11, printed p.686, second and third paragraphs.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {L R : Subgroup G} {z : G}
  {κ : GroupClass} {P : Sylow 2 G} {M : Subgroup G} {n : ℕ}

/-- The original closure has order sixteen in the contrary order-four branch,
using its actual quotient by the marked central subgroup of order two. -/
theorem four_closure_card (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Nat.card (sourceClosure (P : Subgroup G) L R z) = 16 := by
  let := (reduced_space h hnatural hz ho hP).elementary
  have hd := (four_image_three_space h hnatural hz ho hP hplane hcard).2.1
  have hW : Nat.card (space (P : Subgroup G) L R z) = 8 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (space (P : Subgroup G) L R z))
    rw [Nat.card_zmod, hd] at hh
    exact hh
  let U := (sourceClosure (P : Subgroup G) L R z).subgroupOf (Centralizer z)
  have hUH : sourceClosure (P : Subgroup G) L R z ≤ Centralizer z := map_subtype_le _
  have hZH : zpowers z ≤ Centralizer z :=
    (zpowers_le.mpr hz).trans (h.ZS_le_T.trans hP)
  have hZcard : Nat.card (line z) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv).trans (by rw [Nat.card_zpowers, ho])
  have hZU : line z ≤ U := comap_mono
    ((zpowers_le.mpr hz).trans ((ZS_le_sourceClosure_intersection h hz).trans inf_le_left))
  have hc := ((line z).subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv, hZcard] at hc
  change 2 * (line z).relIndex U = Nat.card U at hc
  have hk : (projection z).ker = line z := QuotientGroup.ker_mk' _
  rw [← hk, relIndex_ker, closure_image, hW] at hc
  rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv] at hc
  exact hc.symm

/-- Full action on the quotient carries an involution in Z_S to every
nonzero coset. The central kernel also has exponent two, so the actual
closure U is elementary abelian, not merely its quotient. -/
theorem four_closure_elementary (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    IsElementaryAbelian 2 (sourceClosure (P : Subgroup G) L R z) := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let := h.ZS_elementary
  let U := sourceClosure (P : Subgroup G) L R z
  let f := linearAction (P : Subgroup G) L R z
  have hfull := four_image_full_linear h hnatural hz ho hP hplane hcard
  obtain ⟨x, hx, hxs, _⟩ := four_image_G3 h hnatural hz ho hP hplane hcard
  obtain ⟨s, hs, hsp⟩ := hxs
  change projection z s = x.toMul.val at hsp
  have hs2 : s ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := ZS (P : Subgroup G) L R) (s : G) hs)
  have hline2 (c : Centralizer z) (hc : c ∈ line z) : c ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := ZS (P : Subgroup G) L R)
      (c : G) ((zpowers_le.mpr hz) hc)
  have hpow (u : U) : u ^ 2 = 1 := by
    let uH : Centralizer z := ⟨u.val, map_subtype_le _ u.property⟩
    have huW : projection z uH ∈ space (P : Subgroup G) L R z := by
      rw [← closure_image]
      exact mem_map_of_mem _ u.property
    let w : space (P : Subgroup G) L R z := ⟨projection z uH, huW⟩
    by_cases hw : w = 1
    · have hu : projection z uH = 1 := congrArg Subtype.val hw
      have hc := hline2 uH ((QuotientGroup.eq_one_iff _).mp hu)
      exact Subtype.ext (congrArg (fun t : Centralizer z => (t : G)) hc)
    have hw0 : Additive.ofMul w ≠ 0 := hw
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hx hw0
    obtain ⟨b, hb⟩ := hfull.ge (mem_top g)
    have he : projection z (b * s * b⁻¹) = projection z uH := by
      have hh := congrArg (fun v : Additive (space (P : Subgroup G) L R z) => v.toMul.val) hg
      rw [← hb] at hh
      change projection z b * x.toMul.val * (projection z b)⁻¹ = projection z uH at hh
      rw [← hsp, ← map_inv, ← map_mul, ← map_mul] at hh
      exact hh
    let v := b * s * b⁻¹
    let c := uH / v
    have hc : c ∈ line z := (QuotientGroup.eq_iff_div_mem.mp he.symm)
    have hc2 := hline2 c hc
    have hv2 : v ^ 2 = 1 := by
      change (MulAut.conj b s) ^ 2 = 1
      rw [← map_pow, hs2, map_one]
    have hcomm : Commute c v := (mem_center_iff.mp (line_central z hc) v).symm
    have hu2 : uH ^ 2 = 1 := by
      rw [show uH = c * v by simp [c], hcomm.mul_pow, hc2, hv2, mul_one]
    exact Subtype.ext (congrArg (fun t : Centralizer z => (t : G)) hu2)
  have hi (u : U) : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hpow u)
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  intro a b
  have hh := mul_inv_rev a b
  simpa only [hi] using hh


/-- In the order-four branch the quotient-action kernel already centralizes
U itself. Three-subgroup commutation makes [V,U] centralize this kernel;
[V,U] together with the central line generates Z_S, whose H-closure is U.
This is the kernel comparison in 6.2.11, before 6.2.12. -/
theorem four_kernel_eq_centralizer (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    kernel (P : Subgroup G) L R z =
      Centralizer z ⊓ centralizer (sourceClosure (P : Subgroup G) L R z : Set G) := by
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  let N := kernel (P : Subgroup G) L R z
  let S := ZS (P : Subgroup G) L R
  let Z := zpowers z
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  have hNH : N ≤ Centralizer z := commutatorPreimage_le _ _ _
  have hZN : Z ≤ centralizer (N : Set G) :=
    le_centralizer_iff.mp (hNH.trans (centralizes_line z))
  have hZB : Z ≤ centralizer (B : Set G) :=
    le_centralizer_iff.mp ((layer_le_involution_centralizer h hz).trans (centralizes_line z))
  have hNU : ⁅N, U⁆ ≤ Z :=
    commutator_commutatorPreimage_le _ _ _ (normalizes_line z)
  have hNB : N ≤ normalizer (B : Set G) := by
    intro a ha
    exact hplane (local_action_kernel_normalizes_plane h hz ((mem_kernel _ _ _ _ a).mp ha).2)
  have hBN : ⁅B, N⁆ ≤ S := by
    have hh : ⁅B, N⁆ ≤ B ⊓ N := le_inf
      (le_normalizer_iff_commutator_le_left.mp hNB)
      (le_normalizer_iff_commutator_le_right.mp
        ((layer_le_involution_centralizer h hz).trans (kernel_normalized _ _ _ _)))
    exact hh.trans_eq (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.1
  have hBUC : ⁅B, U⁆ ≤ centralizer (N : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm U N]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hNU.trans hZB)
    · rw [commutator_comm N B]
      exact commutator_eq_bot_iff_le_centralizer.mpr
        ((hBN.trans ((ZS_le_sourceClosure_intersection h hz).trans inf_le_left)).trans U.le_centralizer)
  have hBS : ⁅B, U⁆ ≤ S := (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.2.2.1
  have hnot : ¬ ⁅B, U⁆ ≤ Z := by
    intro hh
    have hBK : B ≤ N := le_commutatorPreimage (layer_le_involution_centralizer h hz) hh
    have he := (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.1
    rw [inf_eq_left.mpr hBK] at he
    have hhcard := congrArg (fun X : Subgroup G => Nat.card X) he
    rw [hnatural.2.1.card, (h.natural_ZS_geometry hnatural).2.1] at hhcard
    contradiction
  have hjoin : Z ⊔ ⁅B, U⁆ = S := by
    have hle : Z ⊔ ⁅B, U⁆ ≤ S := sup_le (zpowers_le.mpr hz) hBS
    have hlt : Z < Z ⊔ ⁅B, U⁆ := lt_of_le_of_ne le_sup_left (by
      intro he
      exact hnot (le_sup_right.trans he.symm.le))
    have hc : 2 < Nat.card (Z ⊔ ⁅B, U⁆ : Subgroup G) := by
      by_contra hh
      have he : Z = Z ⊔ ⁅B, U⁆ := eq_of_le_of_card_ge le_sup_left
        (by simpa only [Z, Nat.card_zpowers, ho] using (not_lt.mp hh))
      exact hlt.ne he
    have hd : Nat.card (Z ⊔ ⁅B, U⁆ : Subgroup G) ∣ 4 :=
      (h.natural_ZS_geometry hnatural).2.1 ▸ card_dvd_of_le hle
    have he : Nat.card (Z ⊔ ⁅B, U⁆ : Subgroup G) = 4 := by
      have hh : Nat.card (Z ⊔ ⁅B, U⁆ : Subgroup G) ∣ 2 ^ 2 := hd
      obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hh
      interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
    exact eq_of_le_of_card_ge hle (by rw [he, (h.natural_ZS_geometry hnatural).2.1])
  have hSC : S ≤ centralizer (N : Set G) := hjoin ▸ sup_le hZN hBUC
  have hUC : U ≤ centralizer (N : Set G) := by
    let C := centralizer (N : Set G)
    let : (C.subgroupOf (Centralizer z)).Normal := normal_subgroupOf_of_le_normalizer
      ((kernel_normalized _ _ _ _).trans (normalizer_le_normalizer_centralizer N))
    have hh : normalClosure (S.subgroupOf (Centralizer z) : Set (Centralizer z)) ≤
        C.subgroupOf (Centralizer z) := normalClosure_le_normal (fun _ hs => hSC hs)
    rintro _ ⟨u, hu, rfl⟩
    exact hh hu
  apply le_antisymm (le_inf hNH (le_centralizer_iff.mp hUC))
  apply le_commutatorPreimage inf_le_left
  exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
