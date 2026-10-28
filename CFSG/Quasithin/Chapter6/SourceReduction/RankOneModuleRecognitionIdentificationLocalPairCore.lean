module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairBounds
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion

/-!
# The quaternion pair core in source 6.2.6

Let two conjugates of the natural layer have index-two normalizer intersections,
and suppose their join is not a two-group. The order-two centralizer kernels
force the mutual commutator of those intersections to be their order-two
intersection. Their product has order 32 and is normalized by both layers.
Its center is precisely the intersection; its central quotient is elementary
abelian. An elementary subgroup of order eight then gives the actual pair
of quaternion factors.

This constructs the source subgroup Q and its quaternion structure. Identifying
Q with the generated pair's two-core and identifying the quotient remain with
the local-analysis assembly owner, qt-d-1222-recognition-local-analysis.
Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem pair_half_card {A B : Subgroup G}
    (hle : A ≤ B) (hc : Nat.card B = 16) (hi : A.relIndex B = 2) :
    Nat.card A = 8 := by
  have hh := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hh
  change Nat.card A * A.relIndex B = Nat.card B at hh
  rw [hi, hc] at hh
  omega

/-- The product of the two index-two normalizer intersections in source 6.2.6. -/
@[expose] def localPairCore (B A : Subgroup G) : Subgroup G :=
  (B ⊓ normalizer (A : Set G)) ⊔ (A ⊓ normalizer (B : Set G))

private theorem pair_core_geometry (B A : Subgroup G)
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 A]
    (hB : Nat.card B = 16) (hA : Nat.card A = 16)
    (hleft : (B ⊓ normalizer (A : Set G)).relIndex B = 2)
    (hright : (A ⊓ normalizer (B : Set G)).relIndex A = 2)
    (hCB : Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) = 2)
    (hCA : Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) = 2)
    (hlargeB : centralizer ((B ⊓ normalizer (A : Set G) : Subgroup G) : Set G) = centralizer (B : Set G))
    (hlargeA : centralizer ((A ⊓ normalizer (B : Set G) : Subgroup G) : Set G) = centralizer (A : Set G)) :
    let Q := localPairCore B A
    Nat.card (B ⊓ A : Subgroup G) = 2 ∧
    ⁅B ⊓ normalizer (A : Set G), A ⊓ normalizer (B : Set G)⁆ = B ⊓ A ∧
    Nat.card Q = 32 ∧ (B ⊔ A) ≤ normalizer (Q : Set G) ∧
    (center Q).map Q.subtype = B ⊓ A := by
  let U := B ⊓ normalizer (A : Set G)
  let F := A ⊓ normalizer (B : Set G)
  let I := B ⊓ A
  let Q := localPairCore B A
  have hU : Nat.card U = 8 := pair_half_card inf_le_left hB hleft
  have hF : Nat.card F = 8 := pair_half_card inf_le_left hA hright
  have hIU : I ≤ U := le_inf inf_le_left (inf_le_right.trans A.le_normalizer)
  have hIF : I ≤ F := le_inf inf_le_right (inf_le_left.trans B.le_normalizer)
  have hUF : U ⊓ F = I := le_antisymm (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left)) (le_inf hIU hIF)
  have hcomm : ⁅U, F⁆ ≤ I := le_inf
    ((commutator_mono (show U ≤ B from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (show F ≤ normalizer (B : Set G) from inf_le_right)))
    ((commutator_mono le_rfl (show F ≤ A from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (show U ≤ normalizer (A : Set G) from inf_le_right)))
  have hnon : ⁅U, F⁆ ≠ ⊥ := by
    intro he
    have hc : U ≤ centralizer (A : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp he).trans_eq hlargeA
    have hh := card_le_of_le (le_inf (show U ≤ B from inf_le_left) hc)
    rw [hU, hCB] at hh
    omega
  have hIC : I ≤ B ⊓ centralizer (A : Set G) := le_inf inf_le_left
    (inf_le_right.trans A.le_centralizer)
  have hIcard : Nat.card I = 2 := by
    have hlo : 1 < Nat.card I :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr (fun he => hnon (bot_unique (hcomm.trans_eq he)))
    have hhi := card_le_of_le hIC
    rw [hCB] at hhi
    omega
  have hcomm_eq : ⁅U, F⁆ = I := by
    have hlo : 1 < Nat.card (⁅U, F⁆ : Subgroup G) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hnon
    exact eq_of_le_of_card_ge hcomm (by rw [hIcard]; omega)
  have hCBI : B ⊓ centralizer (A : Set G) = I :=
    (eq_of_le_of_card_ge hIC (by rw [hCB, hIcard])).symm
  have hCAI : A ⊓ centralizer (B : Set G) = I := by
    apply (eq_of_le_of_card_ge (le_inf (show I ≤ A from inf_le_right)
      (inf_le_left.trans B.le_centralizer)) ?_).symm
    rw [hCA, hIcard]
  have hFU : F ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hIU)
  have hUFN : U ≤ normalizer (F : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans hIF)
  have hcQ : Nat.card Q = 32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U F hFU
    rw [hU, hF, hUF, hIcard] at hh
    change 64 = 2 * Nat.card Q at hh
    omega
  have hBU : B ≤ normalizer (U : Set G) :=
    (B.le_centralizer.trans (centralizer_le (show U ≤ B from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hAF : A ≤ normalizer (F : Set G) :=
    (A.le_centralizer.trans (centralizer_le (show F ≤ A from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hBF : ⁅B, F⁆ ≤ U := commutator_le_of_normalized_index_two B U F inf_le_left
    hleft inf_le_right hFU
  have hAU : ⁅A, U⁆ ≤ F := commutator_le_of_normalized_index_two A F U inf_le_left
    hright inf_le_right hUFN
  have hnorm (X D E : Subgroup G) (hXD : X ≤ normalizer (D : Set G))
      (hc : ⁅X, E⁆ ≤ D) : X ≤ normalizer ((D ⊔ E : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    have hle : D ⊔ E ≤ (D ⊔ E).comap (MulAut.conj x).toMonoidHom := by
      apply sup_le
      · intro d hd
        exact mem_sup_left ((mem_normalizer_iff.mp (hXD hx) d).mp hd)
      · intro e he
        have hh := (D ⊔ E).mul_mem (mem_sup_left (hc (commutator_mem_commutator hx he)))
          (mem_sup_right he)
        change x * e * x⁻¹ ∈ D ⊔ E
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    exact hle hy
  have hQN : B ⊔ A ≤ normalizer (Q : Set G) := by
    apply sup_le
    · exact hnorm B U F hBU hBF
    · change A ≤ normalizer ((U ⊔ F : Subgroup G) : Set G)
      rw [sup_comm]
      exact hnorm A F U hAF hAU
  have hIQ : I ≤ Q := hIU.trans le_sup_left
  have hQI : (center Q).map Q.subtype = I := by
    rw [map_center_subtype_eq_inf_centralizer]
    apply le_antisymm
    · intro x hx
      have hxUF : x ∈ U ⊔ F := hx.1
      have hxset : x ∈ (U : Set G) * (F : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left U F hFU]
        exact hxUF
      obtain ⟨u, hu, f, hf, rfl⟩ := hxset
      have hfc : f ∈ centralizer (U : Set G) := by
        have huc : u ∈ centralizer (U : Set G) :=
          (B.le_centralizer.trans (centralizer_le (show U ≤ B from inf_le_left))) hu.1
        have hxc : u * f ∈ centralizer (U : Set G) :=
          centralizer_le (show U ≤ Q from le_sup_left) hx.2
        simpa using (centralizer (U : Set G)).mul_mem
          ((centralizer (U : Set G)).inv_mem huc) hxc
      rw [hlargeB] at hfc
      have hfI : f ∈ I := hCAI ▸ (show f ∈ A ⊓ centralizer (B : Set G) from ⟨hf.1, hfc⟩)
      have hxB : u * f ∈ B := B.mul_mem hu.1 hfI.1
      have hxc : u * f ∈ centralizer (A : Set G) := by
        rw [← hlargeA]
        exact centralizer_le (show F ≤ Q from le_sup_right) hx.2
      exact hCBI ▸ (show u * f ∈ B ⊓ centralizer (A : Set G) from ⟨hxB, hxc⟩)
    · refine le_inf hIQ ?_
      apply le_centralizer_iff.mp
      exact sup_le ((show U ≤ B from inf_le_left).trans
        (B.le_centralizer.trans (centralizer_le (show I ≤ B from inf_le_left))))
        ((show F ≤ A from inf_le_left).trans
          (A.le_centralizer.trans (centralizer_le (show I ≤ A from inf_le_right))))
  exact ⟨hIcard, hcomm_eq, hcQ, hQN, hQI⟩


private theorem pair_core_quaternion (B A : Subgroup G)
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 A]
    (hU : Nat.card (B ⊓ normalizer (A : Set G) : Subgroup G) = 8)
    (hI : Nat.card (B ⊓ A : Subgroup G) = 2)
    (hcomm : ⁅B ⊓ normalizer (A : Set G), A ⊓ normalizer (B : Set G)⁆ = B ⊓ A)
    (hQ : Nat.card (localPairCore B A) = 32)
    (hcenter : (center (localPairCore B A)).map (localPairCore B A).subtype = B ⊓ A) :
    Nonempty (QuaternionCentralProductData (localPairCore B A)) := by
  let U := B ⊓ normalizer (A : Set G)
  let F := A ⊓ normalizer (B : Set G)
  let Q := localPairCore B A
  have hIU : B ⊓ A ≤ U := le_inf inf_le_left (inf_le_right.trans A.le_normalizer)
  have hFU : F ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.le.trans hIU)
  have hZcard : Nat.card (center Q) = 2 := by
    rw [← card_map_of_injective Q.subtype_injective, hcenter, hI]
  have hsquare (x : Q) : x ^ 2 ∈ center Q := by
    have hx : (x : G) ∈ (U : Set G) * (F : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U F hFU]
      exact x.property
    obtain ⟨u, hu, f, hf, he⟩ := hx
    have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu.1
    have hf2 : f ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian f hf.1
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hf2)
    have hxI : ((x ^ 2 : Q) : G) ∈ B ⊓ A := by
      have hh := hcomm.le (commutator_mem_commutator hu hf)
      change (x : G) ^ 2 ∈ B ⊓ A
      rw [← he]
      simpa only [commutatorElement_def, hui, hfi, pow_two, mul_assoc] using hh
    rw [← hcenter] at hxI
    obtain ⟨z, hz, hez⟩ := hxI
    have hez' : z = x ^ 2 := Subtype.ext hez
    exact hez' ▸ hz
  have hpow (x : Q ⧸ center Q) : x ^ 2 = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
    rw [← map_pow]
    change ((x ^ 2 : Q) : Q ⧸ center Q) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hsquare x)
  let : IsMulCommutative (Q ⧸ center Q) := ⟨⟨fun a b =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩⟩
  let : IsExtraspecial 2 Q := {
    center_order_p := hZcard
    quotient_elementary_abelian := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
      intro he
      have hh := hZcard
      rw [he, card_top] at hh
      change Nat.card Q = 32 at hQ
      omega) }
  let E := U.subgroupOf Q
  have hUQ : U ≤ Q := le_sup_left
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ B from inf_le_left)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hUQ
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hUQ).mpr
    (sup_le U.le_normalizer hFU)
  have hEc : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv).trans hU
  have hZE : center Q ≤ E := by
    intro x hx
    exact hIU (hcenter ▸ mem_map_of_mem Q.subtype hx)
  obtain ⟨B₀, A₀, hB₀, hA₀, hgen, hi, hc⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary hQ E hEc hZE
  exact ⟨⟨B₀, A₀, hB₀, hA₀, hi, hc, hgen⟩⟩


/-- Source 6.2.6: construct the normalized quaternion central product inside
the non-two generated pair, with its literal center and commutator. -/
theorem local_non_two_pair_quaternion_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let Q := localPairCore B A
    Nat.card (B ⊓ A : Subgroup G) = 2 ∧
      ⁅B ⊓ normalizer (A : Set G), A ⊓ normalizer (B : Set G)⁆ = B ⊓ A ∧
      Nat.card Q = 32 ∧ B ⊔ A ≤ normalizer (Q : Set G) ∧
      (center Q).map Q.subtype = B ⊓ A ∧
      Nonempty (QuaternionCentralProductData Q) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hCA := local_pair_normalizer_kernel_card_two h hnatural hE g hright hnon
  have hback : ¬ IsPGroup 2 (B ⊔ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) := by
    intro hp
    have hh := hp.map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_sup, show (B.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = B from by
        simpa using fusion_map_conj_inverse B g⁻¹, sup_comm] at hh
    exact hnon hh
  have hi : (B.map (MulAut.conj g⁻¹).toMonoidHom ⊓ normalizer (B : Set G)).relIndex
      (B.map (MulAut.conj g⁻¹).toMonoidHom) = 2 := by
    have he := relIndex_map_map_of_injective
      (f := (MulAut.conj g⁻¹).toMonoidHom)
      (B ⊓ normalizer (A : Set G)) B (MulAut.conj g⁻¹).injective
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, map_equiv_normalizer_eq,
      fusion_map_conj_inverse] at he
    exact he.trans hleft
  have hCB' := local_pair_normalizer_kernel_card_two h hnatural hE g⁻¹ hi hback
  have hCB : Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) = 2 := by
    have hm : Nat.card ((B ⊓ centralizer (A : Set G)).map (MulAut.conj g⁻¹).toMonoidHom) =
        Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) :=
      card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Theory.Quasithin.map_centralizer, fusion_map_conj_inverse] at hm
    exact hm.symm.trans hCB'
  have hBc : Nat.card B = 16 := hnatural.2.1.card
  have hAc : Nat.card A = 16 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hBc
  have hU := pair_half_card inf_le_left hBc hleft
  have hF := pair_half_card inf_le_left hAc hright
  obtain ⟨hI, hc, hQ, hQN, hZ⟩ := pair_core_geometry B A hBc hAc hleft hright hCB hCA
    (local_large_subgroup_centralizer h hnatural hE inf_le_left (by rw [hU]))
    (local_conjugate_large_subgroup_centralizer h hnatural hE g inf_le_left (by rw [hF]))
  exact ⟨hI, hc, hQ, hQN, hZ, pair_core_quaternion B A hU hI hc hQ hZ⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
