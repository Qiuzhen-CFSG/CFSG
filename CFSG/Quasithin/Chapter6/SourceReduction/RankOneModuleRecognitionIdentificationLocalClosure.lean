module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationContracts
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.ReducedNormal.IrreducibleClosure
public import Theory.GroupTheory.PCoreSurjective

/-!
# The actual plane closure in the involution centralizer

The source plane S = Z_S has order four and contains the central line
Z = ⟨z⟩ of H = C_G(z). Thus S/Z has order two and is irreducible under
the Sylow overgroup. The characteristic-two irreducible-closure theorem
(G.2.2) puts its normal closure in the center of the quotient two-core.
Lifting through the literal central quotient gives U ≤ O₂(H) and
[U,O₂(H)] ≤ Z for the original sourceClosure.

In particular U normalizes S. Source 6.2.1 then makes it normalize the
layer, and normality of U in H gives [V,U] ≤ V ∩ U. These are precisely
the closure clauses in LocalAnalysis, constructed without that record.

Source: Aschbacher--Smith, 6.2.10(1,5), printed p.685, using G.2.2, p.332.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem interval_of_cards {Z S E : Subgroup G}
    (hZ : Nat.card Z = 2) (hS : Nat.card S = 4) (hZE : Z ≤ E) (hES : E ≤ S) :
    E = Z ∨ E = S := by
  have hlow : 2 ≤ Nat.card E := hZ ▸ card_le_of_le hZE
  have hdvd : Nat.card E ∣ 2 ^ 2 := by
    simpa only [hS, Nat.reducePow] using card_dvd_of_le hES
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hec : Nat.card E = 2 ∨ Nat.card E = 4 := by
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  rcases hec with hec | hec
  · exact Or.inl (eq_of_le_of_card_ge hZE (by omega)).symm
  · exact Or.inr (eq_of_le_of_card_ge hES (by omega))

private theorem reduced_closure_of_plane_mod_line (S Z : Subgroup G) [Z.Normal]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hSe : IsElementaryAbelian 2 S) (hZ : Nat.card Z = 2) (hS : Nat.card S = 4)
    (hZS : Z ≤ S) (T : Sylow 2 G) (hST : S ≤ (T : Subgroup G))
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G)) :
    IsPReduced 2 (normalClosure (S.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))) := by
  let q := QuotientGroup.mk' Z
  have hk : q.ker = Z := QuotientGroup.ker_mk' Z
  apply isPReduced_normalClosure_image_of_irreducible q (QuotientGroup.mk'_surjective Z)
    S (T : Subgroup G) T hchar hSe
  · rwa [hk]
  · rw [hk]
    intro he
    rw [he, hS] at hZ
    contradiction
  · exact hST
  · exact le_rfl
  · exact hTS
  · intro E hZE hES _
    rw [hk] at hZE ⊢
    exact interval_of_cards hZ hS hZE hES

-- The intrinsic closure and its literal commutators.
private theorem core_closure_of_plane_mod_line (S Z : Subgroup G) [Z.Normal]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hSe : IsElementaryAbelian 2 S) (hZ : Nat.card Z = 2) (hS : Nat.card S = 4)
    (hZS : Z ≤ S) (T : Sylow 2 G) (hST : S ≤ (T : Subgroup G))
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G)) :
    normalClosure (S : Set G) ≤ pCore 2 G ∧
      ⁅normalClosure (S : Set G), pCore 2 G⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  have hk : q.ker = Z := QuotientGroup.ker_mk' Z
  have hq := QuotientGroup.mk'_surjective Z
  have hp : IsPGroup 2 q.ker := by
    rw [hk]
    exact IsPGroup.of_card (n := 1) (by simpa using hZ)
  have hpre : (pCore 2 (G ⧸ Z)).comap q = pCore 2 G :=
    q.comap_pCore_of_ker_isPGroup hq hp
  have hmap : (normalClosure (S : Set G)).map q =
      normalClosure (S.map q : Set (G ⧸ Z)) := by
    rw [coe_map, map_normalClosure _ q hq]
  have hr := reduced_closure_of_plane_mod_line S Z hchar hSe hZ hS hZS T hST hTS
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    apply map_le_iff_le_comap.mp
    rw [hmap]
    exact hr.le_pCore
  · apply commutator_le.mpr
    intro u hu v hv
    have hu' : q u ∈ normalClosure (S.map q : Set (G ⧸ Z)) :=
      hmap ▸ mem_map_of_mem q hu
    have hv' : q v ∈ pCore 2 (G ⧸ Z) := by
      change v ∈ (pCore 2 (G ⧸ Z)).comap q
      rwa [hpre]
    have hc := hr.le_centralizer_pCore hu' (q v) hv'
    have he : q ⁅u, v⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc.symm
    exact (QuotientGroup.eq_one_iff _).mp he

variable {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Source 6.2.10(1), on the original normal closure and actual two-core. -/
theorem local_closure_core
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    sourceClosure (T : Subgroup G) L R z ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      ⁅sourceClosure (T : Subgroup G) L R z, (centralizer ({z} : Set G)).pCoreIn 2⁆ ≤
        zpowers z := by
  let H := centralizer ({z} : Set G)
  let S := (ZS (T : Subgroup G) L R).subgroupOf H
  let Z := (zpowers z).subgroupOf H
  have hSH : ZS (T : Subgroup G) L R ≤ H := h.ZS_le_T.trans hT
  have hZH : zpowers z ≤ H := (zpowers_le.mpr hz).trans hSH
  have hZcentral : Z ≤ center H := by
    intro x hx
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    have hc : zpowers z ≤ centralizer ({(a : G)} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp a.property).symm)
    exact (mem_centralizer_singleton_iff.mp (hc hx)).symm
  let : Z.Normal := ⟨by
    intro x hx a
    have hc := mem_center_iff.mp (hZcentral hx) a
    simpa only [hc, mul_inv_cancel_right] using hx⟩
  have hSe : IsElementaryAbelian 2 S := by
    let := h.ZS_elementary
    exact IsElementaryAbelian.subgroupOf hSH
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv, Nat.card_zpowers, ho]
  have hScard : Nat.card S = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv).trans (h.natural_ZS_geometry hnatural).2.1
  have hZS : Z ≤ S := comap_mono (zpowers_le.mpr hz)
  let P := T.subtype hT
  have hSP : S ≤ (P : Subgroup H) := comap_mono h.ZS_le_T
  have hPS : (P : Subgroup H) ≤ normalizer (S : Set H) := by
    rw [← subgroupOf_normalizer_eq hSH]
    exact comap_mono h.sylow_normalizes_ZS
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer ho) hT)
  obtain ⟨hle, hcomm⟩ := core_closure_of_plane_mod_line S Z hchar hSe hZcard hScard hZS P hSP hPS
  refine ⟨map_mono hle, ?_⟩
  have hm := map_mono (f := H.subtype) hcomm
  rw [map_commutator, map_subgroupOf_eq_of_le hZH] at hm
  exact hm

/-- Every element of the two-core centralizes the literal U/⟨z⟩ action. -/
theorem local_core_action_kernel
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    {x : G} (hx : x ∈ (centralizer ({z} : Set G)).pCoreIn 2) :
    ∀ u ∈ sourceClosure (T : Subgroup G) L R z, ⁅x, u⁆ ∈ zpowers z := by
  have hc := (local_closure_core h hnatural hz ho hT).2
  rw [commutator_comm] at hc
  exact fun u hu => hc (commutator_mem_commutator hx hu)

/-- The kernel of the literal quotient action normalizes the source plane. -/
theorem local_action_kernel_normalizes_plane
    (h : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) {x : G}
    (hx : ∀ u ∈ sourceClosure (T : Subgroup G) L R z, ⁅x, u⁆ ∈ zpowers z) :
    x ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := by
  -- Finiteness converts the forward conjugation containment into equality.
  have hle : (ZS (T : Subgroup G) L R).map (MulAut.conj x).toMonoidHom ≤
      ZS (T : Subgroup G) L R := by
    rintro _ ⟨v, hv, rfl⟩
    have hu := (ZS_le_sourceClosure_intersection h hz hv).1
    have hc := (zpowers_le.mpr hz) (hx v hu)
    have hh := (ZS (T : Subgroup G) L R).mul_mem hc hv
    simpa only [commutatorElement_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hh
  exact mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective]))

/-- Source 6.2.10(5), obtained from the central quotient and 6.2.1. -/
theorem local_layer_closure_commutator
    (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G)) :
    ⁅layer L R, sourceClosure (T : Subgroup G) L R z⁆ ≤
      layer L R ⊓ sourceClosure (T : Subgroup G) L R z := by
  have hUN : sourceClosure (T : Subgroup G) L R z ≤ normalizer (layer L R : Set G) := by
    intro u hu
    exact hplane (local_action_kernel_normalizes_plane h hz
      (local_core_action_kernel h hnatural hz ho hT ((local_closure_core h hnatural hz ho hT).1 hu)))
  have hHU : centralizer ({z} : Set G) ≤ normalizer (sourceClosure (T : Subgroup G) L R z : Set G) := by
    have hh := (M22Recognition.CentralizerExtension.sourceEight
      ((ZS (T : Subgroup G) L R).subgroupOf (centralizer ({z} : Set G)))).le_normalizer_map
        (centralizer ({z} : Set G)).subtype
    simpa only [sourceClosure, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hUN)
    (le_normalizer_iff_commutator_le_right.mp ((layer_le_involution_centralizer h hz).trans hHU))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
