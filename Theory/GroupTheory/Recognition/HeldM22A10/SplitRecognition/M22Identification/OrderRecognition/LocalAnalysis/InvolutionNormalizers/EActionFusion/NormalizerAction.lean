module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.SylowTransport
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# The faithful quotient action on Janko's elementary sixteen

The centralizer of the marked involution normalizes E and is exactly its
point stabilizer in N(E). Self-centralization of E identifies N(E)/E with
the actual image in Aut(E). Orbit-stabilizer gives |N(E)/E| = 24 times the
orbit size; the orbit lies among the fifteen nonidentity elements. The
Sylow index makes this size odd, and |GL(4,2)| bounds the possible orders.
An actual A6 quotient equivalence therefore also supplies transitivity.

These are reductions for the source argument, not an identification of the
quotient or an unconditional construction of ENormalizerAction.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, pp.5–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
/-- The whole marked centralizer normalizes its binary kernel. -/
public theorem centralizer_le_normalizer_E : D.centralizer ≤ normalizer (E D k : Set G) := by
  have hrange : (into D k).range = D.centralizer := by
    rw [into, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr k.surjective,
      ← MonoidHom.range_eq_map, D.centralizer.range_subtype]
  rw [← hrange, ← modelE_map D k]
  let : modelE.Normal := by unfold modelE; infer_instance
  have h := le_normalizer_map (into D k) (H := modelE)
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using h

/-- The actual automizer quotient, with E restricted to its normalizer. -/
public abbrev eNormalizerQuotient := normalizer (E D k : Set G) ⧸
  (E D k).subgroupOf (normalizer (E D k : Set G))

/-- Conjugation identifies the quotient with its faithful automorphism image. -/
public noncomputable def eNormalizerQuotientEquivAction : eNormalizerQuotient D k ≃*
    (E D k).normalizerMonoidHom.range :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [normalizerMonoidHom_ker, E_centralizer D k])).symm.trans
      (QuotientGroup.quotientKerEquivRange _)

/-- The quotient order divides the order of GL(4,2). -/
public theorem eNormalizerQuotient_card_dvd : Nat.card (eNormalizerQuotient D k) ∣ 20160 := by
  let := E_elementary D k
  have h := (E D k).normalizerMonoidHom.range.card_subgroup_dvd_card
  rw [← Nat.card_congr (eNormalizerQuotientEquivAction D k).toEquiv] at h
  have hc : Nat.card (MulAut (E D k)) = 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 4
      (by simpa using E_card D k)]
    decide +kernel
  rwa [hc] at h

/-- The marked involution as a point of E. -/
@[expose] public def eNormalizerPoint : E D k := ⟨D.z, by
  rw [← into_z_zero D k, ← modelE_map D k]
  exact mem_map_of_mem _ (z_mem_modelE 0)⟩

public theorem eNormalizerPoint_ne_one : eNormalizerPoint D k ≠ 1 := fun h => D.z_ne_one (congrArg Subtype.val h)

/-- Its stabilizer is exactly the original ambient centralizer. -/
public theorem eNormalizerPoint_stabilizer :
    MulAction.stabilizer (normalizer (E D k : Set G)) (eNormalizerPoint D k) =
      D.centralizer.subgroupOf (normalizer (E D k : Set G)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change (⟨(g : G) * D.z * (g : G)⁻¹, _⟩ : E D k) = eNormalizerPoint D k ↔
    (g : G) ∈ D.centralizer
  rw [Subtype.ext_iff]
  change (g : G) * D.z * (g : G)⁻¹ = D.z ↔ _
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

public theorem eNormalizerPoint_stabilizer_card :
    Nat.card (MulAction.stabilizer (normalizer (E D k : Set G)) (eNormalizerPoint D k)) = 384 := by
  rw [eNormalizerPoint_stabilizer, Nat.card_congr
    (subgroupOfEquivOfLe (centralizer_le_normalizer_E D k)).toEquiv, D.centralizer_card]

/-- The orbit size is precisely the index of the S4 point stabilizer. -/
public theorem eNormalizerQuotient_card : Nat.card (eNormalizerQuotient D k) =
    24 * (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k)).ncard := by
  have h := (MulAction.stabilizer (normalizer (E D k : Set G))
    (eNormalizerPoint D k)).card_mul_index
  rw [eNormalizerPoint_stabilizer_card, MulAction.index_stabilizer] at h
  have hN := card_eq_card_quotient_mul_card_subgroup
    ((E D k).subgroupOf (normalizer (E D k : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe (E D k).le_normalizer).toEquiv,
    E_card] at hN
  change _ = Nat.card (eNormalizerQuotient D k) * 16 at hN
  omega

public theorem eNormalizerPoint_orbit_nonidentity :
    MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) ⊆ {1}ᶜ := by
  intro x hx hx1
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact eNormalizerPoint_ne_one D k ((MulAction.injective g) (by simpa using hx1))

public theorem eNormalizerPoint_orbit_card_le :
    (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k)).ncard ≤ 15 := by
  have h := Set.ncard_le_ncard (eNormalizerPoint_orbit_nonidentity D k)
  rw [Set.ncard_compl, Set.ncard_singleton, E_card] at h
  exact h

public theorem eNormalizerQuotient_card_le : Nat.card (eNormalizerQuotient D k) ≤ 360 := by
  rw [eNormalizerQuotient_card]
  have := eNormalizerPoint_orbit_card_le D k
  omega

public theorem eNormalizerPoint_orbit_eq_of_card (hc : Nat.card (eNormalizerQuotient D k) = 360) :
    MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) = {1}ᶜ := by
  apply Set.eq_of_subset_of_ncard_le (eNormalizerPoint_orbit_nonidentity D k)
  rw [eNormalizerQuotient_card] at hc
  rw [Set.ncard_compl, Set.ncard_singleton, E_card]
  omega

/-- Quotient order 360 forces transitivity on the nonidentity elements of E. -/
public theorem E_fusion_of_quotient_card (hc : Nat.card (eNormalizerQuotient D k) = 360)
    (x y : E D k) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : normalizer (E D k : Set G), (g : G) * x * (g : G)⁻¹ = y := by
  have hxO : x ∈ MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) := by
    rw [eNormalizerPoint_orbit_eq_of_card D k hc]; exact hx
  have hyO : y ∈ MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k) := by
    rw [eNormalizerPoint_orbit_eq_of_card D k hc]; exact hy
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hxO
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hyO
  refine ⟨h * g⁻¹, ?_⟩
  have he : (h * g⁻¹) • x = y := by rw [← hg, mul_smul, inv_smul_smul, hh]
  exact congrArg Subtype.val he

/-- An actual A6 quotient identification also supplies the orbit clause. -/
public theorem eNormalizerAction_of_quotient
    (hq : Nonempty (eNormalizerQuotient D k ≃* alternatingGroup (Fin 6))) : ENormalizerAction D k := by
  refine ⟨hq, E_fusion_of_quotient_card D k ?_⟩
  obtain ⟨e⟩ := hq
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide +kernel

public theorem eNormalizerPoint_orbit_odd :
    Odd (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k)).ncard := by
  rw [← MulAction.index_stabilizer, eNormalizerPoint_stabilizer]
  apply Nat.not_even_iff_odd.mp
  intro he
  have hdiv : (D.centralizer.subgroupOf (normalizer (E D k : Set G))).index ∣
      (D.sylow : Subgroup G).index :=
    (relIndex_dvd_index_of_le (centralizer_le_normalizer_E D k)).trans
      (index_dvd_of_le D.sylow_le_centralizer)
  exact D.sylow.not_dvd_index ((even_iff_two_dvd.mp he).trans hdiv)

/-- Numerical candidates only; these do not identify any abstract quotient. -/
public theorem eNormalizerQuotient_card_cases :
    Nat.card (eNormalizerQuotient D k) = 24 ∨ Nat.card (eNormalizerQuotient D k) = 72 ∨
    Nat.card (eNormalizerQuotient D k) = 120 ∨ Nat.card (eNormalizerQuotient D k) = 168 ∨
    Nat.card (eNormalizerQuotient D k) = 360 := by
  have hdiv := eNormalizerQuotient_card_dvd D k
  have hbound := eNormalizerPoint_orbit_card_le D k
  have hodd := eNormalizerPoint_orbit_odd D k
  rw [eNormalizerQuotient_card] at hdiv ⊢
  generalize (MulAction.orbit (normalizer (E D k : Set G)) (eNormalizerPoint D k)).ncard = n at *
  interval_cases n <;> norm_num at *

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
