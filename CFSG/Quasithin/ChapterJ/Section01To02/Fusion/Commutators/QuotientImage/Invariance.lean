module
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientMaps
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Invariance and the full natural commutator image

For h in HC, adjoining Ũ to its cyclic image in H/Z does not change the
commutator with Q̃. The bound [HC,K] ≤ U makes this enlarged subgroup
K-invariant; normality of Q then makes its commutator image K-invariant.
The actual Ru2 marking and the surjection K → A₅ give transitivity on
nonzero vectors of U/Z. Consequently any nontrivial commutator image is Ũ.

This proves the invariance and irreducibility step, without presupposing
either one. The separate index argument must still establish nontriviality.
All quotient images and relative normality refer to the original H and Z.

Source: Aschbacher–Smith, Lemma J.2.4(1), printed p.434 (PDF p.445).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem cyclic_commutator_normalized
    (C K Q U : Subgroup G) [Q.Normal] [U.Normal] (h : G) (hh : h ∈ C)
    (hCK : ⁅C,K⁆ ≤ U) (hUQ : ⁅U,Q⁆ = ⊥) :
    K ≤ normalizer (⁅zpowers h,Q⁆ : Subgroup G) := by
  have hA := le_normalizer_sup_of_commutator_le C K (zpowers h) U
    (zpowers_le.mpr hh) hCK
  have he : ⁅zpowers h,Q⁆ = ⁅zpowers h ⊔ U,Q⁆ := by
    rw [commutator_comm (zpowers h) Q, commutator_comm (zpowers h ⊔ U) Q]
    exact commutator_eq_of_centralizing_sup (sup_comm U (zpowers h))
      (commutator_eq_bot_iff_le_centralizer.mp hUQ) le_normalizer_of_normal
  rw [he]
  intro k hk
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hk),
    mem_normalizer_iff_map_conj_eq.mp (show k ∈ normalizer (Q : Set G) from
      le_normalizer_of_normal (mem_top k))]

/-- Monotonicity for the actual images in H/Z. -/
theorem modZ_mono (d : TypeRuSetup G) {A D : Subgroup G} (hAD : A ≤ D) :
    modZ d A ≤ modZ d D := map_mono (fun _ hx => hAD hx)

/-- K-invariance of the literal cyclic commutator image in J.2.4. -/
theorem modZ_commutator_normalized (d : TypeRuSetup G)
    (hCK : ⁅d.HC,d.K⁆ ≤ d.U) (h : d.HC) :
    modZ d d.K ≤ normalizer
      (⁅zpowers (centerQuotientMap d ⟨h,h.property.1⟩),modZ d d.Q⁆ :
        Subgroup (d.H ⧸ d.Z.subgroupOf d.H)) := by
  let : (d.Q.subgroupOf d.H).Normal :=
    normal_subgroupOf_of_le_normalizer d.ru2.six.normalized
  let : (d.U.subgroupOf d.H).Normal :=
    normal_subgroupOf_of_le_normalizer d.ru2.natural.normalized
  let : (modZ d d.Q).Normal :=
    Subgroup.Normal.map inferInstance (centerQuotientMap d) (QuotientGroup.mk'_surjective _)
  let : (modZ d d.U).Normal :=
    Subgroup.Normal.map inferInstance (centerQuotientMap d) (QuotientGroup.mk'_surjective _)
  apply cyclic_commutator_normalized (modZ d d.HC) (modZ d d.K)
    (modZ d d.Q) (modZ d d.U) _ (mem_map.mpr ⟨⟨h,h.property.1⟩,h.property,rfl⟩)
  · rw [← modZ_commutator d inf_le_left d.K_le_H]
    exact modZ_mono d hCK
  · rw [← modZ_commutator d d.ru2.natural.section_le (pCoreIn_le 2 _)]
    apply le_bot_iff.mp
    have hUQ : ⁅d.U,d.Q⁆ ≤ d.Z := by
      rw [commutator_comm]
      exact d.commutator_Q_U_le_Z
    apply (modZ_mono d hUQ).trans
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact (QuotientGroup.eq_one_iff _).mpr hz

/-- The actual residual K is transitive on nonzero vectors of U/Z. -/
theorem transitive_natural_K (d : TypeRuSetup G) (u v : FourSpace)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ k : d.K, d.ru2.naturalAction.action
      (d.ru2.quotientMap ⟨k,d.K_le_H k.property⟩) u = v := by
  obtain ⟨g,hg⟩ := SL2FourNatural.transitive_nonzero u v hu hv
  obtain ⟨k,hk⟩ := d.alternatingMap_surjective (d.ru2.naturalAction.marking g)
  refine ⟨k, ?_⟩
  rw [← d.alternatingMap_apply, hk, d.ru2.naturalAction.restriction]
  exact hg

/-- The inherited natural action forces every nonzero K-invariant subgroup
of the actual U-image to be the whole image. -/
theorem eq_modZ_U_of_normalized_ne_bot (d : TypeRuSetup G)
    (W : Subgroup (d.H ⧸ d.Z.subgroupOf d.H)) (hWU : W ≤ modZ d d.U)
    (hKW : modZ d d.K ≤ normalizer (W : Set _)) (hW : W ≠ ⊥) :
    W = modZ d d.U := by
  obtain ⟨w,hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  have hw := w.property
  have hw1 : (w : d.H ⧸ d.Z.subgroupOf d.H) ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨u,hu,heu⟩ := hWU hw
  have hu0 : (d.ru2.natural.coordinates ⟨u,hu⟩).toAdd ≠ 0 := by
    intro he
    have huZ := (d.ru2.natural.coordinates_eq_one_iff ⟨u,hu⟩).mp he
    exact hw1 (heu.symm.trans ((QuotientGroup.eq_one_iff _).mpr huZ))
  apply le_antisymm hWU
  rintro _ ⟨v,hv,rfl⟩
  by_cases hvZ : (v : G) ∈ d.Z
  · have hvone : centerQuotientMap d v = 1 := (QuotientGroup.eq_one_iff _).mpr hvZ
    rw [hvone]
    exact W.one_mem
  have hv0 : (d.ru2.natural.coordinates ⟨v,hv⟩).toAdd ≠ 0 := by
    exact fun he => hvZ ((d.ru2.natural.coordinates_eq_one_iff ⟨v,hv⟩).mp he)
  obtain ⟨k,hk⟩ := transitive_natural_K d _ _ hu0 hv0
  let kH : d.H := ⟨k,d.K_le_H k.property⟩
  let a : d.U := ⟨(k : G) * u * (k : G)⁻¹,
    le_normalizer_iff.mp d.ru2.natural.normalized kH kH.property u hu⟩
  have ha : d.ru2.natural.coordinates a = d.ru2.natural.coordinates ⟨v,hv⟩ :=
    Multiplicative.toAdd.injective ((d.ru2.natural.equivariant kH ⟨u,hu⟩).trans hk)
  have hadiff : ((a⁻¹ * (⟨v,hv⟩ : d.U) : d.U) : G) ∈ d.Z := by
    apply (d.ru2.natural.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, ha, inv_mul_cancel]
  have heq : centerQuotientMap d (kH * u * kH⁻¹) = centerQuotientMap d v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (k : G) * (u : G) * (k : G)⁻¹ / (v : G) ∈ d.Z
    have ha' : (a : G)⁻¹ * v ∈ d.Z := hadiff
    have hh : (v : G)⁻¹ * a ∈ d.Z := by simpa only [mul_inv_rev, inv_inv] using d.Z.inv_mem ha'
    have hh' : (a : G) * (v : G)⁻¹ ∈ d.Z := by
      have hz := le_normalizer_iff.mp
        (d.ru2.natural.section_le.trans (Subgroup.centralizer_le_normalizer _))
        a a.property _ hh
      simpa only [← mul_assoc, mul_inv_cancel_right] using hz
    simpa only [a, div_eq_mul_inv] using hh'
  rw [← heq, map_mul, map_mul, map_inv]
  apply le_normalizer_iff.mp hKW _ (mem_map.mpr ⟨kH,k.property,rfl⟩)
  exact heu ▸ hw

/-- The full image conclusion after the separate nontriviality argument. -/
theorem modZ_commutator_eq_of_ne_bot (d : TypeRuSetup G)
    (hQK : d.Q ≤ d.K) (hCK : ⁅d.HC,d.K⁆ ≤ d.U)
    (h : d.HC)
    (hne : ⁅zpowers (centerQuotientMap d ⟨h,h.property.1⟩),modZ d d.Q⁆ ≠ ⊥) :
    ⁅zpowers (centerQuotientMap d ⟨h,h.property.1⟩),modZ d d.Q⁆ = modZ d d.U := by
  apply eq_modZ_U_of_normalized_ne_bot d _ _ (modZ_commutator_normalized d hCK h) hne
  rw [← modZ_zpowers d ⟨h,h.property.1⟩,
    ← modZ_commutator d (zpowers_le.mpr h.property.1) (pCoreIn_le 2 _)]
  exact modZ_mono d ((commutator_mono (zpowers_le.mpr h.property) hQK).trans hCK)

end CFSG.Quasithin.ChapterJ.Fusion
