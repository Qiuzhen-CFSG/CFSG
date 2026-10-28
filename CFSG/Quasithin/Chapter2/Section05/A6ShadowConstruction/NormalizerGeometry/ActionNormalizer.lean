module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.Algebra

/-!
# Lifting the four-group normalizer through the A₆ action

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed p.570, following Lemma 2.5.27.

Transport `E ≤ S_K` through the specified isomorphism `modelK`. Compatibility
identifies the images of elements of `K` with their inner automorphisms and
sends `N_H(E)` into the stabilizer of the transported four-group. The conjugate
reflection `eˣ` has an outer involutory image: an inner image would express it
as a product of elements of `K` and the cyclic core, both centralizing the core,
contrary to the inversion supplied by `CoreReduction`.

The concrete automorphism-stabilizer generation identity now lifts through the
specified action kernel. Independently, transport of the normalizer inside `K`
gives the symmetric-group isomorphism. `ModelFacts` states exactly the two
finite-model inputs. Their proof belongs to the A₆ model and source assembly;
these conditional results do not choose `E`, prove square stability, or supply
the separate reflection-centralizer identity used in the direct-product step.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
namespace ActionNormalizer
open Subgroup NormalizerCalculation

local notation "Q" => alternatingGroup (Fin 6)

/-- Concrete identities in `A₆` and its actual automorphism group. The second
uses the range of inner conjugation, and requires an involution outside that
range stabilizing the same four-group. No ambient generation or ambient
normalizer isomorphism is included among these premises. -/
public structure ModelFacts : Prop where
  symmetric : ∀ F : Subgroup Q, IsKleinFour F →
    Nonempty (normalizer (F : Set Q) ≃* Equiv.Perm (Fin 4))
  outer_generates : ∀ F : Subgroup Q, IsKleinFour F →
    ∀ a : MulAut Q, a ^ 2 = 1 → a ∉ (MulAut.conj : Q →* MulAut Q).range →
      F.map a.toMonoidHom = F → ∀ b : MulAut Q, F.map b.toMonoidHom = F →
        b ∈ zpowers a ⊔ (normalizer (F : Set Q)).map MulAut.conj

variable {G : Type*} [Group G]

private theorem s_le_h (d : Setup G) : d.S ≤ d.H := by
  rw [d.generated]; exact le_sup_right

private theorem k_le_h (d : Setup G) : d.K ≤ d.H := by
  rw [d.generated]; exact le_sup_left

private def modelFour (d : Setup G) (E : Subgroup G) : Subgroup Q :=
  (E.subgroupOf d.K).map d.modelK.toMonoidHom

private theorem modelFour_mem (d : Setup G) (E : Subgroup G) (q : Q) :
    q ∈ modelFour d E ↔ (d.modelK.symm q : G) ∈ E := by
  change q ∈ (E.subgroupOf d.K).map d.modelK.toMonoidHom ↔ _
  rw [mem_map_equiv]
  rfl

private noncomputable def fourEquiv (d : Setup G) (E : Subgroup G) (hE : E ≤ d.K) :
    E ≃* modelFour d E :=
  (subgroupOfEquivOfLe hE).symm.trans (d.modelK.subgroupMap (E.subgroupOf d.K))

private theorem modelFour_four (d : Setup G) (E : Subgroup G)
    [IsKleinFour E] (hE : E ≤ d.K) : IsKleinFour (modelFour d E) := by
  let f := fourEquiv d E hE
  exact ⟨(Nat.card_congr f.toEquiv).symm.trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv f).symm.trans IsKleinFour.exponent_two⟩

private theorem action_on_k (d : Setup G) (k : d.K) :
    d.action ⟨k, k_le_h d k.property⟩ = MulAut.conj (d.modelK k) := by
  ext a : 1
  obtain ⟨b, rfl⟩ := d.modelK.surjective a
  apply d.modelK.symm.injective
  apply Subtype.ext
  rw [d.action_compatible]
  simp [MulAut.conj_apply]

private theorem action_stabilizes (d : Setup G) (E : Subgroup G)
    (h : d.H) (hn : (h : G) ∈ normalizer (E : Set G)) :
    (modelFour d E).map (d.action h).toMonoidHom = modelFour d E := by
  ext q
  rw [mem_map_equiv, modelFour_mem, modelFour_mem]
  have hh := mem_normalizer_iff.mp hn (d.modelK.symm ((d.action h).symm q) : G)
  rw [← d.action_compatible h _] at hh
  simpa only [d.modelK.apply_symm_apply, MulEquiv.apply_symm_apply] using hh

private theorem normalizer_model (d : Setup G) (E : Subgroup G) (hE : E ≤ d.K) :
    ((normalizer (E : Set G)).subgroupOf d.K).map d.modelK.toMonoidHom =
      normalizer (modelFour d E : Set Q) := by
  rw [subgroupOf_normalizer_eq hE, map_equiv_normalizer_eq]
  rfl

private theorem model_normalizer_mem (d : Setup G) (E : Subgroup G) (hE : E ≤ d.K)
    (q : Q) (hq : q ∈ normalizer (modelFour d E : Set Q)) :
    (d.modelK.symm q : G) ∈ normalizer (E : Set G) := by
  rw [← normalizer_model d E hE, mem_map_equiv] at hq
  exact hq

private noncomputable def normalizerEquiv (d : Setup G) (E : Subgroup G)
    (hE : E ≤ d.K) : (d.K ⊓ normalizer (E : Set G) : Subgroup G) ≃*
      normalizer (modelFour d E : Set Q) := by
  have hn : (d.K ⊓ normalizer (E : Set G)).subgroupOf d.K =
      (normalizer (E : Set G)).subgroupOf d.K := inf_subgroupOf_left _ _
  exact (subgroupOfEquivOfLe (show d.K ⊓ normalizer (E : Set G) ≤ d.K from inf_le_left)).symm.trans
    ((MulEquiv.subgroupCongr hn).trans
      ((d.modelK.subgroupMap _).trans (MulEquiv.subgroupCongr (normalizer_model d E hE))))

private theorem core_centralizes_core (d : Setup G) (r : CoreReduction d) :
    d.core ≤ centralizer (d.core : Set G) := by
  obtain ⟨f⟩ := r.cyclic
  intro u hu v hv
  have hh : (⟨v, hv⟩ : d.core) * ⟨u, hu⟩ = ⟨u, hu⟩ * (⟨v, hv⟩ : d.core) := by
    apply f.injective
    simp only [map_mul]
    exact mul_comm _ _
  exact congrArg Subtype.val hh

private theorem inner_centralizes_core (d : Setup G) (r : CoreReduction d)
    (h : d.H) (ha : d.action h ∈ (MulAut.conj : Q →* MulAut Q).range) :
    (h : G) ∈ centralizer (d.core : Set G) := by
  obtain ⟨q, hq⟩ := ha
  let k : d.K := d.modelK.symm q
  let kH : d.H := ⟨k, k_le_h d k.property⟩
  have hk : d.action kH = d.action h := by
    rw [action_on_k]
    exact (congrArg MulAut.conj (d.modelK.apply_symm_apply q)).trans hq
  have hc : h * kH⁻¹ ∈ d.action.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, mul_inv_cancel]
  rw [d.action_kernel] at hc
  have hcc : ((h : G) * (k : G)⁻¹) ∈ centralizer (d.core : Set G) :=
    core_centralizes_core d r hc
  have hkC : (k : G) ∈ centralizer (d.core : Set G) := fun v hv => (hv.2 k k.property).symm
  have hp := (centralizer (d.core : Set G)).mul_mem hcc hkC
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hp


/-- Lift the concrete Aut(A₆) stabilizer calculation through the compatible
conjugation action, using the cyclic core as its exact kernel. -/
public theorem normalizer_eq_of_model [Finite G] (d : Setup G) (r : CoreReduction d) (m : ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    d.H ⊓ normalizer (E : Set G) =
      (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) ⊔ (d.K ⊓ normalizer (E : Set G)) := by
  let s := d.x⁻¹ * e * d.x
  have hEK : E ≤ d.K := hE.trans inf_le_right
  have hsX : s ∈ conjugate d.x E := ⟨e, he, by simp [s]⟩
  have hsH : s ∈ d.H := s_le_h d (conjugate_le_s d (hE.trans inf_le_left) hsX)
  have hsN : s ∈ normalizer (E : Set G) := by
    apply centralizer_le_normalizer
    intro v hv
    exact (d.sk_centralizes_conjugate (hE hv) s (map_mono hE hsX)).symm
  have hs2 : s ^ 2 = 1 := by
    have he2 : e ^ 2 = 1 := by
      simpa only [pow_two, coe_mul, coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
    have hh : ((MulAut.conj d.x⁻¹) e) ^ 2 = 1 := by rw [← map_pow, he2, map_one]
    simpa [s] using hh
  let sH : d.H := ⟨s, hsH⟩
  have ha2 : (d.action sH) ^ 2 = 1 := by
    rw [← map_pow, show sH ^ 2 = 1 from Subtype.ext hs2, map_one]
  have haout : d.action sH ∉ (MulAut.conj : Q →* MulAut Q).range := by
    intro hin
    exact conjugate_not_centralizer d r E hE he heout (inner_centralizes_core d r sH hin)
  let L : Subgroup G := (zpowers s ⊔ d.core) ⊔ (d.K ⊓ normalizer (E : Set G))
  have hCL : d.core ≤ L := le_sup_right.trans le_sup_left
  apply le_antisymm
  · rintro h ⟨hhH, hhN⟩
    let hH : d.H := ⟨h, hhH⟩
    have hb := m.outer_generates (modelFour d E) (modelFour_four d E hEK)
      (d.action sH) ha2 haout (action_stabilizes d E sH hsN)
      (d.action hH) (action_stabilizes d E hH hhN)
    have himage : zpowers (d.action sH) ⊔
        (normalizer (modelFour d E : Set Q)).map MulAut.conj ≤
        (L.subgroupOf d.H).map d.action := by
      refine sup_le (zpowers_le.mpr ?_) (map_le_iff_le_comap.mpr ?_)
      · exact ⟨sH, mem_sup_left (mem_sup_left (mem_zpowers s)), rfl⟩
      · intro q hq
        let k : d.K := d.modelK.symm q
        let kH : d.H := ⟨k, k_le_h d k.property⟩
        refine ⟨kH, mem_sup_right ⟨k.property, model_normalizer_mem d E hEK q hq⟩, ?_⟩
        rw [action_on_k]
        exact congrArg MulAut.conj (d.modelK.apply_symm_apply q)
    obtain ⟨l, hl, hal⟩ := himage hb
    have hker : hH * l⁻¹ ∈ d.action.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hal, mul_inv_cancel]
    rw [d.action_kernel] at hker
    have hp := L.mul_mem (hCL hker) hl
    change (h * (l : G)⁻¹) * (l : G) ∈ L at hp
    change h ∈ L
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hp
  · have hc : d.core ≤ d.H ⊓ normalizer (E : Set G) := by
      refine le_inf (inf_le_left.trans (s_le_h d)) ?_
      intro v hv
      apply centralizer_le_normalizer
      intro a ha
      exact hv.2 a (hEK ha)
    exact sup_le (sup_le (zpowers_le.mpr ⟨hsH, hsN⟩) hc)
      (le_inf (inf_le_left.trans (k_le_h d)) inf_le_right)

/-- Transport the normalizer in the actual subgroup `K` through `modelK`.
No independent identification of the ambient normalizer is assumed. -/
public theorem normalizer_symmetric_of_model (d : Setup G) (m : ModelFacts)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    Nonempty ((d.K ⊓ normalizer (E : Set G) : Subgroup G) ≃* Equiv.Perm (Fin 4)) := by
  have hEK : E ≤ d.K := hE.trans inf_le_right
  obtain ⟨f⟩ := m.symmetric (modelFour d E) (modelFour_four d E hEK)
  exact ⟨(normalizerEquiv d E hEK).trans f⟩

end ActionNormalizer
end CFSG.Quasithin.Chapter2.A6ShadowConstruction
