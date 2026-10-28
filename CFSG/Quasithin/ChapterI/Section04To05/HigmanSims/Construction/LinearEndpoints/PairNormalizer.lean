module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicals
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneCentralizerCard
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicals

/-!
# The literal normalizer of the paired plane radicals

This internal continuation intentionally shares the private commutator
calculations of PairedRadicals through a same-package import-all edge.
The first radical's stabilizer inside the whole cyclic-four core is exactly
the square preimage of the seed plane. Thus every core element whose square
lies outside that plane gives the same second radical. Consequently the
joint normalizer of the two radicals is exactly the normalizer of the first
radical intersected with the full plane normalizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem core_normalizer_iff (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) :
    p ∈ normalizer (A : Set G) ↔ p ^ 2 ∈ W := by
  constructor
  · intro hpN
    by_contra hpW
    have hi := (conjugate_pair h W A hWV hW4 hWA hAC hAP p hp hpW).1
    have he : A.map (MulAut.conj p).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hpN
    rw [he, inf_idem] at hi
    have hh := congrArg (fun S : Subgroup G => Nat.card S) hi
    rw [hA16, hW4] at hh
    omega
  · intro hpW
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro x ⟨a, ha, rfl⟩
      have had := plane_displacement h W hWV hW4 a p (hAC ha)
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) hp hpW
      have hpa : ⁅p, a⁆ ∈ A := by
        rw [← commutatorElement_inv]
        exact A.inv_mem (hWA had)
      have hh := A.mul_mem hpa ha
      change p * a * p⁻¹ ∈ A
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · exact (card_map_of_injective (MulAut.conj p).injective).ge

private theorem same_exterior_conjugate (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p r : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2)
    (hr : r ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W) (hrW : r ^ 2 ∉ W) :
    A.map (MulAut.conj p).toMonoidHom = A.map (MulAut.conj r).toMonoidHom := by
  let := core_abelian h
  let WV := W.subgroupOf V
  have hi : WV.index = 2 := by
    have hh := WV.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hWV).toEquiv, hW4, h.seed_card] at hh
    omega
  have hsq : (r⁻¹ * p) ^ 2 ∈ W := by
    have hh := (mul_mem_iff_of_index_two hi
      (a := (⟨(r ^ 2)⁻¹, V.inv_mem (core_square_seed h r hr)⟩ : V))
      (b := (⟨p ^ 2, core_square_seed h p hp⟩ : V))).mpr
        (iff_of_false (by intro hh; exact hrW (W.inv_mem_iff.mp hh)) hpW)
    change (r ^ 2)⁻¹ * p ^ 2 ∈ W at hh
    rwa [(show Commute r⁻¹ p from setLike_mul_comm (inv_mem hr) hp).mul_pow, inv_pow]
  have hd := (core_normalizer_iff h W A hWV hW4 hA16 hWA hAC hAP
    (r⁻¹ * p) (mul_mem (inv_mem hr) hp)).mpr hsq
  have he : (MulAut.conj p).toMonoidHom =
      (MulAut.conj r).toMonoidHom.comp (MulAut.conj (r⁻¹ * p)).toMonoidHom := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hdmap : A.map (MulAut.conj (r⁻¹ * p)).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hd
  rw [he, ← map_map, hdmap]

/-- The first radical's stabilizer in the whole original core is exactly
the square preimage of the literal seed plane. -/
theorem TypeAt.plane_radical_core_normalizer (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) :
    p ∈ normalizer (A : Set G) ↔ p ^ 2 ∈ W :=
  core_normalizer_iff h W A hWV hW4 hA16 hWA hAC hAP p hp

/-- The actual paired radicals have joint normalizer equal to the stabilizer
of the first radical and its original seed plane. -/
theorem TypeAt.paired_plane_radicals_normalizer (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W) :
    normalizer (A : Set G) ⊓ normalizer (A.map (MulAut.conj p).toMonoidHom : Set G) =
      normalizer (A : Set G) ⊓ normalizer (W : Set G) := by
  let B := A.map (MulAut.conj p).toMonoidHom
  have hi := (conjugate_pair h W A hWV hW4 hWA hAC hAP p hp hpW).1
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1, ?_⟩
    rw [← hi]
    apply mem_normalizer_iff_map_conj_eq.mpr
    have ha : A.map (MulAut.conj g).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hg.1
    have hb : (A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        A.map (MulAut.conj p).toMonoidHom := mem_normalizer_iff_map_conj_eq.mp hg.2
    change (A ⊓ A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj g).injective, ha, hb]
  · rintro g ⟨hgA, hgW⟩
    refine ⟨hgA, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    change (A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom = _
    have hgM := h.plane_normalizer_le_seed_normalizer W hWV hW4 hgW
    have hr : g * p * g⁻¹ ∈ (normalizer (V : Set G)).pCoreIn 2 :=
      (mem_normalizer_iff.mp (core_normalized h hgM) p).mp hp
    have hrW : (g * p * g⁻¹) ^ 2 ∉ W := by
      intro hh
      have he : (g * p * g⁻¹) ^ 2 = g * p ^ 2 * g⁻¹ := by simp only [pow_two]; group
      rw [he] at hh
      exact hpW ((mem_normalizer_iff.mp hgW (p ^ 2)).mpr hh)
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj p).toMonoidHom =
        (MulAut.conj (g * p * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hgmap : A.map (MulAut.conj g).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hgA
    rw [map_map, he, ← map_map, hgmap]
    exact same_exterior_conjugate h W A hWV hW4 hA16 hWA hAC hAP
      (g * p * g⁻¹) p hr hp hrW hpW

end CFSG.Quasithin.HigmanSims
