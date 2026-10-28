module
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic
public import Stellmacher.OmegaOneCenterMap
public import Theory.ElementaryAbelian.Basic

/-!
# Cubic movement of the original Sylow omega-center span

For r c r⁻¹=c⁻¹ and c³=1, a vector fixed by r but moved by c has a cubic
translate moved by r. This applies to the actual binary six-letter module.
An equivariant group coordinate transports the fixed vector into Ω₁Z(R)
and its cubic translate into the literal normal closure. Any actual actor
mapping to r therefore moves that original omega-center span.

Source: Aschbacher–Smith C.1.21(4) and C.1.24(c), printed pp.129–131.
-/

public section

open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
theorem exists_moved_cubic_translate (ρ : Representation (ZMod 2) G V)
    (r c : G) (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace ρ (zpowers r) ≤ fixedSpace ρ (zpowers c)) :
    ∃ v : V, ρ r v=v ∧ ρ r (ρ c v)≠ρ c v := by
  by_contra hn
  push Not at hn
  apply hm
  intro v hv
  have hrv := (mem_fixedSpace_zpowers_iff ρ r v).mp hv
  have hrcv := hn v hrv
  have hrc : r*c=c⁻¹*r := by
    calc
      r*c=(r*c*r⁻¹)*r := by group
      _ = c⁻¹*r := by rw [hi]
  have hinv : ρ c⁻¹ v=ρ c v := by
    have hh : ρ r (ρ c v)=ρ c⁻¹ v := by
      rw [←Module.End.mul_apply,←map_mul,hrc,map_mul,Module.End.mul_apply,hrv]
    exact hh.symm.trans hrcv
  have h2 : ρ (c^2) v=v := by
    rw [pow_two,map_mul,Module.End.mul_apply,←hinv,ρ.self_inv_apply]
  apply (mem_fixedSpace_zpowers_iff ρ c v).mpr
  calc
    ρ c v=ρ c (ρ (c^2) v) := by rw [h2]
    _ = ρ (c^3) v := by rw [show c^3=c*c^2 by group,map_mul,Module.End.mul_apply]
    _ = v := by rw [hc,map_one,Module.End.one_apply]
end Representation.BinaryOffender

namespace Theory.SpecificGroups.SymmetricSix.TranspositionCubic
theorem exists_moved_transposition_vector (r : Sym) (hr : r.IsSwap) :
    ∃ c : Sym, orderOf c=3 ∧ c ∈ alternatingGroup (Fin 6) ∧ r*c*r⁻¹=c⁻¹ ∧
      normalizer (zpowers r : Set Sym) ⊔ zpowers c=⊤ ∧
      Nat.card (zpowers c ⊔ zpowers r : Subgroup Sym)=6 ∧
      ∃ v : BinaryPermutation.natural (Fin 6),
        BinaryPermutation.naturalRepresentation (Fin 6) r v=v ∧
        BinaryPermutation.naturalRepresentation (Fin 6) r
          (BinaryPermutation.naturalRepresentation (Fin 6) c v)≠
          BinaryPermutation.naturalRepresentation (Fin 6) c v := by
  obtain ⟨c,hc,hce,hci,hcg,hcard,hm⟩ := exists_cubic_for_transposition r hr
  exact ⟨c,hc,hce,hci,hcg,hcard,
    Representation.BinaryOffender.exists_moved_cubic_translate _ r c (hc ▸ pow_orderOf_eq_one c) hci hm⟩

open Stellmacher Representation.BinaryOffender
variable {G : Type*} [Group G]
theorem omega_span_moved (V R A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (q : G →* Sym)
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (r c : Sym) (hR : R.map q ≤ zpowers r) (hrA : r ∈ A.map q) (hcG : c ∈ q.range)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers c)) :
    ¬ A ≤ centralizer (normalClosure (omegaOneCenterAmbient R : Set G) : Set G) := by
  obtain ⟨v,hv,hcv⟩ := exists_moved_cubic_translate _ r c hc hi hm
  let u : V := e.symm (Multiplicative.ofAdd v)
  have heu : (e u).toAdd=v := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  have huv : v ∈ fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) :=
    (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
  have huR : (u:G) ∈ omegaOneCenterAmbient R := by
    apply (mem_omegaOneCenterAmbient_iff R (u:G)).mpr
    refine ⟨hVR u.property,elemPow_eq_one_of_isElementaryAbelian (u:G) u.property,?_⟩
    intro a ha
    have hfix : MulAut.conjNormal a u=u := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he,heu]
      exact huv ⟨q a,hR (mem_map_of_mem q ha)⟩
    have hh := congrArg (fun z : V => (z:G)) hfix
    change a*(u:G)*a⁻¹=(u:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨g,hg⟩ := hcG
  let w : V := MulAut.conjNormal g u
  have hw : (w:G) ∈ normalClosure (omegaOneCenterAmbient R : Set G) :=
    (normalClosure_normal.conj_mem _ (subset_normalClosure huR) g)
  obtain ⟨a,ha,hqa⟩ := hrA
  intro hA
  have hfix : MulAut.conjNormal a w=w := by
    apply Subtype.ext
    change a*(w:G)*a⁻¹=(w:G)
    rw [←hA ha (w:G) hw]
    group
  have hh := he a w
  rw [hfix,hqa] at hh
  have hwcoord : (e w).toAdd=BinaryPermutation.naturalRepresentation (Fin 6) c v := by
    rw [show w=MulAut.conjNormal g u from rfl,he,hg,heu]
  rw [hwcoord] at hh
  exact hcv hh.symm
end Theory.SpecificGroups.SymmetricSix.TranspositionCubic
