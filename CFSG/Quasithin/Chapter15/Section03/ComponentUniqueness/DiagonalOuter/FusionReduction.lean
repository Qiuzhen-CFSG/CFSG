module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CentralizerConsequences
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.Transfer
/-!
# Forcing the field-involution fusion class

The local normalizer and representative centralizer determine a TI four-group.
Its two-perfect action property excludes fusion of the graph-field involution
with the central four-group. A component in the graph involution centralizer
excludes the `z` class. Thompson transfer through the cyclic-four quotient
then forces both graph representatives into the field class.

The theorem takes the geometric subgroup/action data and local model facts
explicitly. It constructs TI and the fusion conclusion, rather than taking
either as an input. The cover reduction must supply the geometry, and the
field-centralizer argument must still eliminate the resulting fusion.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.38, printed pp.1136--1137.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

/-- The TI, nonfusion and transfer arguments force both graph involutions
into the field-involution class. The geometric and model inputs are explicit. -/
theorem field_fusion_of_transfer_geometry [Finite G]
    (T : Sylow 2 G) (hG : IsPPerfect 2 G)
    (V I L F : Subgroup G) [IsKleinFour V]
    (hI : I = normalizer (V : Set G)) (v z : G)
    (hv : v ∈ V) (hv1 : v ≠ 1) (hCv : centralizer ({v} : Set G) ≤ I)
    (htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : I, (MulAut.conj (m : G)) x = y)
    (hF : IsPPerfect 2 F)
    (hnorm : centralizer (V : Set G) ≤ normalizer (L : Set G))
    (hkernel : centralizer (V : Set G) ⊓ centralizer (L : Set G) ≤ V)
    (hsmall : ¬ 4 ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom))
    (W : Subgroup T) (hW : W.index = 2)
    (q : W →* Multiplicative (ZMod 4))
    (hker : ∀ x : W, q x = 1 ↔ ((x : T) : G) ∈ L)
    (f : W) (hf : q f = Multiplicative.ofAdd (2 : ZMod 4))
    (τ : T) (hτ : orderOf τ = 2) (t : G)
    (hconj : (MulAut.conj t) (τ : G) = (τ : G) * (((f : T) : G)))
    (houtside : (τ : G) * (((f : T) : G)) ∉ V)
    (hfixedV : (τ : G) * (((f : T) : G)) ∈ centralizer (V : Set G))
    (hfixedF : (τ : G) * (((f : T) : G)) ∈ centralizer (F : Set G))
    (K : Subgroup (centralizer ({(τ : G)} : Set G)))
    (hK : IsComponent (centralizer ({(τ : G)} : Set G)) K)
    (hz : generalizedFitting (centralizer ({z} : Set G)) =
      pCore 2 (centralizer ({z} : Set G)))
    (hinside : ∀ x : G, x ∈ L → orderOf x = 2 → IsConj x v ∨ IsConj x z)
    (hcoset : ∀ x : G, orderOf x = 2 → x * (((f : T) : G))⁻¹ ∈ L →
      IsConj x (((f : T) : G))) :
    IsTISubgroup V ∧ IsConj (τ : G) (((f : T) : G)) ∧
      IsConj ((τ : G) * (((f : T) : G))) (((f : T) : G)) := by
  have hTI : IsTISubgroup V := ti_of_transitive_normalizer V I hI hv hv1 hCv htrans
  have hτtf : IsConj (τ : G) ((τ : G) * (((f : T) : G))) :=
    isConj_iff.mpr ⟨t, hconj⟩
  have hvnot := not_fused_of_centralizer_image_order V L F hTI hF hnorm hkernel
    hsmall hv hv1 houtside hfixedV hfixedF
  have hτv : ¬ IsConj (τ : G) v := fun hc => hvnot (hc.symm.trans hτtf)
  have hτz : ¬ IsConj (τ : G) z := not_fused_of_component_centralizer K hK hz
  have hcases := transfer_fusion_trichotomy T hG W hW q L hker f hf τ hτ v z
    hinside hcoset
  have hτf : IsConj (τ : G) (((f : T) : G)) := by
    rcases hcases with h | h | h
    · exact h
    · exact (hτv h).elim
    · exact (hτz h).elim
  exact ⟨hTI, hτf, hτtf.symm.trans hτf⟩
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
