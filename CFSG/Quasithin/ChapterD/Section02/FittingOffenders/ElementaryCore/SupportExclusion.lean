module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.Basic
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.Cardinality
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion.Linear
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion.SmallAction

/-!
# Central lines are excluded from the Frattini subgroup

For an A-invariant central order-three line Z, its centralizer B in A has
order two and C_P(B) = Z. The preceding hyperplane input and odd averaging give
C_[V,Z](B) = [C_V(B),Z] of dimension two. The involution bound makes [V,Z]
at most four-dimensional. The actual image of P on this support is elementary
abelian, so Φ(P) fixes it. Faithfulness of Z on its own odd moved support
excludes Z from Φ(P).

Source: Aschbacher--Smith D.2.14(2), printed p.186, paragraph (++).
This proves the support-exclusion step from `HyperplaneSupport`; existence
of an invariant central line in a nontrivial Frattini subgroup is separate.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open SupportExclusion
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The hyperplane support input bounds the whole support of an invariant
order-three line by four dimensions, using its actual centralizer in A. -/
theorem central_line_support_bound (P A Z : Subgroup G)
    (hA : Nat.card A = 4) (hZP : Z ≤ P) (hZ : Nat.card Z = 3)
    (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ P A) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) ≤ 4 := by
  let B := A ⊓ centralizer (Z : Set G)
  have hB : Nat.card B = 2 := line_centralizer_card P A Z hA hZP hZ hnZ hfix
  obtain ⟨hr, he⟩ := line_eq_hyperplane_centralizer P A Z hA hZP hZ hnZ hfix
    (fun D hDA hDr hDn => (hs D hDA hDr hDn).1)
  have hZn : Z ≠ ⊥ := by
    intro hb
    have ho : Nat.card Z = 1 := card_eq_one.mpr hb
    omega
  have hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) Z) = 2 := by
    have hh := (hs B inf_le_left hr (by rw [he]; exact hZn)).2
    rwa [he] at hh
  have hodd : Odd (Nat.card Z) := hZ ▸ (by decide : Odd 3)
  have hfm := fixed_moved ρ Z B hodd (show B ≤ centralizer (Z : Set G) from inf_le_right)
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht⟩ := exists_ne (1 : B)
  have ht2 : (t : G) ^ 2 = 1 := by
    have htB : t ^ 2 = 1 := by simpa only [hB] using (pow_card_eq_one' (x := t))
    exact congrArg Subtype.val htB
  have htord : orderOf (t : G) = 2 := orderOf_eq_prime ht2
    (fun h => ht (Subtype.ext h))
  have htgen : zpowers (t : G) = B := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr t.property)
    rw [Nat.card_zpowers, htord, hB]
  have hstable := moved_stable ρ Z B (inf_le_left.trans hnZ)
  have hb := involution_bound ρ (t : G) ht2 (subspaceCommutator ρ ⊤ Z)
    (fun v hv => (hstable t.property v).mpr hv)
  rw [htgen, hfm, hdim] at hb
  exact hb

/-- The module-support exclusion in D.2.14 (++): an A-invariant central
order-three subgroup of P cannot lie in Φ(P). Normality of the line in G
is not required. The stronger source assumptions that P is normal and A
acts faithfully on P are unnecessary for this individual exclusion. -/
theorem central_line_not_le_frattini (hρ : Function.Injective ρ)
    (P A Z : Subgroup G) (hP : IsPGroup 3 P) (hA : Nat.card A = 4)
    (hcentral : Z ≤ (center P).map P.subtype) (hZ : Nat.card Z = 3)
    (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ P A) :
    ¬ Z ≤ (frattini P).map P.subtype := by
  have hZP : Z ≤ P := hcentral.trans (map_subtype_le _)
  have hPc : P ≤ centralizer (Z : Set G) := by
    intro p hp
    apply mem_centralizer_iff.mpr
    intro z hz
    obtain ⟨z', hz', rfl⟩ := hcentral hz
    exact (congrArg Subtype.val (mem_center_iff.mp hz' ⟨p, hp⟩)).symm
  have hstable := moved_stable ρ Z P (hPc.trans (centralizer_le_normalizer _))
  have hd := central_line_support_bound ρ P A Z hA hZP hZ hnZ hfix hs
  have hPhi := frattini_fixes_small ρ (subspaceCommutator ρ ⊤ Z) P hP hstable hd
  have hfaith := moved_faithful ρ hρ Z (hZ ▸ (by decide : Odd 3))
  intro hZPhi
  have hb : Z = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    rw [← hfaith]
    exact ⟨hz, (hPhi (hZPhi hz)).2⟩
  have hc : Nat.card Z = 1 := card_eq_one.mpr hb
  omega

end CFSG.Quasithin.ChapterD.ElementaryCore
