module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.Contracts
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer

/-!
# Lifting the marked projective root calculations

Projective fixed points lift modulo Z(L). Projective commutator coverage
lifts once Z(L) is contained in the commutator. For the full Sylow centralizer,
fixing the actual component Sylow pointwise gives conjugation by an element
of its projective centre. The supplied plane-image equality lifts that
conjugator from W₂; faithfulness on the perfect central cover leaves C_S(L).

These are conditional lifting lemmas for the literal ProjectiveRootData;
they require neither arbitrary automorphism coverage nor centre identification.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section

open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Projective fixed points lift modulo the original central two-kernel. -/
theorem centralLift_root_fixed {S L D W : Subgroup G} {q : ℕ}
    (c : ProjectiveMarking L q) (r : ProjectiveRootData S L D W c)
    (hn : D ≤ normalizer (L : Set G)) (hc : pCore 2 L ≤ center L)
    (hz : ∃ z ∈ D, c.Diagonal z) :
    (S ⊓ L) ⊓ centralizer (D : Set G) ≤ W ⊔ centerImage L := by
  obtain ⟨z, hzD, hzdiag⟩ := hz
  let z' : normalizer (L : Set G) := ⟨z, hn hzD⟩
  have hf := (r.cubic z hzD hzdiag (markedAction c z') (markedAction_realizes c z')).1
  intro x hx
  let x' : L := ⟨x, hx.1.2⟩
  have hxf : projectiveMap c x' ∈ (W.subgroupOf L).map (projectiveMap c) := by
    rw [← hf]
    refine ⟨r.sylow_image ▸ mem_map_of_mem (projectiveMap c) hx.1.1, ?_⟩
    apply (MulAut.mem_fixedSubgroup (markedAction c z') (projectiveMap c x')).mpr
    rw [markedAction_apply]
    congr 1
    apply Subtype.ext
    change z * x * z⁻¹ = x
    rw [hx.2 z hzD, mul_inv_cancel_right]
  obtain ⟨w, hw, he⟩ := hxf
  have hcore : x' / w ∈ pCore 2 L := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact c.equivalence.injective he.symm
  have hxZ : x / (w : G) ∈ centerImage L := mem_map_of_mem L.subtype (hc hcore)
  have hm := (W ⊔ centerImage L).mul_mem (mem_sup_right hxZ) (mem_sup_left hw)
  change x / (w : G) * (w : G) ∈ _ at hm
  simpa only [div_mul_cancel] using hm

omit [Finite G] in
/-- A centralizer of D fixes Q pointwise; its projective conjugator lifts
from the actual Sylow centre through the given plane image. -/
theorem centralLift_sylow_fixed {S L D W : Subgroup G} {n : ℕ}
    (c : ProjectiveMarking L (2^n)) (r : ProjectiveRootData S L D W c)
    [Group.IsPerfect L] (hc : pCore 2 L ≤ center L) (hn : 0 < n)
    (hSL : S ≤ normalizer (L : Set G)) (hWS : W ≤ S) (hQD : S ⊓ L ≤ D) :
    S ⊓ centralizer (D : Set G) ≤ W ⊔ (S ⊓ centralizer (L : Set G)) := by
  intro s hs
  let s' : normalizer (L : Set G) := ⟨s, hSL hs.1⟩
  have hfix : ∀ x ∈ r.sylow, markedAction c s' x = x := by
    intro x hx
    change x ∈ (r.sylow : Subgroup PSL(3,c.F)) at hx
    rw [← r.sylow_image] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    rw [markedAction_apply]
    congr 1
    apply Subtype.ext
    change s * (l : G) * s⁻¹ = l
    rw [← hs.2 (l : G) (hQD ⟨hl, l.property⟩), mul_inv_cancel_right]
  obtain ⟨z, hz, he⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    c.F hn c.card (MulEquiv.refl _) r.sylow (markedAction c s') hfix
  rw [← r.plane_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  let w' := inclusion L.le_normalizer w
  have he' : markedAction c s' = markedAction c w' := by
    rw [markedAction_on_component]
    exact he
  have hker : s * (w : G)⁻¹ ∈ Chapter4.sectionCentralizer L :=
    (markedAction_eq_one_iff c (s' * w'⁻¹)).mp (by
      rw [map_mul, map_inv, he', mul_inv_cancel])
  rw [sectionCentralizer_eq_centralizer_of_perfect hc] at hker
  have ht : s * (w : G)⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
    ⟨S.mul_mem hs.1 (S.inv_mem (hWS hw)), hker⟩
  have hm := (W ⊔ (S ⊓ centralizer (L : Set G))).mul_mem
    (mem_sup_right ht) (mem_sup_left hw)
  change s * (w : G)⁻¹ * (w : G) ∈ _ at hm
  simpa only [inv_mul_cancel_right] using hm
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover

open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Projective commutator coverage lifts after the central kernel is moved. -/
theorem centralLift_commutator {S L D W : Subgroup G} {q : ℕ}
    (c : ProjectiveMarking L q) (r : ProjectiveRootData S L D W c)
    (hn : D ≤ normalizer (L : Set G)) (hc : pCore 2 L ≤ center L)
    (hDQ : D ≤ normalizer (S ⊓ L : Subgroup G))
    (hZ : centerImage L ≤ ⁅S ⊓ L, D⁆)
    (hz : ∃ z ∈ D, c.Diagonal z) : ⁅S ⊓ L, D⁆ = S ⊓ L := by
  have hCQ := le_normalizer_iff_commutator_le_left.mp hDQ
  apply le_antisymm hCQ
  obtain ⟨z, hzD, hzdiag⟩ := hz
  let z' : normalizer (L : Set G) := ⟨z, hn hzD⟩
  let f := projectiveMap c
  let C := ⁅S ⊓ L, D⁆
  have himage : (r.sylow : Subgroup PSL(3,c.F)) ≤ (C.subgroupOf L).map f := by
    rw [← (r.cubic z hzD hzdiag (markedAction c z') (markedAction_realizes c z')).2]
    rw [commutatorSubgroup, closure_le]
    rintro _ ⟨a, x, hx, rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.property
    rw [← r.sylow_image] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    have hu : (l : G)⁻¹ * ((z : G)^k * (l : G) * ((z : G)^k)⁻¹) ∈ C := by
      have hh := commutator_mem_commutator
        ((S ⊓ L).inv_mem ⟨hl, l.property⟩) (D.zpow_mem hzD k)
      simpa only [Subgroup.coe_subtype, commutatorElement_def, inv_inv, mul_assoc] using hh
    refine ⟨l⁻¹ * L.normalizerMonoidHom (z'^k) l, hu, ?_⟩
    change f (l⁻¹ * L.normalizerMonoidHom (z'^k) l) = (f l)⁻¹ * (a : MulAut _) (f l)
    rw [map_mul, map_inv, ← markedAction_apply]
    congr 1
    rw [map_zpow, hk]
  intro x hx
  let x' : L := ⟨x, hx.2⟩
  have hxim : f x' ∈ (r.sylow : Subgroup PSL(3,c.F)) :=
    r.sylow_image ▸ mem_map_of_mem f hx.1
  obtain ⟨u, hu, he⟩ := himage hxim
  have hker : x' / u ∈ pCore 2 L :=
    QuotientGroup.eq_iff_div_mem.mp (c.equivalence.injective he.symm)
  have hz' : x / (u : G) ∈ centerImage L := mem_map_of_mem L.subtype (hc hker)
  have hh := C.mul_mem (hZ hz') hu
  change x / (u : G) * (u : G) ∈ C at hh
  simpa only [div_mul_cancel] using hh
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover