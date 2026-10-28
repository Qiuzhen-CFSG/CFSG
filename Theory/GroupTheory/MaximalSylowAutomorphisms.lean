module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Simple
public import Theory.GroupTheory.CoatomNormalizerIndex

/-!
# Automorphisms of maximal Sylow overgroups

Let M be maximal proper in a simple finite group, and identify M with a
local group H. A nontrivial normal p-subgroup N of H determines M as the
ambient normalizer of its transported image. If N is characteristic in
each Sylow p-subgroup of H, every ambient automorphism preserving the
specified Sylow subgroup preserves that image, hence preserves M.

The proof transports the Sylow automorphism through the actual isomorphism.
It uses maximality to prove the full ambient normalizer equality; normality
or Sylow characteristicity alone would not give that equality.

Source application: Aschbacher–Smith, Proposition 1.3.4, printed p.511 of
`refs/quasithin.pdf`. The concrete local characteristic-subgroup facts are
separate inputs to this general finite-group argument.
-/

public section

open Subgroup

namespace Subgroup

/-- Restrict an ambient automorphism to a subgroup that it preserves. -/
def stableAut {G : Type*} [Group G] (S : Subgroup G) (b : MulAut G)
    (hb : ∀ x, b x ∈ S ↔ x ∈ S) : MulAut S where
  toFun x := ⟨b x, (hb x).mpr x.property⟩
  invFun x := ⟨b.symm x, (hb (b.symm x)).mp (by simpa only [b.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x)
  right_inv x := Subtype.ext (b.apply_symm_apply x)
  map_mul' x y := Subtype.ext (b.map_mul x y)

/-- The restricted automorphism agrees with the ambient one. -/
theorem stableAut_coe {G : Type*} [Group G] (S : Subgroup G) (b : MulAut G)
    (hb : ∀ x, b x ∈ S ↔ x ∈ S) (x : S) : (stableAut S b hb x : G) = b x := by rfl

private theorem map_eq_of_stable {G : Type*} [Group G] (S : Subgroup G) (b : MulAut G)
    (hb : ∀ x, b x ∈ S ↔ x ∈ S) : S.map b.toMonoidHom = S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hb x).mpr hx
  · intro x hx
    exact ⟨b.symm x, (hb (b.symm x)).mp (by simpa using hx), b.apply_symm_apply x⟩

/-- If the centralizer of a normal p-subgroup is central, restricting the
ambient center gives exactly the center of every Sylow p-subgroup. -/
theorem center_subgroupOf_sylow_eq_of_centralizer_le_center
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hp : IsPGroup p N)
    (hc : centralizer (N : Set G) ≤ center G) (P : Sylow p G) :
    (center G).subgroupOf P.toSubgroup = center P := by
  ext x
  constructor
  · intro hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
  · intro hx
    apply hc
    intro n hn
    exact congrArg (fun z : P => (z : G))
      (mem_center_iff.mp hx ⟨n, hp.le_sylow_of_normal P hn⟩)

/-- A normal subgroup characteristic in local Sylows makes every maximal
embedding stable under automorphisms preserving its ambient Sylow. -/
theorem stable_coatom_of_sylow_characteristic_normal
    {G H : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (N : Subgroup H) [N.Normal]
    (hne : N ≠ ⊥) (hp : IsPGroup p N)
    (hchar : ∀ P : Sylow p H, (N.subgroupOf P.toSubgroup).Characteristic)
    (S : Sylow p G) (M : Subgroup G) (hM : IsCoatom M)
    (hSM : S.toSubgroup ≤ M) (e : M ≃* H)
    (b : MulAut G) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ M ↔ x ∈ M := by
  let P := (S.subtype hSM).mapSurjective (f := e.toMonoidHom) e.surjective
  let f : S ≃* P := (subgroupOfEquivOfLe hSM).symm.trans
    (e.subgroupMap (S.toSubgroup.subgroupOf M))
  let K := N.comap e.toMonoidHom
  let B := K.map M.subtype
  have hK : K ≠ ⊥ := by
    intro h
    apply hne
    have hm := map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N
    rw [show N.comap e.toMonoidHom = ⊥ from h, map_bot] at hm
    exact hm.symm
  have hB : B ≠ ⊥ := fun h => hK ((K.map_eq_bot_iff_of_injective M.subtype_injective).mp h)
  have hBM : B ≤ M := map_subtype_le K
  have hn : normalizer (B : Set G) ≠ ⊤ := by
    intro hn
    rcases (normalizer_eq_top_iff.mp hn).eq_bot_or_eq_top with h | h
    · exact hB h
    · exact hM.ne_top (top_unique (h ▸ hBM))
  have hNM : normalizer (B : Set G) = M :=
    normalizer_map_eq_of_isCoatom_of_ne_top M hM K hn
  have hBS : B ≤ S.toSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : e x ∈ P := hp.le_sylow_of_normal P hx
    obtain ⟨y, hy, he⟩ := hxP
    exact e.injective he ▸ hy
  have hstable : ∀ x, b x ∈ B ↔ x ∈ B := by
    have forward (c : MulAut G) (hc : ∀ x, c x ∈ S ↔ x ∈ S)
        (x : G) (hx : x ∈ B) : c x ∈ B := by
      let xS : S := ⟨x, hBS hx⟩
      let u := MulAut.congr f (stableAut S.toSubgroup c hc)
      have hxN : f xS ∈ N.subgroupOf P.toSubgroup := by
        obtain ⟨y, hy, he⟩ := hx
        change e ⟨x, hSM xS.property⟩ ∈ N
        have he' : (⟨x, hSM xS.property⟩ : M) = y := Subtype.ext he.symm
        rwa [he']
      have huN := characteristic_iff_le_comap.mp (hchar P) u hxN
      refine ⟨⟨c x, hSM ((hc x).mpr xS.property)⟩, ?_, rfl⟩
      change (f (stableAut S.toSubgroup c hc xS) : H) ∈ N
      change (u (f xS) : H) ∈ N at huN
      simpa only [u, MulAut.congr_apply, MulEquiv.trans_apply, f.symm_apply_apply] using huN
    intro x
    constructor
    · intro hx
      have hh : ∀ x, b.symm x ∈ S ↔ x ∈ S := fun x => by
        simpa only [b.apply_symm_apply] using (hb (b.symm x)).symm
      simpa using forward b.symm hh (b x) hx
    · exact forward b hb x
  have hmap : M.map b.toMonoidHom = M := by
    rw [← hNM, map_equiv_normalizer_eq, map_eq_of_stable B b hstable]
  intro x
  constructor
  · intro hx
    have hx' : b x ∈ M.map b.toMonoidHom := hmap.symm ▸ hx
    obtain ⟨y, hy, he⟩ := hx'
    exact b.injective he ▸ hy
  · intro hx
    rw [← hmap]
    exact mem_map_of_mem b.toMonoidHom hx

end Subgroup
