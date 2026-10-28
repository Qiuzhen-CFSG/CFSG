module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionTypes

/-!
# Irreducible normalizer conjugates and ambient subgroup intersections

An invariant subgroup pulls through the marked multiplicative coordinates
to a binary subrepresentation. Irreducibility makes it trivial or the whole
constituent. Pullback by inverse normalizer conjugation preserves this
minimality. Thus an escaping conjugate has zero intersection with any
normalized submodule that does not contain it.

The actual chosen-seed application is `SeedAlternativesMovedExhaustionDisjoint`.
This is the irreducible-copy geometry used after D.3.11, before the cubic
multiplicity argument in D.3.12--19; it does not bound the number of copies.
Source: Aschbacher--Smith, printed pp.201--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G P W : Type*} [Group G] [Group P]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A normalized subgroup of an irreducible marked conjugation module is
trivial or the whole module, with the actual ambient inclusion retained. -/
theorem ConjugationCoordinates.invariant_subgroup_eq
    {L V : Subgroup G} {τ : Representation (ZMod 2) P W} {f : L →* P}
    (c : ConjugationCoordinates L V τ f) (hirr : IsIrreducible (τ.comp f))
    (J : Subgroup G) (hJV : J ≤ V) (hLJ : L ≤ normalizer (J : Set G)) :
    J = ⊥ ∨ J = V := by
  let A := (J.subgroupOf V).map c.equiv.toMonoidHom
  let S : Subrepresentation (τ.comp f) := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 A.toAddSubgroup
    apply_mem_toSubmodule := by
      intro l w hw
      change Multiplicative.ofAdd w ∈ A at hw
      obtain ⟨v,hv,hcv⟩ := hw
      let z : V := ⟨l.val * v.val * l.val⁻¹,
        (mem_normalizer_iff.mp (c.normalizes l.property) _).mp v.property⟩
      have hz : z ∈ J.subgroupOf V :=
        (mem_normalizer_iff.mp (hLJ l.property) _).mp hv
      change Multiplicative.ofAdd (τ (f l) w) ∈ A
      refine ⟨z,hz,?_⟩
      apply Multiplicative.toAdd.injective
      change (c.equiv z).toAdd = τ (f l) w
      rw [c.intertwines l v z rfl]
      exact congrArg (τ (f l)) (congrArg Multiplicative.toAdd hcv) }
  rcases hirr.eq_bot_or_eq_top S with hb | ht
  · left
    apply bot_unique
    intro x hx
    let v : V := ⟨x,hJV hx⟩
    have hm : (c.equiv v).toAdd ∈ S := mem_map_of_mem c.equiv.toMonoidHom (show v ∈ J.subgroupOf V from hx)
    rw [hb] at hm
    have hv : c.equiv v = 1 := Multiplicative.toAdd.injective hm
    exact mem_bot.mpr (congrArg Subtype.val
      (c.equiv.injective (hv.trans (map_one c.equiv).symm)))
  · right
    apply le_antisymm hJV
    intro x hx
    let v : V := ⟨x,hx⟩
    have hm : (c.equiv v).toAdd ∈ S := by rw [ht]; trivial
    obtain ⟨w,hw,he⟩ : ∃ w ∈ J.subgroupOf V, c.equiv w = c.equiv v := hm
    have hv : v ∈ J.subgroupOf V := c.equiv.injective he ▸ hw
    exact hv

/-- Invariant-subgroup minimality transports through the original normalizer
conjugation map, without replacing the acting component. -/
theorem invariant_conjugate_subgroup_eq
    {L V : Subgroup G}
    (hmin : ∀ J : Subgroup G, J ≤ V → L ≤ normalizer (J : Set G) → J = ⊥ ∨ J = V)
    (g : normalizer (L : Set G)) (J : Subgroup G)
    (hJV : J ≤ V.map (MulAut.conj g.val).toMonoidHom)
    (hLJ : L ≤ normalizer (J : Set G)) :
    J = ⊥ ∨ J = V.map (MulAut.conj g.val).toMonoidHom := by
  let K := J.map (MulAut.conj g.val⁻¹).toMonoidHom
  have hK : K ≤ V := by
    have hh := map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hJV
    rw [map_conj_map_conj,inv_mul_cancel,map_one] at hh
    change K ≤ V.map (MonoidHom.id G) at hh
    simpa only [Subgroup.map_id] using hh
  have hLK : L ≤ normalizer (K : Set G) := by
    rw [←map_equiv_normalizer_eq J (MulAut.conj g.val⁻¹)]
    exact (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (L : Set G)).inv_mem g.property)).ge.trans (map_mono hLJ)
  have hback : K.map (MulAut.conj g.val).toMonoidHom = J := by
    rw [show K = J.map (MulAut.conj g.val⁻¹).toMonoidHom from rfl,
      map_conj_map_conj,mul_inv_cancel,map_one]
    exact Subgroup.map_id J
  rcases hmin K hK hLK with hb | ht
  · left
    simpa only [hb,Subgroup.map_bot] using hback.symm
  · right
    exact hback.symm.trans (congrArg (fun X : Subgroup G =>
      X.map (MulAut.conj g.val).toMonoidHom) ht)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

