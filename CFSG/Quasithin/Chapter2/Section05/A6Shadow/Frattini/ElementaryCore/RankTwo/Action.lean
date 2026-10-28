module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Families
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryPair
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Centralizers in the actual Sylow action

The faithful action on S ∩ K detects commutation with its subgroups.
The two four-group centralizers in S are consequently the full preimages
of the marked elementary eight-groups in Aut(A₆). Kernel-image counting
and a lift of the model rotation give their orders and an actual conjugator
in S, without elementary-core or rank assumptions.

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568. The finite
centralizer calculations use the checked cyclic-eight holomorph model.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

noncomputable def preimage (V : Subgroup d.imageSylow) : Subgroup G :=
  (V.comap d.toImageSylow).map d.S.subtype

theorem preimage_le (V : Subgroup d.imageSylow) : preimage d V ≤ d.S := by
  exact (map_le_range _ _).trans_eq d.S.range_subtype

theorem mem_preimage (V : Subgroup d.imageSylow) (s : d.S) :
    (s : G) ∈ preimage d V ↔ d.toImageSylow s ∈ V := by
  constructor
  · rintro ⟨t, ht, he⟩
    exact d.S.subtype_injective he ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

theorem mem_imageInner (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (a : d.imageSylow) :
    a ∈ imageInner d E ↔ ∃ e : E, d.toImageSylow ⟨e, (hE e.property).1⟩ = a := by
  constructor
  · rintro ⟨b, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨innerEquiv d ⟨e, hE e.property⟩, ⟨⟨e, hE e.property⟩, e.property, rfl⟩, rfl⟩

private theorem action_commutes_iff (h : d.H) (k : d.K) :
    Commute (d.action h) (MulAut.conj (d.modelK k)) ↔
      Commute (h : G) (k : G) := by
  change d.action h * MulAut.conj (d.modelK k) =
    MulAut.conj (d.modelK k) * d.action h ↔ _
  rw [← mul_inv_eq_iff_eq_mul, aut_conj_inner, inner_injective.eq_iff]
  constructor
  · intro he
    have hv := d.action_compatible h k
    rw [he, d.modelK.symm_apply_apply] at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv.symm)
  · intro hc
    apply d.modelK.symm.injective
    apply Subtype.ext
    rw [d.action_compatible, d.modelK.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr hc.eq

theorem centralizer_preimage (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) :
    d.S ⊓ centralizer (E : Set G) =
      preimage d (centralizer (imageInner d E : Set d.imageSylow)) := by
  apply le_antisymm
  · intro s hs
    apply (mem_preimage d _ ⟨s, hs.1⟩).mpr
    intro a ha
    obtain ⟨e, rfl⟩ := (mem_imageInner d E hE a).mp ha
    apply Subtype.ext
    change d.action ⟨e, d.s_le_h (hE e.property).1⟩ * d.action ⟨s, d.s_le_h hs.1⟩ =
      d.action ⟨s, d.s_le_h hs.1⟩ * d.action ⟨e, d.s_le_h (hE e.property).1⟩
    rw [d.action_on_K ⟨e, (hE e.property).2⟩]
    exact ((action_commutes_iff d ⟨s, d.s_le_h hs.1⟩ ⟨e, (hE e.property).2⟩).mpr
      (hs.2 e e.property).symm).eq.symm
  · intro s hs
    have hsS := preimage_le d _ hs
    refine ⟨hsS, ?_⟩
    have hc := (mem_preimage d _ ⟨s, hsS⟩).mp hs
    intro e he
    have heI : d.toImageSylow ⟨e, (hE he).1⟩ ∈ imageInner d E :=
      (mem_imageInner d E hE _).mpr ⟨⟨e, he⟩, rfl⟩
    have hh := congrArg Subtype.val (hc _ heI)
    change d.action ⟨e, d.s_le_h (hE he).1⟩ * d.action ⟨s, d.s_le_h hsS⟩ =
      d.action ⟨s, d.s_le_h hsS⟩ * d.action ⟨e, d.s_le_h (hE he).1⟩ at hh
    rw [d.action_on_K ⟨e, (hE he).2⟩] at hh
    exact ((action_commutes_iff d ⟨s, d.s_le_h hsS⟩ ⟨e, (hE he).2⟩).mp hh.symm).eq.symm

private theorem model_centralizer_zero :
    centralizer (Holomorph.kleinZero : Set Holomorph.Model) = Holomorph.ElementaryPair.zero := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, Holomorph.mem_kleinZero,
    Holomorph.ElementaryPair.zero, MonoidHom.mem_range]
  revert x
  decide +kernel

private theorem model_centralizer_one :
    centralizer (Holomorph.kleinOne : Set Holomorph.Model) = Holomorph.ElementaryPair.one := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, Holomorph.mem_kleinOne,
    Holomorph.ElementaryPair.one, MonoidHom.mem_range]
  revert x
  decide +kernel

private theorem map_centralizer {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (U : Subgroup A) :
    (centralizer (U : Set A)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set B) := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hx y hy
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx y (by simpa using hy))
  · intro hx y hy
    apply e.injective
    simpa only [map_mul] using hx (e y) (by simpa using hy)

theorem centralizer_fourZero :
    d.S ⊓ centralizer (fourZero d : Set G) = preimage d (ElementaryPair.zero d.imageSylow) := by
  rw [centralizer_preimage d _ (fourZero_le d)]
  change preimage d (centralizer (imageInner d (liftInner d _) : Set d.imageSylow)) = _
  rw [imageInner_liftInner d _ (SylowGeometry.kleinZero_le_inner d.imageSylow)]
  congr 1
  rw [SylowGeometry.kleinZero, ← map_centralizer, model_centralizer_zero]
  rfl

theorem centralizer_fourOne :
    d.S ⊓ centralizer (fourOne d : Set G) = preimage d (ElementaryPair.one d.imageSylow) := by
  rw [centralizer_preimage d _ (fourOne_le d)]
  change preimage d (centralizer (imageInner d (liftInner d _) : Set d.imageSylow)) = _
  rw [imageInner_liftInner d _ (SylowGeometry.kleinOne_le_inner d.imageSylow)]
  congr 1
  rw [SylowGeometry.kleinOne, ← map_centralizer, model_centralizer_one]
  rfl

theorem card_preimage (V : Subgroup d.imageSylow) :
    Nat.card (preimage d V) = Nat.card d.SC * Nat.card V := by
  rw [preimage, card_map_of_injective d.S.subtype_injective]
  have hker : d.toImageSylow.ker ≤ V.comap d.toImageSylow := by
    intro s hs
    change d.toImageSylow s ∈ V
    rw [MonoidHom.mem_ker.mp hs]
    exact V.one_mem
  have hc := (d.toImageSylow.ker.subgroupOf (V.comap d.toImageSylow)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv] at hc
  change Nat.card d.toImageSylow.ker *
    d.toImageSylow.ker.relIndex (V.comap d.toImageSylow) = _ at hc
  rw [relIndex_ker, map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr (toImageSylow_surjective d)]; exact le_top),
    d.toImageSylow_kernel,
    Nat.card_congr (subgroupOfEquivOfLe d.sc_le_s).toEquiv] at hc
  exact hc.symm

theorem card_centralizer_fourZero (hcard : Nat.card d.SC = 4) :
    Nat.card (d.S ⊓ centralizer (fourZero d : Set G) : Subgroup G) = 32 := by
  rw [centralizer_fourZero, card_preimage, hcard, ElementaryPair.card_zero]

theorem card_centralizer_fourOne (hcard : Nat.card d.SC = 4) :
    Nat.card (d.S ⊓ centralizer (fourOne d : Set G) : Subgroup G) = 32 := by
  rw [centralizer_fourOne, card_preimage, hcard, ElementaryPair.card_one]

theorem conjugate_preimage (V : Subgroup d.imageSylow) (s : d.S) :
    rightConjugate (s : G) (preimage d V) =
      preimage d (V.map (MulAut.conj ((d.toImageSylow s)⁻¹)).toMonoidHom) := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgS := preimage_le d V hg
    have ht : ((s : G)⁻¹ * g * s) ∈ d.S :=
      d.S.mul_mem (d.S.mul_mem (d.S.inv_mem s.property) hgS) s.property
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    apply (mem_preimage d _ ⟨_, ht⟩).mpr
    refine ⟨d.toImageSylow ⟨g, hgS⟩, (mem_preimage d V ⟨g, hgS⟩).mp hg, ?_⟩
    change (d.toImageSylow s)⁻¹ * d.toImageSylow ⟨g, hgS⟩ * d.toImageSylow s = _
    simpa only [map_mul, map_inv] using
      (show d.toImageSylow (s⁻¹ * ⟨g, hgS⟩ * s) = d.toImageSylow ⟨_, ht⟩ from rfl)
  · intro hg
    have hgS := preimage_le d _ hg
    have hm := (mem_preimage d _ ⟨g, hgS⟩).mp hg
    rw [mem_map_equiv] at hm
    have ht : ((s : G) * g * (s : G)⁻¹) ∈ d.S :=
      d.S.mul_mem (d.S.mul_mem s.property hgS) (d.S.inv_mem s.property)
    refine ⟨(s : G) * g * (s : G)⁻¹, ?_, ?_⟩
    · apply (mem_preimage d V ⟨_, ht⟩).mpr
      change d.toImageSylow (s * ⟨g, hgS⟩ * s⁻¹) ∈ V
      simpa [MulAut.conj_symm_apply] using hm
    · simp [mul_assoc]

theorem centralizers_conjugate : ∃ s ∈ d.S,
    rightConjugate s (d.S ⊓ centralizer (fourZero d : Set G)) =
      d.S ⊓ centralizer (fourOne d : Set G) := by
  obtain ⟨s, hs⟩ := toImageSylow_surjective d
    (Identification.sylowEquiv d.imageSylow Holomorph.rotation)⁻¹
  refine ⟨s, s.property, ?_⟩
  rw [centralizer_fourZero, centralizer_fourOne, conjugate_preimage, hs, inv_inv,
    ElementaryPair.rotation_conjugates]

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
