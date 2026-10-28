module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models

/-!
# Trivial intersection of the intrinsic root four-subgroups

The marked E₄ × A₅ model suffices for the TI assertion of Aschbacher,
*Sporadic Groups* (1994), 47.1(1), pp.259–260. A nonidentity element of
the E₄ factor is in the second involution class. Its centralizer contains
the original centralizer and has the same order, so the two centralizers
are equal. Their intrinsic two-cores are therefore equal as well.

Applying this argument to a nontrivial intersection with a conjugate proves
TI. The proof does not assert that the fixed z belongs to the component of
every conjugate centralizer. The marked model remains an explicit input.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_map (t : G) (e : G ≃* G) :
    (involutionCentralizer t).map e.toMonoidHom = involutionCentralizer (e t) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({t} : Set G) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp hx

omit [Finite G] in
/-- Embedded intrinsic cores commute with the actual automorphism of the ambient group. -/
theorem rootCore_map (t : G) (e : G ≃* G) :
    (rootCore t).map e.toMonoidHom = rootCore (e t) := by
  let H := involutionCentralizer t
  let f := H.equivMapOfInjective e.toMonoidHom e.injective
  have hf := pCore_map_iso 2 f
  calc
    _ = ((pCore 2 H).map f.toMonoidHom).map (H.map e.toMonoidHom).subtype := by
      rw [map_map, rootCore, pCoreIn, map_map]
      rfl
    _ = (H.map e.toMonoidHom).pCoreIn 2 := by rw [hf]; rfl
    _ = rootCore (e t) := by rw [centralizer_map]; rfl

omit [Finite G] in
private theorem centralizer_card_of_isConj {t u : G} (h : IsConj t u) :
    Nat.card (involutionCentralizer t) = Nat.card (involutionCentralizer u) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he := centralizer_map t (MulAut.conj g)
  rw [show MulAut.conj g t = u from hg] at he
  rw [← he, card_map_of_injective (MulAut.conj g).injective]

namespace SecondCentralizer
variable {D : Seed G} {t : G} (C : SecondCentralizer D t)

include C in
/-- The embedded core is central in the full centralizer, as the E₄ factor is. -/
theorem centralizer_le_core_centralizer :
    involutionCentralizer t ≤ centralizer (rootCore t : Set G) := by
  intro a ha u hu
  have huK := pCoreIn_le 2 (involutionCentralizer t) hu
  let aK : involutionCentralizer t := ⟨a, ha⟩
  let uK : involutionCentralizer t := ⟨u, huK⟩
  have hu2 := (C.mem_rootCore_iff uK).mp hu
  have hc : uK * aK = aK * uK := by
    apply C.equiv.injective
    simp only [map_mul]
    apply Prod.ext
    · exact mul_comm _ _
    · change (C.equiv uK).2 * (C.equiv aK).2 = (C.equiv aK).2 * (C.equiv uK).2
      rw [hu2, one_mul, mul_one]
  exact congrArg Subtype.val hc

include C in
/-- Every nonidentity root-core element is an involution of the second class. -/
theorem other_of_mem_rootCore {u : G} (hu : u ∈ rootCore t) (hne : u ≠ 1) :
    OtherInvolution D u := by
  have huK := pCoreIn_le 2 (involutionCentralizer t) hu
  let uK : involutionCentralizer t := ⟨u, huK⟩
  have hu2 := (C.mem_rootCore_iff uK).mp hu
  have hu1 : (C.equiv uK).1 ≠ 1 := by
    intro h
    have he : C.equiv uK = 1 := Prod.ext h hu2
    have huone : uK = 1 := C.equiv.injective (he.trans (map_one C.equiv).symm)
    exact hne (congrArg Subtype.val huone)
  have hsquare : ∀ a : E4, a ^ 2 = 1 := by decide +kernel
  have horder : orderOf uK = 2 := by
    apply orderOf_eq_prime
    · apply C.equiv.injective
      rw [map_pow, map_one]
      exact Prod.ext (hsquare _) (by simp [hu2])
    · exact fun h => hne (congrArg Subtype.val h)
  exact ⟨(orderOf_coe uK).trans horder, fun h => hu1 ((C.fusion uK horder).mp h)⟩

include C in
/-- A nonidentity root-core element has exactly the original centralizer. -/
theorem centralizer_eq_of_mem_rootCore (ht : OtherInvolution D t)
    {u : G} (hu : u ∈ rootCore t) (hne : u ≠ 1) :
    involutionCentralizer u = involutionCentralizer t := by
  have hother := C.other_of_mem_rootCore hu hne
  have hle : involutionCentralizer t ≤ involutionCentralizer u := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (C.centralizer_le_core_centralizer ha u hu).symm
  exact (eq_of_le_of_card_ge hle
    (centralizer_card_of_isConj (ht.isConj hother)).symm.le).symm

include C in
/-- The TI property of the actual ambient image of O₂(C_G(t)). -/
theorem rootCore_trivial_intersection (ht : OtherInvolution D t) (g : G) :
    rootCore t ⊓ (rootCore t).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (rootCore t).map (MulAut.conj g).toMonoidHom = rootCore t := by
  classical
  by_cases hd : rootCore t ⊓ (rootCore t).map (MulAut.conj g).toMonoidHom = ⊥
  · exact Or.inl hd
  right
  obtain ⟨u, hu, hne⟩ := (rootCore t ⊓
    (rootCore t).map (MulAut.conj g).toMonoidHom).bot_or_exists_ne_one.resolve_left hd
  obtain ⟨v, hv, hvu⟩ := hu.2
  have hvne : v ≠ 1 := by
    intro h
    apply hne
    rw [← hvu, h, map_one]
  have hCu := C.centralizer_eq_of_mem_rootCore ht hu.1 hne
  have hCv := C.centralizer_eq_of_mem_rootCore ht hv hvne
  have hmap := centralizer_map v (MulAut.conj g)
  rw [show MulAut.conj g v = u from hvu, hCu, hCv] at hmap
  have htconj : involutionCentralizer (MulAut.conj g t) = involutionCentralizer t :=
    (centralizer_map t (MulAut.conj g)).symm.trans hmap
  rw [rootCore_map]
  change (involutionCentralizer (MulAut.conj g t)).pCoreIn 2 =
    (involutionCentralizer t).pCoreIn 2
  rw [htconj]

end SecondCentralizer
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
