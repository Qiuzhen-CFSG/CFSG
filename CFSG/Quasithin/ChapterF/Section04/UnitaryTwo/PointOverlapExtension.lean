module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointOverlapDetection
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import Theory.GroupTheory.IndexTwoOverlapEquivalence

/-!
# Extending the marked ordinary unitary point map

The ordinary point parabolic is the index-two kernel of the outer coordinate
in the literal extended point group. A compatible map of the full overlap
therefore extends a marked ordinary point equivalence: the ordinary overlap
detects its conjugation action, and the outside element's square is already
in the common subgroup. The resulting map retains both original inclusions.

This supplies the point-endpoint extension in the doubled branch of
Aschbacher--Smith 13.5.17, printed p.922.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointOverlapExtension
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "EP" => Extension.point 1 hn
local notation "EB" => Subgroup.subgroupOf (Extension.overlap 1 hn) EP
local notation "B" => Subgroup.subgroupOf (overlap 1 hn) P

/-- The original point group inside the literal graph extension. -/
def ordinaryPoint : Subgroup EP :=
  (SemidirectProduct.rightHom.comp (EP).subtype).ker

instance ordinaryPoint_normal : ordinaryPoint.Normal := MonoidHom.normal_ker _

/-- The literal inclusion identifies the original point endpoint with the
kernel of the outer coordinate. -/
def ordinaryPointEquiv : P ≃* ordinaryPoint where
  toFun p := ⟨⟨SemidirectProduct.inl p.val,
    (Extension.mem_point 1 hn _).mpr p.property⟩, rfl⟩
  invFun p := ⟨p.val.val.left, (Extension.mem_point 1 hn _).mp p.val.property⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact p.property.symm
  map_mul' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact SemidirectProduct.inl.map_mul p.val q.val

theorem ordinaryPoint_index : ordinaryPoint.index = 2 := by
  have h := ordinaryPoint.card_mul_index
  rw [← Nat.card_congr ordinaryPointEquiv.toEquiv,
    BinaryCompletion.point_card, Extension.binary_point_card] at h
  omega

/-- The marking here uses the original flag subgroup, with its actual
semidirect-product inclusion. -/
theorem ordinaryPoint_mem_overlap (p : P) :
    (ordinaryPointEquiv p : EP) ∈ EB ↔ p ∈ B := by
  change SemidirectProduct.inl p.val ∈ Extension.overlap 1 hn ↔ _
  exact Extension.binary_mem_overlap _

/-- The point detector transports through a marked equivalence of the
ordinary endpoint. -/
theorem eq_of_eq_on_marked_overlap
    {G : Type*} [Group G] (N D : Subgroup G) (eP : N ≃* P)
    (hmark : ∀ n : N, eP n ∈ B → (n : G) ∈ D)
    (α β : MulAut N) (h : ∀ n : N, (n : G) ∈ D → α n = β n) : α = β := by
  have he : ((eP.symm.trans α).trans eP) = ((eP.symm.trans β).trans eP) :=
    PointOverlapDetection.eq_of_eq_on_overlap _ _ (by
      intro x hx
      change eP (α (eP.symm x)) = eP (β (eP.symm x))
      apply congrArg eP
      exact h _ (hmark _ (by simpa only [eP.apply_symm_apply] using hx)))
  apply MulEquiv.ext
  intro n
  apply eP.injective
  have hh := DFunLike.congr_fun he (eP n)
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hh

/-- Compatibility and the ordinary overlap marking detect the outside coset
on the target side as well. -/
theorem outside_of_compatible_overlap
    {G : Type*} [Group G] (N D : Subgroup G)
    (eP : N ≃* P) (eB : D ≃* EB)
    (hmark : ∀ n : N, eP n ∈ B → (n : G) ∈ D)
    (hcompat : ∀ (n : N) (hnD : (n : G) ∈ D),
      (ordinaryPointEquiv (eP n) : EP) = (eB ⟨n, hnD⟩ : EP))
    (a : D) (ha : (a : G) ∉ N) : (eB a : EP) ∉ ordinaryPoint := by
  intro ha'
  let n : N := eP.symm (ordinaryPointEquiv.symm ⟨eB a, ha'⟩)
  have he : (ordinaryPointEquiv (eP n) : EP) = (eB a : EP) := by
    simp only [n, eP.apply_symm_apply, ordinaryPointEquiv.apply_symm_apply]
  have hnD : (n : G) ∈ D := hmark n
    ((ordinaryPoint_mem_overlap (eP n)).mp (he.symm ▸ (eB a).property))
  have hh : (⟨(n : G), hnD⟩ : D) = a :=
    eB.injective (Subtype.ext ((hcompat n hnD).symm.trans he))
  have heq : (n : G) = (a : G) := congrArg Subtype.val hh
  exact ha (heq ▸ n.property)

/-- A compatible full-overlap map extends the marked ordinary point map to
the actual extended point endpoint and preserves the whole overlap square. -/
theorem exists_extension_to_graph_point
    {G : Type*} [Group G] (N D : Subgroup G) [N.Normal]
    (hi : N.index = 2) (eP : N ≃* P) (eB : D ≃* EB)
    (hmark : ∀ n : N, eP n ∈ B → (n : G) ∈ D)
    (hcompat : ∀ (n : N) (hnD : (n : G) ∈ D),
      (ordinaryPointEquiv (eP n) : EP) = (eB ⟨n, hnD⟩ : EP))
    (a : D) (ha : (a : G) ∉ N) :
    ∃ e : G ≃* EP,
      (∀ n : N, e n = (ordinaryPointEquiv (eP n) : EP)) ∧
      (∀ b : D, e b = (eB b : EP)) :=
  exists_mulEquiv_of_index_two_overlap N ordinaryPoint hi ordinaryPoint_index
    D EB (eP.trans ordinaryPointEquiv) eB hcompat
    (eq_of_eq_on_marked_overlap N D eP hmark) a ha
    (outside_of_compatible_overlap N D eP eB hmark hcompat a ha)

end CFSG.Quasithin.ChapterF.UnitaryTwo.PointOverlapExtension
