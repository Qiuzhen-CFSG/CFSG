module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Conjugation
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Counting
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Reductions
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The two-root plane and the symplectic counting set

Multiplication coordinates on `V = C × W`, together with an actual symplectic
model on the component, define the set β in the proof of 16.5.13. Its elements
have nontrivial C coordinate and either zero W coordinate or nonzero coordinates
on both central root groups. Counting this explicit set gives
`((q - 1)^2 + 1) * (r - 1)`. The genuine Δ₀ detector and uniform exclusion of
root projections then put the punctured union of the C-conjugates in β.

The source configuration and the root-plane coordinates are separate construction
obligations; the structures below specify multiplication and actual matrix
identities, without asserting those obligations or the source exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.5.13, printed p.1202. Conjugation is left conjugation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic
open Subgroup
open scoped Pointwise
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
variable {G : Type*} [Group G]
variable {F : Type*} [Field F]

/-- Root membership through an actual symplectic model, including conjugates
of both root lengths. -/
def IsModelRoot {L : Subgroup G} (eL : L ≃* Sp F) (w : G) : Prop :=
  ∃ hw : w ∈ L, InvolutionTypes.IsRootElement (eL ⟨w, hw⟩)

/-- Coordinates on the two central root groups. The displayed equation
anchors the coordinates to the actual matrices, not a family label. -/
structure RootPlane (L W : Subgroup G) (eL : L ≃* Sp F) where
  le_component : W ≤ L
  coordinates : W ≃* (Multiplicative F × Multiplicative F)
  model_eq : ∀ w : W, eL ⟨w, le_component w.property⟩ =
    rootElement 0 (coordinates w).1.toAdd * rootElement 4 (coordinates w).2.toAdd

/-- Actual multiplication coordinates on V = C × W. -/
structure Splitting (V C W : Subgroup G) where
  equiv : V ≃* C × W
  multiply : ∀ x : V, (x : G) = ((equiv x).1 : G) * ((equiv x).2 : G)

namespace Splitting
variable {V C W : Subgroup G}

theorem exists_of_product (hV : V = C ⊔ W) (hd : Disjoint C W)
    (hc : C ≤ centralizer (W : Set G)) : Nonempty (Splitting V C W) := by
  subst V
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C W hd hc
  refine ⟨⟨e.symm, fun x => ?_⟩⟩
  exact (congrArg Subtype.val (e.apply_symm_apply x)).symm.trans (he _ _)

theorem mem_right_iff (d : Splitting V C W) (hd : Disjoint C W) (x : V) :
    (x : G) ∈ W ↔ (d.equiv x).1 = 1 := by
  constructor
  · intro hx
    have hc : ((d.equiv x).1 : G) ∈ W := by
      have hh := W.mul_mem hx (W.inv_mem (d.equiv x).2.property)
      simpa only [d.multiply x, mul_inv_cancel_right] using hh
    exact Subtype.ext (Subgroup.disjoint_def.mp hd (d.equiv x).1.property hc)
  · intro hx
    simpa only [d.multiply x, hx, OneMemClass.coe_one, one_mul] using (d.equiv x).2.property

theorem mem_left_iff (d : Splitting V C W) (hd : Disjoint C W) (x : V) :
    (x : G) ∈ C ↔ (d.equiv x).2 = 1 := by
  constructor
  · intro hx
    have hw : ((d.equiv x).2 : G) ∈ C := by
      have hh := C.mul_mem (C.inv_mem (d.equiv x).1.property) hx
      simpa only [d.multiply x, inv_mul_cancel_left] using hh
    exact Subtype.ext (Subgroup.disjoint_def.mp hd hw (d.equiv x).2.property)
  · intro hx
    simpa only [d.multiply x, hx, OneMemClass.coe_one, mul_one] using (d.equiv x).1.property

/-- Both factors really are subgroups of the coordinate domain. -/
theorem left_le (d : Splitting V C W) : C ≤ V := by
  intro c hc
  have h := d.multiply (d.equiv.symm (⟨c, hc⟩, 1))
  have hh := (d.equiv.symm (⟨c, hc⟩, 1)).property
  simpa only [h, MulEquiv.apply_symm_apply, OneMemClass.coe_one, mul_one] using hh

theorem right_le (d : Splitting V C W) : W ≤ V := by
  intro w hw
  have h := d.multiply (d.equiv.symm (1, ⟨w, hw⟩))
  have hh := (d.equiv.symm (1, ⟨w, hw⟩)).property
  simpa only [h, MulEquiv.apply_symm_apply, OneMemClass.coe_one, one_mul] using hh

end Splitting

namespace RootPlane
variable {L W : Subgroup G} {eL : L ≃* Sp F}

theorem root_of_axis (p : RootPlane L W eL) (w : W) (hw : w ≠ 1)
    (haxis : (p.coordinates w).1 = 1 ∨ (p.coordinates w).2 = 1) :
    IsModelRoot eL (w : G) := by
  refine ⟨p.le_component w.property, ?_⟩
  have hne : p.coordinates w ≠ 1 := fun h => hw (p.coordinates.injective
    (h.trans (map_one p.coordinates).symm))
  rw [p.model_eq]
  rcases haxis with h | h
  · have hn : (p.coordinates w).2.toAdd ≠ 0 := by
      intro hz
      apply hne
      exact Prod.ext h (congrArg Multiplicative.ofAdd hz)
    rw [h]
    change InvolutionTypes.IsRootElement (rootElement 0 0 * rootElement 4 _ )
    rw [RootSubgroup.element_zero, one_mul]
    exact ⟨1, 4, _, hn, by simp⟩
  · have hn : (p.coordinates w).1.toAdd ≠ 0 := by
      intro hz
      apply hne
      exact Prod.ext (congrArg Multiplicative.ofAdd hz) h
    rw [h]
    change InvolutionTypes.IsRootElement (rootElement 0 _ * rootElement 4 0)
    rw [RootSubgroup.element_zero, mul_one]
    exact ⟨1, 0, _, hn, by simp⟩

end RootPlane

section Counting
variable [Finite G] [Fintype F]

/-- The allowed central projections: zero, or nonzero on both root axes. -/
noncomputable def allowedProjections : Finset (Multiplicative F × Multiplicative F) :=
  letI := Classical.decEq (Multiplicative F)
  insert 1 ((Finset.univ.erase 1) ×ˢ (Finset.univ.erase 1))

theorem mem_allowedProjections (a : Multiplicative F × Multiplicative F) :
    a ∈ allowedProjections (F := F) ↔ a = 1 ∨ (a.1 ≠ 1 ∧ a.2 ≠ 1) := by
  classical
  simp [allowedProjections]

theorem card_allowedProjections :
    (allowedProjections (F := F)).card = (Nat.card F - 1)^2 + 1 := by
  classical
  rw [allowedProjections, Finset.card_insert_of_notMem (by simp)]
  simp [Finset.card_product, pow_two, Nat.card_eq_fintype_card]

/-- The actual subset β of the ambient group, obtained from multiplication
coordinates. Nonidentity in C is precisely the condition of lying outside W. -/
noncomputable def beta {V C W L : Subgroup G} {eL : L ≃* Sp F}
    (d : Splitting V C W) (p : RootPlane L W eL) : Finset G := by
  classical
  letI := Fintype.ofFinite C
  let e : V ≃ C × (Multiplicative F × Multiplicative F) :=
    (d.equiv.trans ((MulEquiv.refl C).prodCongr p.coordinates)).toEquiv
  exact (((Finset.univ.erase (1 : C)) ×ˢ allowedProjections (F := F)).map
    (e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩))

theorem card_beta {V C W L : Subgroup G} {eL : L ≃* Sp F}
    (d : Splitting V C W) (p : RootPlane L W eL) :
    (beta d p).card = ((Nat.card F - 1)^2 + 1) * (Nat.card C - 1) := by
  classical
  simp only [beta, Finset.card_map, Finset.card_product]
  rw [card_allowedProjections]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [@Nat.card_eq_fintype_card C (Fintype.ofFinite C)]
  exact mul_comm _ _

theorem mem_beta {V C W L : Subgroup G} {eL : L ≃* Sp F}
    (d : Splitting V C W) (p : RootPlane L W eL) (x : V) :
    (x : G) ∈ beta d p ↔
      (d.equiv x).1 ≠ 1 ∧
      p.coordinates (d.equiv x).2 ∈ allowedProjections (F := F) := by
  classical
  simp only [beta, Finset.mem_map, Finset.mem_product, Finset.mem_erase,
    Finset.mem_univ, and_true, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, ⟨ha, hp⟩, he⟩
    have hh := congrArg (fun x : V =>
      (d.equiv.trans ((MulEquiv.refl C).prodCongr p.coordinates)) x)
      (Subtype.ext he)
    have hh' : a = ((d.equiv x).1, p.coordinates (d.equiv x).2) := by
      simpa [MulEquiv.prodCongr, Prod.map_def] using hh
    cases hh'
    exact ⟨ha, hp⟩
  · rintro ⟨ha, hp⟩
    refine ⟨((d.equiv x).1, p.coordinates (d.equiv x).2), ⟨ha, hp⟩, ?_⟩
    exact congrArg Subtype.val
      ((d.equiv.trans ((MulEquiv.refl C).prodCongr p.coordinates)).symm_apply_apply x)

section Specification
variable {V C W L : Subgroup G} {eL : L ≃* Sp F}

theorem beta_subset (d : Splitting V C W) (p : RootPlane L W eL)
    {x : G} (hx : x ∈ beta d p) : x ∈ V := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  exact (d.equiv.trans ((MulEquiv.refl C).prodCongr p.coordinates)).symm a |>.property

/-- With the source elementary-abelian V, the coordinate construction is
exactly its set of involutions outside W that lie in C or project off both axes. -/
theorem mem_beta_source_iff (d : Splitting V C W) (p : RootPlane L W eL)
    (hd : Disjoint C W) (hV2 : ∀ x ∈ V, x ^ 2 = 1) (x : G) :
    x ∈ beta d p ↔ orderOf x = 2 ∧ ∃ hx : x ∈ V,
      x ∉ W ∧ (x ∈ C ∨
        ((p.coordinates (d.equiv ⟨x, hx⟩).2).1 ≠ 1 ∧
         (p.coordinates (d.equiv ⟨x, hx⟩).2).2 ≠ 1)) := by
  constructor
  · intro hx
    have hxV := beta_subset d p hx
    have hh := (mem_beta d p ⟨x, hxV⟩).mp hx
    have hxW : x ∉ W := fun h => hh.1 ((d.mem_right_iff hd _).mp h)
    refine ⟨orderOf_eq_prime (hV2 x hxV) (fun h => hxW (h ▸ W.one_mem)),
      hxV, hxW, ?_⟩
    rcases (mem_allowedProjections _).mp hh.2 with hz | hz
    · exact Or.inl ((d.mem_left_iff hd _).mpr
        (p.coordinates.injective (hz.trans (map_one p.coordinates).symm)))
    · exact Or.inr hz
  · rintro ⟨_, hxV, hxW, hx⟩
    apply (mem_beta d p ⟨x, hxV⟩).mpr
    refine ⟨fun h => hxW ((d.mem_right_iff hd _).mpr h), ?_⟩
    rw [mem_allowedProjections]
    rcases hx with hx | hx
    · exact Or.inl (by rw [(d.mem_left_iff hd _).mp hx, map_one])
    · exact Or.inr hx
end Specification

omit [Finite G] in
/-- Disjointness persists under the whole normalizer because W is invariant. -/
theorem disjoint_conjugate_right {C W : Subgroup G} (hd : Disjoint C W)
    {a : G} (ha : a ∈ normalizer (W : Set G)) : Disjoint (C.conjBy a) W := by
  have hh := Subgroup.disjoint_map (f := (MulAut.conj a).toMonoidHom)
    (MulAut.conj a).injective hd
  change Disjoint (C.conjBy a) (W.map (MulAut.conj a).toMonoidHom) at hh
  rwa [MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp ha] at hh

/-- The detector and uniform root exclusion place every nonidentity element
of every conjugate of C in the explicitly counted set β. -/
theorem conjugate_mem_beta {V C W L M : Subgroup G} {eL : L ≃* Sp F}
    (d : Splitting V C W) (p : RootPlane L W eL)
    (hd : Disjoint C W) (hLK : Disjoint L (centralizer (L : Set G)))
    (hCK : C ≤ centralizer (L : Set G))
    (hC2 : ∀ c ∈ C, c ^ 2 = 1)
    (hMV : M ≤ normalizer (V : Set G))
    (hMW : M ≤ normalizer (W : Set G))
    (hdetect : ∀ J : Subgroup G,
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
      i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
      J ∈ deltaZero L)
    (havoid : ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsModelRoot eL w)
    {a x : G} (ha : a ∈ M) (hx : x ∈ C.conjBy a) (hne : x ≠ 1) :
    x ∈ beta d p := by
  have hxV : x ∈ V := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) d.left_le hx
    rwa [MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp (hMV ha)] at hh
  let v : V := ⟨x, hxV⟩
  have hxW : x ∉ W := fun hw => hne
    (Subgroup.disjoint_def.mp (disjoint_conjugate_right hd (hMW ha)) hx hw)
  apply (mem_beta d p v).mpr
  refine ⟨fun h => hxW ((d.mem_right_iff hd v).mpr h), ?_⟩
  rw [mem_allowedProjections]
  by_cases hw : (d.equiv v).2 = 1
  · exact Or.inl (by simp [hw])
  have hiJ : x ∈ (centralizer (L : Set G)).conjBy a := map_mono hCK hx
  have hi2 : orderOf x = 2 := by
    apply orderOf_eq_prime _ hne
    obtain ⟨c, hc, rfl⟩ := hx
    simp only [← map_pow, hC2 c hc, map_one]
  have hnotK : x ∉ centralizer (L : Set G) := by
    intro hxK
    have hwK : ((d.equiv v).2 : G) ∈ centralizer (L : Set G) := by
      have hh := (centralizer (L : Set G)).mul_mem
        ((centralizer (L : Set G)).inv_mem (hCK (d.equiv v).1.property)) hxK
      rw [show x = ((d.equiv v).1 : G) * ((d.equiv v).2 : G) from d.multiply v] at hh
      simpa only [inv_mul_cancel_left] using hh
    exact hw (Subtype.ext (Subgroup.disjoint_def.mp hLK
      (p.le_component (d.equiv v).2.property) hwK))
  have hJ := hdetect _ ⟨a, rfl⟩ x hiJ hi2
    (by
      change (v : G) ∈ _
      rw [d.multiply v]
      exact mul_mem_sup (hCK (d.equiv v).1.property)
        (p.le_component (d.equiv v).2.property)) hnotK
  have hroot := havoid _ hJ x (d.equiv v).1 (d.equiv v).2 hiJ hi2
    (hCK (d.equiv v).1.property) (p.le_component (d.equiv v).2.property) (d.multiply v)
  exact Or.inr ⟨fun h => hroot (p.root_of_axis _ hw (Or.inl h)),
    fun h => hroot (p.root_of_axis _ hw (Or.inr h))⟩

end Counting
end CFSG.Quasithin.Chapter16.Intersections.RankTwo.Symplectic
