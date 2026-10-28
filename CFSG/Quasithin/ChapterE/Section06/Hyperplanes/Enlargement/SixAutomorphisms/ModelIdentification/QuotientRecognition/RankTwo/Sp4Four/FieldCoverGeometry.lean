module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four.FieldCoverGeometry.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four.FieldCoverGeometry.FixedGroup
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.ElementaryAbelian.CyclicKernel
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity

/-!
# Sylow-fixing actors in the central-cover field configuration

A cyclic outer quotient forces the elementary order-eight action to contain
a nonidentity inner automorphism. Since it commutes with the distinguished
field involution, its conjugating element belongs to the actual fixed Sp₄(2).
The fixed-component theorem places the given A₆ in the embedded derived
subfield group. The separate binary Sylow centralizer calculation then gives
an ambient Sylow subgroup fixed by this inner actor.

For a central cover, triviality of the actual universal multiplier first
makes the quotient map injective. Only then do we transport the action and
the Sylow subgroup through a genuine equivalence with Sp₄(4). Thus fixation
on the central quotient is never substituted for fixation on the cover.

The final theorem `fieldCoverSylowGeometry` discharges all three model inputs
using the even symplectic multiplier theorem, the diagram-preserving
semilinear classification, and the binary fixed-group Sylow calculation.
It proves the exact `FieldCoverSylowGeometry` contract without extra premises,
for the original action on the whole central cover. The conditional assembly
is retained as a separate interface.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8(2),
printed pp.247–248; E.6.23, p.254 (PDF p.265); I.1.1–3, p.407; and
16.1.4(4), pp.1171–1172. Cyclicity of the outer quotient is obtained from
the explicit exceptional graph automorphism and semilinear coverage.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
universe u

/-- Triviality of the actual universal multiplier removes the central cover.
This is a transport lemma; the multiplier calculation is a separate theorem. -/
theorem center_eq_bot_of_trivial_multiplier
    {D : Type u} [Group D] [Group.IsPerfect D]
    {F : Type} [Field F]
    (hm : (PerfectCentralCovering.universalProjection (Sp F)).ker = ⊥)
    (e : (D ⧸ center D) ≃* Sp F) : center D = ⊥ := by
  let q := QuotientGroup.mk' (center D)
  let f := e.toMonoidHom.comp q
  have hk : f.ker = center D := by
    ext x
    change e (q x) = 1 ↔ x ∈ center D
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let c : PerfectCentralCovering.Cover D (Sp F) := {
    toMonoidHom := f
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := hk.le }
  have hi := c.injective_of_universalProjection_ker_eq_bot hm
  exact hk.symm.trans (f.ker_eq_bot_iff.mpr hi)

private theorem exists_nonidentity_inner_actor {D : Type*} [Group D]
    [IsCyclic (MulAut.Outer D)] (s : FixedSixAction D) :
    ∃ g : D, MulAut.conj g ∈ s.actors ∧ MulAut.conj g ≠ 1 := by
  classical
  let _ := s.elementary
  by_contra! h
  have hd : Disjoint s.actors (MulAut.innerSubgroup D) := by
    rw [Subgroup.disjoint_def]
    rintro a ha ⟨g, rfl⟩
    exact h g ha
  let π := QuotientGroup.mk' (MulAut.innerSubgroup D)
  have hb := IsElementaryAbelian.card_le_of_disjoint_cyclic_kernel (p := 2) s.actors π
    (by simpa only [π, QuotientGroup.ker_mk'] using hd)
  rw [s.card_actors] at hb
  omega

private theorem fixed_of_commute_conj {D : Type*} [Group D]
    (hz : center D = ⊥) (a : MulAut D) (g : D)
    (h : Commute a (MulAut.conj g)) : a g = g := by
  apply conj_injective_of_center_eq_bot hz
  apply MulEquiv.ext
  intro x
  have hh := DFunLike.congr_fun h.eq (a.symm x)
  change a (g * a.symm x * g⁻¹) = g * a (a.symm x) * g⁻¹ at hh
  simpa only [map_mul, map_inv, a.apply_symm_apply, MulAut.conj_apply] using hh

/-- Cyclicity of the outer group forces a nontrivial inner actor; commutation
with the distinguished field automorphism places its conjugating element in
the actual field-fixed subgroup. -/
theorem exists_field_fixed_inner_actor
    {F : Type} [Field F] [Finite F] [CharP F 2]
    [IsCyclic (MulAut.Outer (Sp F))]
    (s : FixedSixAction (Sp F))
    (hs : s.involution = DiagramAutomorphisms.FieldFixedResidual.representative 1) :
    ∃ g : Sp F, MulAut.conj g ∈ s.actors ∧ MulAut.conj g ≠ 1 ∧
      DiagramAutomorphisms.FieldFixedResidual.representative 1 g = g := by
  obtain ⟨g, hg, hne⟩ := exists_nonidentity_inner_actor s
  refine ⟨g, hg, hne, ?_⟩
  apply fixed_of_commute_conj EvenProjective.center_eq_bot
  let _ := s.elementary
  rw [← hs]
  exact congrArg Subtype.val (mul_comm (⟨s.involution, s.involution_mem⟩ : s.actors)
    ⟨MulAut.conj g, hg⟩)

/-- The actual component is the binary derived subfield group. The local
centralizer calculation then turns the inner actor into an ambient Sylow fixer. -/
theorem exists_sylow_fixed_actor_of_fixedGroup
    (hgeom : FixedGroupSylowGeometry)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    [IsCyclic (MulAut.Outer (Sp F))]
    (s : FixedSixAction (Sp F))
    (hs : s.involution = DiagramAutomorphisms.FieldFixedResidual.representative 1) :
    ∃ a : MulAut (Sp F), a ∈ s.actors ∧ a ≠ 1 ∧
      ∃ P : Sylow 2 (Sp F), ∀ x ∈ (P : Subgroup (Sp F)), a x = x := by
  obtain ⟨g, hg, hne, hfixed⟩ := exists_field_fixed_inner_actor s hs
  have he : s.six = FieldComponent.embedded (F := F) 1 :=
    FieldComponent.component_eq_embedded (by decide) (by simpa using hF) s.six
      (hs ▸ s.component)
  let e := MulEquiv.subgroupCongr he
  let P := s.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : ∀ x ∈ (P : Subgroup (FieldComponent.embedded (F := F) 1)),
      MulAut.conj g (x : Sp F) = x := by
    rintro x ⟨y, hy, rfl⟩
    exact s.fixes (MulAut.conj g) hg y hy
  obtain ⟨Q, hQ⟩ := hgeom F hF P g hfixed hP
  exact ⟨MulAut.conj g, hg, hne, Q, hQ⟩

private theorem eq_of_zpowers_eq_of_order_two {D : Type*} [Group D] [Finite D]
    {a b : D} (ha : a ≠ 1) (hb : orderOf b = 2) (h : zpowers a = zpowers b) : a = b := by
  classical
  have hm : a ∈ zpowers b := h ▸ mem_zpowers a
  rw [mem_zpowers_iff_mem_range_orderOf, hb] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact (ha (by simpa using he.symm)).elim
  · simpa using he.symm

/-- Assembly from the universal multiplier kernel, diagram coverage, and the
binary derived Sylow centralizer calculation. No quotient fixation is lifted
until the cover has actually been proved centerless. -/
theorem fieldCoverSylowGeometry_of_inputs
    (hmult : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      (PerfectCentralCovering.universalProjection (Sp F)).ker = ⊥)
    (hclass : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
      ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
        ∃ g : Sp F, ∃ σ : F ≃+* F,
          a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    (hgeom : FixedGroupSylowGeometry) : FieldCoverSylowGeometry.{u} := by
  intro D _ _ _ _hZ F _ _ _ hF e s hs
  have hc : center D = ⊥ := center_eq_bot_of_trivial_multiplier (hmult F hF) e
  let q := QuotientGroup.mk' (center D)
  have hq : Function.Bijective q :=
    ⟨(MonoidHom.ker_eq_bot_iff q).mp ((QuotientGroup.ker_mk' (center D)).trans hc),
      QuotientGroup.mk'_surjective _⟩
  let f := (MulEquiv.ofBijective q hq).trans e
  have hf (a : MulAut D) :
      MulAut.congr f a = MulAut.congr e (quotientAut (center D) a) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    change f (a (f.symm (f y))) = e (quotientAut (center D) a (e.symm (e (q y))))
    rw [f.symm_apply_apply, e.symm_apply_apply, quotientAut_apply_mk]
    rfl
  have hi : (s.map f).involution =
      DiagramAutomorphisms.FieldFixedResidual.representative 1 := by
    apply eq_of_zpowers_eq_of_order_two
    · intro he
      have ho := (s.map f).involution_order
      rw [he, orderOf_one] at ho
      contradiction
    · exact DiagramAutomorphisms.FieldFixedResidual.representative_orderOf
        (by decide : 1 ≤ 1) (by simpa using hF)
    · rw [FixedSixAction.map_involution, hf]
      change zpowers ((MulAut.congr e).toMonoidHom
        ((center D).quotientAut s.involution)) = _
      rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers]
      exact hs
  let _ := DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic
    (by omega : 2 < Nat.card F) (hclass F hF)
  obtain ⟨a, ha, hne, P, hP⟩ := exists_sylow_fixed_actor_of_fixedGroup hgeom hF (s.map f) hi
  obtain ⟨b, hb, rfl⟩ := ha
  let Q := P.mapSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  refine ⟨b, hb, ?_, Q, ?_⟩
  · intro he
    exact hne (by rw [he, map_one])
  · rintro x ⟨y, hy, rfl⟩
    apply f.injective
    have hh := hP y hy
    change f (b (f.symm y)) = y at hh
    change f (b (f.symm y)) = f (f.symm y)
    rw [f.apply_symm_apply]
    exact hh

/-- In the genuine Sp₄(4) field configuration, a nonidentity actor fixes a
Sylow two-subgroup of the whole quasisimple group pointwise. The actual
multiplier calculation removes the central cover before Sylow transport. -/
theorem fieldCoverSylowGeometry : FieldCoverSylowGeometry.{u} := by
  apply fieldCoverSylowGeometry_of_inputs
  · intro F _ _ _ hF
    exact CentralCovers.Even.universalProjection_ker_eq_bot (by omega)
  · intro F _ _ _ _hF a ha
    exact DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a ha
  · exact fixedGroupSylowGeometry

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
