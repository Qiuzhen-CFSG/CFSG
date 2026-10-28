module

public import Theory.GroupTheory.ChiefFactorDirectPower.CharacteristicallySimple
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Chief factors as powers of composition factors

A chief interval uses normality in the ambient group. Its image in the quotient
is a nontrivial minimal normal subgroup, hence has no proper nontrivial
characteristic subgroup. The finite characteristically-simple structure theorem
therefore identifies it with a positive direct power of a finite simple group.
The quotient-image equivalence gives the corresponding isomorphism for `X/Y`.

A positive direct power of a simple group supplies a genuine composition-factor
witness: project onto one coordinate and apply the first isomorphism theorem.
The kernel is normal in the section subgroup, not necessarily in the ambient
group. All subgroup, normality, subnormality and multiplicative-equivalence data
are retained in `SimpleSection`.

This proves the chief-factor structure used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.10(5), p.211, which cites
Aschbacher (1986), 8.2.
-/

@[expose] public section

universe u v
namespace ChiefFactor
open Subgroup
variable {G : Type u} [Group G]

/-- An explicit simple normal section of a subnormal subgroup. For finite `G`,
this witnesses a composition factor, with its actual group isomorphism. -/
structure SimpleSection (G : Type u) [Group G] (S : Type v) [Group S] where
  simple : IsSimpleGroup S
  subgroup : Subgroup G
  subnormal : subgroup.IsSubnormal
  kernel : Subgroup subgroup
  normal : kernel.Normal
  equiv : letI := normal; subgroup ⧸ kernel ≃* S

variable {S : Type v} [Group S] [IsSimpleGroup S]

/-- The first isomorphism theorem makes a simple quotient of a subnormal subgroup
into an explicit simple-section witness. -/
noncomputable def simpleSectionOfSurjective (X : Subgroup G) (hX : X.IsSubnormal)
    (f : X →* S) (hf : Function.Surjective f) : SimpleSection G S where
  simple := inferInstance
  subgroup := X
  subnormal := hX
  kernel := f.ker
  normal := inferInstance
  equiv := QuotientGroup.quotientKerEquivOfSurjective f hf

/-- Projecting a positive direct power onto coordinate zero gives a simple
normal section of the original subnormal subgroup. -/
noncomputable def simpleSectionOfPower (X Y : Subgroup G) [Y.Normal]
    (hX : X.IsSubnormal) {n : ℕ} (hn : 0 < n)
    (e : X ⧸ Y.subgroupOf X ≃* (Fin n → S)) : SimpleSection G S := by
  let f : X →* S := (Pi.evalMonoidHom (fun _ : Fin n => S) ⟨0, hn⟩).comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Y.subgroupOf X)))
  apply simpleSectionOfSurjective X hX f
  intro s
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf X) (e.symm (fun _ => s))
  refine ⟨x, ?_⟩
  change e (QuotientGroup.mk' (Y.subgroupOf X) x) ⟨0, hn⟩ = s
  rw [hx, e.apply_symm_apply]

variable (X Y : Subgroup G) [Y.Normal]

/-- An ambient chief interval. The two normality conditions refer to `G`. -/
structure IsChief : Prop where
  normal_upper : X.Normal
  normal_lower : Y.Normal
  lt : Y < X
  minimal : ∀ Z : Subgroup G, Z.Normal → Y ≤ Z → Z ≤ X → Z = Y ∨ Z = X

/-- The image of the upper endpoint of a chief interval is nontrivial. -/
theorem IsChief.image_ne_bot (h : IsChief X Y) : X.map (QuotientGroup.mk' Y) ≠ ⊥ := by
  intro he
  have hXY : X ≤ Y := by simpa using ((Subgroup.map_eq_bot_iff X).mp he)
  exact h.lt.not_ge hXY

/-- The subgroup correspondence transfers ambient chief minimality to the image. -/
theorem IsChief.image_minimal (h : IsChief X Y) (N : Subgroup (G ⧸ Y))
    (hN : N.Normal) (hNX : N ≤ X.map (QuotientGroup.mk' Y)) :
    N = ⊥ ∨ N = X.map (QuotientGroup.mk' Y) := by
  let q := QuotientGroup.mk' Y
  have hYX : Y ≤ N.comap q := by simpa [q] using N.ker_le_comap q
  have hXX : (X.map q).comap q = X := by
    apply Subgroup.comap_map_eq_self
    simpa [q] using h.lt.le
  have hpre : N.comap q ≤ X := hXX ▸ Subgroup.comap_mono hNX
  obtain he | he := h.minimal (N.comap q) (hN.comap q) hYX hpre
  · left
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective Y)
    simpa [q] using he
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective Y)
    exact he.trans hXX.symm

omit [Y.Normal] in
/-- A characteristic subgroup of a minimal normal subgroup is trivial or whole. -/
theorem characteristic_eq_bot_or_top_of_minimal_normal
    (M : Subgroup G) [M.Normal]
    (hM : ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M)
    (C : Subgroup M) (hC : C.Characteristic) : C = ⊥ ∨ C = ⊤ := by
  let := hC
  obtain he | he := hM (C.map M.subtype) inferInstance (Subgroup.map_subtype_le C)
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective C M.subtype_injective).mp he)
  · right
    apply Subgroup.map_injective M.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

omit [Y.Normal] in
/-- A chief factor is a nontrivial group. -/
theorem IsChief.quotient_nontrivial (h : IsChief X Y) :
    Nontrivial (X ⧸ Y.subgroupOf X) := by
  apply QuotientGroup.nontrivial_iff.mpr
  intro he
  exact h.lt.not_ge (Subgroup.subgroupOf_eq_top.mp he)

/-- A chief image is characteristically simple. -/
theorem IsChief.image_characteristic_eq_bot_or_top (h : IsChief X Y)
    (C : Subgroup (X.map (QuotientGroup.mk' Y))) (hC : C.Characteristic) :
    C = ⊥ ∨ C = ⊤ := by
  let : (X.map (QuotientGroup.mk' Y)).Normal :=
    h.normal_upper.map _ (QuotientGroup.mk'_surjective Y)
  exact characteristic_eq_bot_or_top_of_minimal_normal _
    (h.image_minimal X Y) C hC

/-- The quotient of `X` by its relative intersection with `Y` is its actual image
in `G/Y`. No chief or minimal-supplement assumption is needed. -/
noncomputable def quotientImageEquiv :
    X ⧸ Y.subgroupOf X ≃* X.map (QuotientGroup.mk' Y) := by
  let f := (QuotientGroup.mk' Y).subgroupMap X
  have hk : Y.subgroupOf X = f.ker := by
    ext x
    change (x : G) ∈ Y ↔ f x = 1
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff (x : G)).symm
  exact (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' Y).subgroupMap_surjective X))

/-- A finite chief factor is a positive direct power of a finite simple group
which occurs as an explicit simple normal section of a subnormal subgroup of `G`.
The carrier `S` is a subgroup of the chief image, so its finiteness is inherited.
Chief normality is ambient; the kernel in `SimpleSection` is normal only in its
section subgroup, as required for a composition factor. -/
theorem IsChief.exists_directPower_and_simpleSection [Finite G] (h : IsChief X Y) :
    ∃ S : Subgroup (X.map (QuotientGroup.mk' Y)), IsSimpleGroup S ∧
      ∃ n : ℕ, 0 < n ∧
        Nonempty (X ⧸ Y.subgroupOf X ≃* (Fin n → S)) ∧
        Nonempty (SimpleSection G S) := by
  let : Nontrivial (X.map (QuotientGroup.mk' Y)) :=
    (X.map (QuotientGroup.mk' Y)).nontrivial_iff_ne_bot.mpr (h.image_ne_bot X Y)
  obtain ⟨S, hS, n, hn, ⟨e⟩⟩ :=
    CharacteristicallySimple.exists_simple_subgroup_power
      (h.image_characteristic_eq_bot_or_top X Y)
  let := hS
  let eQ := (quotientImageEquiv X Y).trans e
  exact ⟨S, hS, n, hn, ⟨eQ⟩,
    ⟨simpleSectionOfPower X Y h.normal_upper.isSubnormal hn eQ⟩⟩

end ChiefFactor
