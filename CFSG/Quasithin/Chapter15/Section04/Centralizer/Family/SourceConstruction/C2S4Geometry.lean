module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.C2S4Geometry.Basic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.C2S4Geometry.Central
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.C2S4Geometry.DihedralCover
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Transfer

/-!
# The C₂ × S₄ geometry in 15.4.13

Two-perfectness and T-invariance identify X with the actual two-residual of
XT. From an equivalence XT ≃ C₂ × S₄, we construct the central four-group,
its three nonfused involutions, and the index-two dihedral subgroup
R = ⟨t⟩O₂(X), with its two XT-classes of involutions. `exists_geometry`
retains all these witnesses and their source identities. Its specialization
to the canonical Y-family discharges the intrinsic assumptions.

The final theorems supply the literal inputs to the parent's transfer argument
and construct a central involution outside O²(G). No simplicity hypothesis is
used here; the final simple-group exclusion belongs to the family assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 15.4.13, printed p.1161.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
variable {G : Type*} [Group G] [Finite G]

/-- The local intersection identity uses exactly the source's ambient Z and Φ(T). -/
theorem omegaCenter_inter_dihedral (T : Sylow 2 G) (X : Subgroup G)
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
    (D : DihedralCover T X) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      D.R.map (T : Subgroup G).subtype = (frattini T).map (T : Subgroup G).subtype := by
  obtain ⟨eT⟩ := sylow_equiv T X e
  rw [omegaCenter_eq_center_image T eT, ← map_inf _ _ _ Subtype.val_injective, D.center_inter]

/-- The three central classes provide the literal inputs of the transfer theorem
for a supplied local dihedral cover. -/
theorem transfer_inputs_of_dihedralCover (T : Sylow 2 G) (X : Subgroup G)
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
    (D : DihedralCover T X) :
    ∃ a b c : T, orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf c = 2 ∧
      (∀ x : T, (x : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ↔
        x = 1 ∨ x = a ∨ x = b ∨ x = c) ∧
      ¬ IsConj (a : G) (b : G) ∧ ¬ IsConj (a : G) (c : G) ∧
      ¬ IsConj (b : G) (c : G) ∧
      (∀ r : T, r ∈ D.R → orderOf r = 2 →
        IsConj (r : G) (D.t : G) ∨ IsConj (r : G) (D.z : G)) := by
  obtain ⟨eT⟩ := sylow_equiv T X e
  obtain ⟨a, b, c, ha, hb, hc, _, _, _, hZ, hab, hac, hbc⟩ :=
    exists_three_central_involutions T eT
  refine ⟨a, b, c, ha, hb, hc, ?_, hab, hac, hbc, ?_⟩
  · intro x
    exact (mem_omegaCenter_iff T eT x).trans (hZ x)
  · intro r hr ho
    exact (D.cover r hr ho).imp (X ⊔ (T : Subgroup G)).subtype.map_isConj
      (X ⊔ (T : Subgroup G)).subtype.map_isConj

/-- Actual application to the parent's missing-class theorem: the selected
involution lies in the source Z, misses R, and lies outside O²(G). -/
theorem missing_class_of_dihedralCover (T : Sylow 2 G) (X : Subgroup G)
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
    (D : DihedralCover T X) :
    ∃ i : T, (i : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      orderOf i = 2 ∧ (∀ r : T, r ∈ D.R → ¬ IsConj (i : G) (r : G)) ∧
      (i : G) ∉ pResidual 2 G := by
  obtain ⟨a, b, c, ha, hb, hc, hZ, hab, hac, hbc, hcover⟩ :=
    transfer_inputs_of_dihedralCover T X e D
  obtain ⟨i, hi, ho, hmiss, hout⟩ := Transfer.exists_missing_class T D.R D.R_index
    a b c ha hb hc hab hac hbc D.t D.z hcover
  exact ⟨i, (hZ i).mpr (Or.inr hi), ho, hmiss, hout⟩

/-- Output of the geometric construction, retaining the source subgroups and
the three nonidentity elements of Z. Existence is proved below from the actual
XT equivalence, two-perfectness and T-invariance. -/
structure Geometry (T : Sylow 2 G) (X : Subgroup G) extends DihedralCover T X where
  sylowEquiv : T ≃* SylowModel
  omegaCenterEquiv : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≃* Two × Two
  frattini_card : Nat.card (frattini T) = 2
  omegaCenter_inter : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
    R.map (T : Subgroup G).subtype = (frattini T).map (T : Subgroup G).subtype
  a : T
  b : T
  c : T
  a_order : orderOf a = 2
  b_order : orderOf b = 2
  c_order : orderOf c = 2
  omegaCenter_elements : ∀ x : T,
    (x : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ↔
      x = 1 ∨ x = a ∨ x = b ∨ x = c
  ab_nonconj : ¬ IsConj (a : G) (b : G)
  ac_nonconj : ¬ IsConj (a : G) (c : G)
  bc_nonconj : ¬ IsConj (b : G) (c : G)
  ambient_cover : ∀ r : T, r ∈ R → orderOf r = 2 →
    IsConj (r : G) (t : G) ∨ IsConj (r : G) (z : G)

/-- Construct every geometric input of 15.4.13 without assuming simplicity,
nonfusion, a dihedral cover, or an exclusion certificate. -/
theorem exists_geometry (T : Sylow 2 G) (X : Subgroup G)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    Nonempty (Geometry T X) := by
  obtain ⟨D⟩ := exists_dihedralCover T X hp hn e
  obtain ⟨eT⟩ := sylow_equiv T X e
  obtain ⟨eZ⟩ := omegaCenter_equiv_four T eT
  obtain ⟨a, b, c, ha, hb, hc, hZ, hab, hac, hbc, hcover⟩ :=
    transfer_inputs_of_dihedralCover T X e D
  exact ⟨{
    toDihedralCover := D
    sylowEquiv := eT
    omegaCenterEquiv := eZ
    frattini_card := frattini_card_two eT
    omegaCenter_inter := omegaCenter_inter_dihedral T X e D
    a := a, b := b, c := c
    a_order := ha, b_order := hb, c_order := hc
    omegaCenter_elements := hZ
    ab_nonconj := hab, ac_nonconj := hac, bc_nonconj := hbc
    ambient_cover := hcover
  }⟩

/-- The actual canonical Y-family supplies all intrinsic assumptions of the
geometric construction; it supplies none of its conclusions as hypotheses. -/
theorem exists_geometry_of_mem_Y (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G))
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    Nonempty (Geometry T X) :=
  exists_geometry T X (YFamily.perfect hX) (YFamily.invariant hX) e

/-- The normalizer acts trivially on the actual source Z. -/
theorem Geometry.normalizer_fixes {T : Sylow 2 G} {X : Subgroup G}
    (D : Geometry T X) (g : normalizer (T : Set G)) (x : G)
    (hx : x ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) :
    (g : G) * x * (g : G)⁻¹ = x := by
  have hxT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
  exact normalizer_fixes_center T D.sylowEquiv g ⟨x, hxT.1⟩
    ((mem_omegaCenter_iff T D.sylowEquiv ⟨x, hxT.1⟩).mp hx)

/-- The literal witnesses required by `Transfer.two_class_cover_impossible`,
with the dihedral cover and nonfusion fully constructed. -/
theorem exists_transfer_inputs (T : Sylow 2 G) (X : Subgroup G)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    ∃ (R : Subgroup T) (a b c : T) (t z : G), R.index = 2 ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf c = 2 ∧
      ¬ IsConj (a : G) (b : G) ∧ ¬ IsConj (a : G) (c : G) ∧
      ¬ IsConj (b : G) (c : G) ∧
      (∀ r : T, r ∈ R → orderOf r = 2 → IsConj (r : G) t ∨ IsConj (r : G) z) := by
  obtain ⟨D⟩ := exists_geometry T X hp hn e
  exact ⟨D.R, D.a, D.b, D.c, D.t, D.z, D.R_index, D.a_order, D.b_order,
    D.c_order, D.ab_nonconj, D.ac_nonconj, D.bc_nonconj, D.ambient_cover⟩

/-- Applying the parent's transfer theorem to the constructed geometry selects
one of the three retained central involutions whose class misses R. -/
theorem Geometry.exists_missing_class {T : Sylow 2 G} {X : Subgroup G}
    (D : Geometry T X) :
    ∃ i : T, (i = D.a ∨ i = D.b ∨ i = D.c) ∧
      (i : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      orderOf i = 2 ∧ (∀ r : T, r ∈ D.R → ¬ IsConj (i : G) (r : G)) ∧
      (i : G) ∉ pResidual 2 G := by
  obtain ⟨i, hi, ho, hmiss, hout⟩ := Transfer.exists_missing_class T D.R D.R_index
    D.a D.b D.c D.a_order D.b_order D.c_order D.ab_nonconj D.ac_nonconj D.bc_nonconj
    D.t D.z D.ambient_cover
  exact ⟨i, hi, (D.omegaCenter_elements i).mpr (Or.inr hi), ho, hmiss, hout⟩

/-- Source specialization: a hypothetical C₂ × S₄ member constructs the full
geometry and a central involution outside O²(G). Simplicity is used only by
the parent's final exclusion step. -/
theorem exists_missing_class_of_mem_Y (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Y (T : Subgroup G))
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    ∃ (D : Geometry T X) (i : T), (i = D.a ∨ i = D.b ∨ i = D.c) ∧
      (i : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      orderOf i = 2 ∧ (∀ r : T, r ∈ D.R → ¬ IsConj (i : G) (r : G)) ∧
      (i : G) ∉ pResidual 2 G := by
  obtain ⟨D⟩ := exists_geometry_of_mem_Y T hX e
  obtain ⟨i, hi⟩ := D.exists_missing_class
  exact ⟨D, i, hi⟩

end CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
