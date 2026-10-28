module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.Geometry
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.TorusSeparation
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Eliminating central defects in lifted Ree angular tails

Suppose the actual base root blocks normalize angular tails, and fixed torus
actors separate distinct blocks as specified in `Geometry`. Then any
homomorphic, torus-equivariant block sections through a surjection with central
kernel normalize the same tails in the extension. Perfectness and the order of
the kernel are not needed for this local implication.

For an earlier lifted element x and a later lifted element y, choose an actor t
fixing the earlier block and express y as [t,z] in its own block. Equivariance
makes the lifted actor commute with x and normalize the lifted tail H.
The projection of xzx⁻¹ belongs to the base tail, which is the image of H.
Thus xzx⁻¹ differs from an element of H by a central kernel element. That
factor disappears in [t,xzx⁻¹], proving xyx⁻¹ ∈ H. This handles the whole B₂
blocks without an increasing-height assumption or an abelianization.

The concrete interval and fixed-coroot calculations discharge both geometric
inputs for every m ≥ 1, including q = 8. Thus torus-equivariant block sections
normalize the lifted angular tails, with no additional lifted relations.
The final theorem applies this result to the literal unipotent section
consumer. Existence of the block sections remains an independent input to
the parent central-cover argument; the Tits endpoint is separate.
Commutators here are a*b*a⁻¹*b⁻¹; the source right commutator is obtained by
replacing a,b by a⁻¹,b⁻¹.

Source: GLS3, Corollary 2.4.6 and Theorem 2.4.7(f),
`refs/KGroup/GLS3/chapter2.tex`; GLS3 §6.1 and Aschbacher–Smith I.1.1–4,
printed pp.407–408 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped commutatorElement

private theorem central_commutator_eq {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : f.ker ≤ center E) (t a b : E) (hab : f a = f b) :
    ⁅t, a⁆ = ⁅t, b⁆ := by
  have hk : b⁻¹ * a ∈ center E := hf (by
    change f (b⁻¹ * a) = 1
    simp only [map_mul, map_inv, hab, inv_mul_cancel])
  have hc : Commute t (b⁻¹ * a) := mem_center_iff.mp hk t
  have ha : a = b * (b⁻¹ * a) := by simp
  calc
    ⁅t, a⁆ = ⁅t, b * (b⁻¹ * a)⁆ := congrArg (fun z => ⁅t, z⁆) ha
    _ = ⁅t, b⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hc.commutator_eq]
      simp

private theorem central_commutator_mem {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : f.ker ≤ center E) (H : Subgroup E)
    (t a : E) (ht : t ∈ normalizer (H : Set E)) (ha : f a ∈ H.map f) :
    ⁅t, a⁆ ∈ H := by
  obtain ⟨b, hb, he⟩ := ha
  rw [central_commutator_eq f hf t a b he.symm, commutatorElement_def]
  exact H.mul_mem ((mem_normalizer_iff.mp ht b).mp hb) (H.inv_mem hb)

namespace ReeF4.CentralCovers.TwoPrimary
open ElementaryTwoBound TailRelations

private theorem orderedJoin_le {m : ℕ} {E : Type*} [Group E] {f : E →* Model m}
    (L : BlockSections m f) (order : List BlockIndex) (H : Subgroup E)
    (h : ∀ i ∈ order, (L.lift i).range ≤ H) : L.orderedJoin order ≤ H := by
  induction order with
  | nil => exact bot_le
  | cons i rest ih =>
    exact sup_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

private theorem range_le_join {m : ℕ} {E : Type*} [Group E] {f : E →* Model m}
    (L : BlockSections m f) (order : List BlockIndex) (i : BlockIndex)
    (hi : i ∈ order) : (L.lift i).range ≤ L.orderedJoin order := by
  induction order with
  | nil => simp at hi
  | cons j rest ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_sup_left
    · exact (ih hi).trans le_sup_right

/-- Projection carries a lifted tail onto the literal join of its root blocks. -/
theorem BlockSections.map_orderedJoin {m : ℕ} {E : Type*} [Group E]
    {f : E →* Model m} (L : BlockSections m f) (order : List BlockIndex) :
    (L.orderedJoin order).map f = baseOrderedJoin m order := by
  have hr (i : BlockIndex) : (L.lift i).range.map f = X m (rootIndex i) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      rw [L.project]
      exact y.property
    · intro hx
      exact ⟨L.lift i ⟨x, hx⟩, ⟨⟨x,hx⟩,rfl⟩, L.project _ _⟩
  induction order with
  | nil => exact map_bot f
  | cons i rest ih =>
    change ((L.lift i).range ⊔ L.orderedJoin rest).map f =
      X m (rootIndex i) ⊔ baseOrderedJoin m rest
    rw [Subgroup.map_sup, hr, ih]

private theorem lift_normalizes_range {m : ℕ} {E : Type*} [Group E]
    {f : E →* Model m} (L : BlockSections m f) (hL : L.TorusEquivariant)
    (t : E) (ht : f t ∈ Parabolics.fixedTorus m) (i : BlockIndex)
    (hi : f t ∈ normalizer (X m (rootIndex i) : Set (Model m))) :
    t ∈ normalizer ((L.lift i).range : Set E) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨y,rfl⟩
    let y' : X m (rootIndex i) :=
      ⟨f t * y.val * (f t)⁻¹, (mem_normalizer_iff.mp hi _).mp y.property⟩
    exact ⟨y', (hL i y y' t ht rfl).symm⟩
  · intro hx
    obtain ⟨y,hy⟩ := hx
    let y' : X m (rootIndex i) :=
      ⟨(f t)⁻¹ * y.val * f t, (mem_normalizer_iff''.mp hi _).mp y.property⟩
    refine ⟨y', ?_⟩
    have h := hL i y y' t⁻¹ (by simpa using (Parabolics.fixedTorus m).inv_mem ht)
      (by simp only [map_inv, inv_inv]; rfl)
    rw [hy] at h
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h.symm

private theorem lift_normalizes_join {m : ℕ} {E : Type*} [Group E]
    {f : E →* Model m} (L : BlockSections m f) (hL : L.TorusEquivariant)
    (t : E) (ht : f t ∈ Parabolics.fixedTorus m)
    (hn : ∀ i, f t ∈ normalizer (X m (rootIndex i) : Set (Model m)))
    (order : List BlockIndex) :
    t ∈ normalizer (L.orderedJoin order : Set E) := by
  induction order with
  | nil =>
    change t ∈ normalizer ((⊥ : Subgroup E) : Set E)
    rw [normalizer_eq_top]
    exact mem_top t
  | cons i rest ih =>
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
      ⟨lift_normalizes_range L hL t ht i (hn i), ih⟩

private theorem sourceOrder_nodup : sourceOrder.Nodup := by decide

/-- Base angular normalization and separating torus actors eliminate the central
defects of all inter-block conjugations. No extra lifted relations are assumed. -/
theorem BlockSections.normalizesTails_of_base_and_torus {m : ℕ}
    {E : Type*} [Group E] {f : E →* Model m}
    (hf : Function.Surjective f) (hker : f.ker ≤ center E)
    (L : BlockSections m f) (hL : L.TorusEquivariant)
    (hb : BaseNormalizesTails m) (htorus : TorusBlockSeparation m) :
    L.NormalizesTails := by
  intro before i after he
  have hn : (before ++ i :: after).Nodup := he ▸ sourceOrder_nodup
  have hi : i ∉ after := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  apply le_normalizer_iff.mpr
  rintro _ ⟨x,rfl⟩
  change L.orderedJoin after ≤
    (L.orderedJoin after).comap (MulAut.conj (L.lift i x)).toMonoidHom
  apply orderedJoin_le L after
  intro j hj
  rintro _ ⟨y,rfl⟩
  change L.lift i x * L.lift j y * (L.lift i x)⁻¹ ∈ L.orderedJoin after
  obtain ⟨a, haT, haN, haX, haY⟩ := htorus i j (fun h => hi (h.symm ▸ hj))
  obtain ⟨t, ht⟩ := hf a
  have htT : f t ∈ Parabolics.fixedTorus m := ht ▸ haT
  have htN : ∀ k, f t ∈ normalizer (X m (rootIndex k) : Set (Model m)) :=
    fun k => ht ▸ haN k
  have htH : t ∈ normalizer (L.orderedJoin after : Set E) :=
    lift_normalizes_join L hL t htT htN after
  have htx : Commute t (L.lift i x) := by
    apply mul_inv_eq_iff_eq_mul.mp
    exact hL i x x t htT (by
      rw [ht, (haX x).eq, mul_assoc, mul_inv_cancel, mul_one])
  have hxt : L.lift i x * t * (L.lift i x)⁻¹ = t := by
    rw [← htx.eq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨z, hz⟩ := haY y
  let z' : X m (rootIndex j) :=
    ⟨a * z.val * a⁻¹, (mem_normalizer_iff.mp (haN j) _).mp z.property⟩
  have hy : L.lift j y = ⁅t, L.lift j z⁆ := by
    rw [commutatorElement_def, hL j z z' t htT (by rw [ht])]
    rw [← map_inv, ← map_mul]
    exact congrArg (L.lift j) (Subtype.ext hz.symm)
  have hzH : L.lift j z ∈ L.orderedJoin after :=
    range_le_join L after j hj ⟨z,rfl⟩
  have hzB : z.val ∈ baseOrderedJoin m after := by
    rw [← L.project j z, ← L.map_orderedJoin]
    exact mem_map_of_mem f hzH
  have hp : f (L.lift i x * L.lift j z * (L.lift i x)⁻¹) ∈
      (L.orderedJoin after).map f := by
    rw [L.map_orderedJoin, map_mul, map_mul, map_inv, L.project, L.project]
    exact (mem_normalizer_iff.mp (hb before i after he x.property) _).mp hzB
  rw [hy, conjugate_commutatorElement, hxt]
  exact central_commutator_mem f hker (L.orderedJoin after) t _ htH hp

/-- Application to the original covering map and marked unipotent subgroup.
The two concrete geometric premises still require their independent calculations. -/
theorem unipotent_section_of_base_and_torus (m : ℕ)
    {F : Type*} [Group F] [Finite F] (d : PerfectCentralCovering.Cover F (Model m))
    (L : BlockSections m d.toMonoidHom) (hL : L.TorusEquivariant)
    (hb : BaseNormalizesTails m) (ht : TorusBlockSeparation m) :
    ∃ s : Parabolics.unipotent m →* F,
      d.toMonoidHom.comp s = (Parabolics.unipotent m).subtype :=
  L.exists_unipotent_section
    (L.normalizesTails_of_base_and_torus d.surjective d.ker_le_center hL hb ht)

/-- For m ≥ 1, torus-equivariant lifts of the actual Ree blocks normalize
successive angular tails in any central extension. Both base-group geometric
premises are discharged by the concrete root and fixed-coroot calculations. -/
theorem BlockSections.normalizesTails_of_torusEquivariant {m : ℕ} (hm : 1 ≤ m)
    {E : Type*} [Group E] {f : E →* Model m}
    (hf : Function.Surjective f) (hker : f.ker ≤ center E)
    (L : BlockSections m f) (hL : L.TorusEquivariant) : L.NormalizesTails :=
  L.normalizesTails_of_base_and_torus hf hker hL
    (BaseIntervals.baseNormalizesTails m) (torusBlockSeparation m hm)

/-- The exact degree-two covering contract consumed by
`not_two_dvd_kernel_of_block_calculations`. The kernel-order hypothesis is
retained for that interface, although the local normalization proof works for
every central kernel. -/
theorem BlockSections.normalizesTails_of_two_cover (m : ℕ) (hm : 1 ≤ m)
    {F : Type*} [Group F] [Finite F] (d : PerfectCentralCovering.Cover F (Model m))
    (_hd : Nat.card d.toMonoidHom.ker = 2)
    (L : BlockSections m d.toMonoidHom) (hL : L.TorusEquivariant) :
    L.NormalizesTails :=
  L.normalizesTails_of_torusEquivariant hm d.surjective d.ker_le_center hL

/-- Torus-equivariant homomorphic block lifts give a section over the literal
positive unipotent subgroup, with no further relation or geometric premise.
The independent block-lift construction supplies L in the parent assembly. -/
theorem unipotent_section_of_torusEquivariant (m : ℕ) (hm : 1 ≤ m)
    {F : Type*} [Group F] [Finite F] (d : PerfectCentralCovering.Cover F (Model m))
    (L : BlockSections m d.toMonoidHom) (hL : L.TorusEquivariant) :
    ∃ s : Parabolics.unipotent m →* F,
      d.toMonoidHom.comp s = (Parabolics.unipotent m).subtype :=
  L.exists_unipotent_section
    (L.normalizesTails_of_torusEquivariant hm d.surjective d.ker_le_center hL)

end ReeF4.CentralCovers.TwoPrimary
