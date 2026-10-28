module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Kernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.SourceAlignment.FieldSeparation
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.AtlasPort.OtherSporadic.GroupTheory.CenterSimpleQuotient

/-!
# The raw A.3.15(5) configuration for the linear case

The groups F, H and I live in Aut(D); the subgroup B ≤ D is included by its
actual inner action. The supplied model witnesses the phrase "induces field
automorphisms": in those coordinates the whole field subgroup acts by
coefficient automorphisms. It has no condition on the image of U or H and
need not be an initially supplied identification of D with PSL₃(E).

For a split group in characteristic two, a Cartan of the Borel N_I(U) is
its abelian odd-order complement to the unipotent radical. `SplitCartan`
records that complement intrinsically, without a conjugating equivalence
or any reference to the standard torus. `cartan_odd_hall` verifies its
odd order and power-of-two relative index. The standard matrix complement
is proved independently in `BorelGeometry`.

The normalizer here is relative to I. `relative_normalizer` identifies the
stabilizer convention with the actual subgroup normalizer inside I, using
centerlessness of the nonabelian simple D. Every raw source clause is
retained, including F-invariance, |F| = f dividing n, the literal set-product
equality FBD = HBD, and the definition of the inner-diagonal part I.

Field/inner-diagonal disjointness is proved in `FieldSeparation` and
transported through the actual model. Only then do we deduce B ≤ H using
the shared kernel lemma. The product equality also forces F = 1 in this
inside-D branch. The alignment argument needs only the resulting B ≤ N_D(U).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma A.3.15(5),
printed pp.50–51 (PDF pp.61–62), and Proposition 1.3.4, printed p.511.
For split Cartans see also GLS3, §2.3 and Theorem 2.4.7. The imported ATLAS
centerlessness theorem retains its attribution and license in its source.
-/

@[expose] public section

open scoped MatrixGroups Pointwise
open Subgroup Matrix.PSL3.OuterSolvable

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment

variable {D : Type*} [Group D]

/-- Automorphisms stabilizing the actual subgroup U. -/
def autNormalizer (U : Subgroup D) : Subgroup (MulAut D) where
  carrier := {a | ∀ x, x ∈ U ↔ a x ∈ U}
  one_mem' := by intro x; rfl
  mul_mem' ha hb x := (hb x).trans (ha _)
  inv_mem' {a} ha x := by simpa using (ha (a⁻¹ x)).symm

theorem inner_mem_autNormalizer_iff (U : Subgroup D) (x : D) :
    MulAut.conj x ∈ autNormalizer U ↔ x ∈ normalizer U := by
  exact Subgroup.mem_normalizer_iff.symm

private theorem conjugate_inner (a : MulAut D) (x : D) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  ext y
  simp

theorem autNormalizer_eq_normalizer_inner (U : Subgroup D) (hc : center D = ⊥) :
    autNormalizer U = normalizer (U.map (MulAut.conj : D →* MulAut D)) := by
  have hinj := MulAut.conj_injective_of_center_eq_bot hc
  ext a
  constructor
  · intro ha
    rw [mem_normalizer_iff]
    intro b
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨a x, (ha x).mp hx, conjugate_inner a x⟩
    · rintro ⟨x,hx,he⟩
      refine ⟨a⁻¹ x, (ha (a⁻¹ x)).mpr (by simpa using hx), ?_⟩
      rw [conjugate_inner, he]
      group
  · intro ha x
    have h₁ : MulAut.conj x ∈ U.map (MulAut.conj : D →* MulAut D) ↔ x ∈ U :=
      mem_map_iff_mem hinj
    have h₂ : MulAut.conj (a x) ∈ U.map (MulAut.conj : D →* MulAut D) ↔ a x ∈ U :=
      mem_map_iff_mem hinj
    rw [← h₁, ← h₂, conjugate_inner]
    exact mem_normalizer_iff.mp ha (MulAut.conj x)

/-- The intrinsic toral-complement description of a split Cartan in N_I(U). -/
structure SplitCartan (I : Subgroup (MulAut D)) (U : Subgroup D)
    (H : Subgroup (MulAut D)) : Prop where
  inside : H ≤ I
  normalizes : H ≤ autNormalizer U
  abelian : IsMulCommutative H
  odd : Odd (Nat.card H)
  complement : IsComplement' ((U.map (MulAut.conj : D →* MulAut D)).subgroupOf
      (I ⊓ autNormalizer U)) (H.subgroupOf (I ⊓ autNormalizer U))

variable (E : Type*) [Field E] [Finite E]

/-- All clauses of A.3.15(5), specialized to an actual B ≤ D of type A₂.
The model is a field-coordinate witness, with no Sylow or Cartan alignment. -/
structure RawConfiguration (n : ℕ) (U B : Subgroup D) where
  model : D ≃* PSL(3,E)
  field_card : Nat.card E = 2 ^ n
  degree : 1 < n
  F : Subgroup (MulAut D)
  H : Subgroup (MulAut D)
  I : Subgroup (MulAut D)
  f : ℕ
  field_cyclic : IsCyclic F
  field_order : Nat.card F = f
  field_degree : f ∣ n
  field_action : F.map (MulAut.congr model).toMonoidHom ≤ (fieldAction E).range
  cartan : SplitCartan I U H
  invariant : F ≤ normalizer H
  product : ∀ b ∈ B.map (MulAut.conj : D →* MulAut D),
    ∃ a ∈ F, ∃ h ∈ H, b = a * h
  product_eq : ((F : Set (MulAut D)) * (B.map (MulAut.conj : D →* MulAut D)) : Set (MulAut D)) *
      (MulAut.innerSubgroup D : Set (MulAut D)) =
    ((H : Set (MulAut D)) * (B.map (MulAut.conj : D →* MulAut D)) : Set (MulAut D)) *
      (MulAut.innerSubgroup D : Set (MulAut D))
  inner_part : I = (F ⊔ B.map (MulAut.conj : D →* MulAut D) ⊔ MulAut.innerSubgroup D) ⊓
    (innerDiagonal E).comap (MulAut.congr model).toMonoidHom

variable {E}

omit [Finite E] in
theorem RawConfiguration.inner_le_diagonal {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) :
    MulAut.innerSubgroup D ≤ (innerDiagonal E).comap (MulAut.congr c.model).toMonoidHom := by
  rintro _ ⟨x,rfl⟩
  change MulAut.congr c.model (MulAut.conj x) ∈ innerDiagonal E
  rw [MulAut.congr_conj]
  exact inner_le_innerDiagonal E ⟨_,rfl⟩

omit [Finite E] in
theorem RawConfiguration.subgroup_le_inner_part {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) : B.map (MulAut.conj : D →* MulAut D) ≤ c.I := by
  rw [c.inner_part]
  apply le_inf (le_sup_of_le_left le_sup_right)
  exact (show B.map (MulAut.conj : D →* MulAut D) ≤ MulAut.innerSubgroup D from
    by rintro _ ⟨x,_,rfl⟩; exact ⟨x,rfl⟩).trans c.inner_le_diagonal

omit [Finite E] in
theorem RawConfiguration.inner_le_inner_part {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) : MulAut.innerSubgroup D ≤ c.I := by
  rw [c.inner_part]
  exact le_inf le_sup_right c.inner_le_diagonal

omit [Finite E] in
/-- The normalizer is computed inside I, not inside the ambient automorphism group. -/
theorem RawConfiguration.relative_normalizer [IsSimpleGroup D]
    {n : ℕ} {U B : Subgroup D} (c : RawConfiguration E n U B)
    (hna : ¬ IsMulCommutative D) :
    normalizer ((U.map (MulAut.conj : D →* MulAut D)).subgroupOf c.I) =
      (autNormalizer U).subgroupOf c.I := by
  have hUI : U.map (MulAut.conj : D →* MulAut D) ≤ c.I := by
    rintro _ ⟨x,_,rfl⟩
    exact c.inner_le_inner_part ⟨x,rfl⟩
  rw [← subgroupOf_normalizer_eq hUI, ← autNormalizer_eq_normalizer_inner U
    (Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian D hna)]

/-- Disjointness is a consequence of genuine coefficient-field actions. -/
theorem RawConfiguration.field_inner_disjoint {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) : Disjoint c.F c.I := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using c.field_card)
  apply Subgroup.disjoint_def.mpr
  intro a haF haI
  apply (MulAut.congr c.model).injective
  rw [map_one]
  apply (SourceAlignment.field_inner_disjoint E).le_bot
  refine ⟨c.field_action (mem_map_of_mem _ haF), ?_⟩
  rw [c.inner_part] at haI
  exact haI.2

/-- The source equality removes the field factor after disjointness is established. -/
theorem RawConfiguration.field_eq_bot {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) : c.F = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hprod : a ∈ ((c.F : Set (MulAut D)) * B.map (MulAut.conj : D →* MulAut D)) *
      (MulAut.innerSubgroup D : Set (MulAut D)) := by
    exact ⟨a,⟨a,ha,1,one_mem _,mul_one a⟩,1,one_mem _,mul_one a⟩
  rw [c.product_eq] at hprod
  obtain ⟨hb,⟨h,hh,b,hb,rfl⟩,d,hd,he⟩ := hprod
  have hdiag : a ∈ (innerDiagonal E).comap (MulAut.congr c.model).toMonoidHom := by
    rw [← he]
    have hhI := c.cartan.inside hh
    rw [c.inner_part] at hhI
    have hbD : b ∈ MulAut.innerSubgroup D := by
      obtain ⟨x,_,rfl⟩ := hb
      exact ⟨x,rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhI.2 (c.inner_le_diagonal hbD))
      (c.inner_le_diagonal hd)
  apply c.field_inner_disjoint.le_bot
  refine ⟨ha, ?_⟩
  rw [c.inner_part]
  exact ⟨mem_sup_left (mem_sup_left ha),hdiag⟩

/-- The source subgroup lies in H; this is not a field of the raw configuration. -/
theorem RawConfiguration.subgroup_le_cartan {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) : B.map (MulAut.conj : D →* MulAut D) ≤ c.H := by
  exact le_cartan_of_field_inner_disjoint _ _ _ _ c.subgroup_le_inner_part
    c.cartan.inside c.field_inner_disjoint c.product

theorem RawConfiguration.subgroup_le_normalizer {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) : B ≤ normalizer U := by
  intro b hb
  apply (inner_mem_autNormalizer_iff U b).mp
  exact c.cartan.normalizes (c.subgroup_le_cartan (mem_map_of_mem _ hb))

omit [Finite E] in
/-- H is an odd Hall complement in the relative Borel, with a power-of-two index. -/
theorem RawConfiguration.cartan_odd_hall [Finite D] {n : ℕ} {U B : Subgroup D}
    (c : RawConfiguration E n U B) (hU : IsPGroup 2 U) :
    Odd (Nat.card (c.H.subgroupOf (c.I ⊓ autNormalizer U))) ∧
      ∃ k : ℕ, (c.H.subgroupOf (c.I ⊓ autNormalizer U)).index = 2 ^ k := by
  constructor
  · rw [Nat.card_congr (subgroupOfEquivOfLe
      (le_inf c.cartan.inside c.cartan.normalizes)).toEquiv]
    exact c.cartan.odd
  · rw [c.cartan.complement.index_eq_card]
    exact ((hU.map (MulAut.conj : D →* MulAut D)).comap_subtype).exists_card_eq

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment
