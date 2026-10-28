module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.Data
public import Theory.Mathieu.M22.Properties.Order
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# A finite paired ATLAS model and its native M₂₂ projection

Generate a subgroup of Sym(4928) × Sym(22) by the two literal ATLAS
permutations paired with the native standard generators. The second projection
is onto the Steiner-defined M₂₂ because its two generators generate that group.
Four explicit permutation relations suffice for perfectness: in every abelian
image, AB has order dividing both four and eleven, and ABABB then kills B.

The distinguished word has trivial native image. Its exact order, centrality
and exhaustion of the kernel remain separate certificate obligations.
Source: Aschbacher–Smith I.1.1 and I.1.3(4), printed p.407; ATLAS data as
attributed in `Data.lean` and its retained source files.
-/

namespace Sporadic.Mathieu.M22CyclicFour

private theorem trivial_of_relations {C : Type*} [CommGroup C] (a b : C)
    (ha : a ^ 2 = 1) (hb : b ^ 4 = 1)
    (hab : (a * b) ^ 11 = 1) (hababb : (a * b * a * b * b) ^ 11 = 1) :
    a = 1 ∧ b = 1 := by
  have hab4 : (a * b) ^ 4 = 1 := by
    rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha, one_pow]
    simpa using hb
  have hab1 : a * b = 1 := by
    have hd : orderOf (a * b) ∣ Nat.gcd 4 11 := Nat.dvd_gcd
      (orderOf_dvd_of_pow_eq_one hab4) (orderOf_dvd_of_pow_eq_one hab)
    have ho : orderOf (a * b) = 1 := Nat.dvd_one.mp hd
    exact orderOf_eq_one_iff.mp ho
  have hword : a * b * a * b * b = b := by simp only [hab1, one_mul]
  have hb1 : b = 1 := by
    rw [hword] at hababb
    have hd : orderOf b ∣ Nat.gcd 4 11 := Nat.dvd_gcd
      (orderOf_dvd_of_pow_eq_one hb) (orderOf_dvd_of_pow_eq_one hababb)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  exact ⟨by simpa [hb1] using hab1, hb1⟩

private theorem perfect_of_relations {G : Type*} [Group G] (a b : G)
    (hgen : Subgroup.closure {a,b} = ⊤)
    (ha : a ^ 2 = 1) (hb : b ^ 4 = 1)
    (hab : (a * b) ^ 11 = 1) (hababb : (a * b * a * b * b) ^ 11 = 1) :
    Group.IsPerfect G := by
  let q : G →* Abelianization G := Abelianization.of
  have h := trivial_of_relations (q a) (q b)
    (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (by rw [← map_mul, ← map_pow, hab, map_one])
    (by simp only [← map_mul, ← map_pow, hababb, map_one])
  refine ⟨top_le_iff.mp ?_⟩
  rw [← hgen, ← Abelianization.ker_of, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact h.1
  · exact h.2


@[expose] public section

/-- The first literal generator with its specified native image. -/
noncomputable def pairA : Equiv.Perm (Fin 4928) × Equiv.Perm (Fin 22) :=
  (Data.aPerm, m22GeneratorA)

/-- The second literal generator with its specified native image. -/
noncomputable def pairB : Equiv.Perm (Fin 4928) × Equiv.Perm (Fin 22) :=
  (Data.bPerm, m22GeneratorB)

/-- The actual finite candidate group; no multiplier assertion enters its definition. -/
noncomputable def Model : Subgroup (Equiv.Perm (Fin 4928) × Equiv.Perm (Fin 22)) :=
  Subgroup.closure {pairA, pairB}

noncomputable def ambientProjection : Model →* Equiv.Perm (Fin 22) :=
  (MonoidHom.snd _ _).comp Model.subtype

/-- The native image is the whole Steiner-defined M₂₂. -/
theorem ambientProjection_range : ambientProjection.range = M22 := by
  rw [ambientProjection, MonoidHom.range_comp, Subgroup.range_subtype, Model,
    MonoidHom.map_closure]
  simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_snd,
    pairA, pairB] using (m22Atlas_eq_closure.symm.trans m22Atlas_eq_M22)

/-- Restriction of the literal second projection to the native Mathieu group. -/
noncomputable def projection : Model →* M22 :=
  ambientProjection.codRestrict M22 (by
    intro x
    rw [← ambientProjection_range]
    exact ⟨x, rfl⟩)

theorem projection_surjective : Function.Surjective projection := by
  intro x
  have hx : (x : Equiv.Perm (Fin 22)) ∈ ambientProjection.range := by
    rw [ambientProjection_range]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

noncomputable def generatorA : Model := ⟨pairA, Subgroup.subset_closure (by simp)⟩
noncomputable def generatorB : Model := ⟨pairB, Subgroup.subset_closure (by simp)⟩

theorem generators_closure : Subgroup.closure {generatorA, generatorB} = ⊤ := by
  apply Subgroup.map_injective Model.subtype_injective
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  change Model = (⊤ : Subgroup Model).map Model.subtype
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- A certificate consisting of four raw permutation identities gives perfectness
of the actual paired group. These identities are not yet assumed as instances. -/
theorem perfect_of_generator_relations
    (ha : Data.aPerm ^ 2 = 1) (hb : Data.bPerm ^ 4 = 1)
    (hab : (Data.aPerm * Data.bPerm) ^ 11 = 1)
    (hababb : (Data.aPerm * Data.bPerm * Data.aPerm * Data.bPerm * Data.bPerm) ^ 11 = 1) :
    Group.IsPerfect Model := by
  apply perfect_of_relations generatorA generatorB generators_closure
  · apply Subtype.ext
    refine Prod.ext ha ?_
    change m22GeneratorA ^ 2 = 1
    rw [← m22GeneratorA_order]
    exact pow_orderOf_eq_one _
  · apply Subtype.ext
    refine Prod.ext hb ?_
    change m22GeneratorB ^ 4 = 1
    rw [← m22GeneratorB_order]
    exact pow_orderOf_eq_one _
  · apply Subtype.ext
    refine Prod.ext hab ?_
    change (m22GeneratorA * m22GeneratorB) ^ 11 = 1
    decide +kernel
  · apply Subtype.ext
    refine Prod.ext hababb ?_
    change (m22GeneratorA * m22GeneratorB * m22GeneratorA * m22GeneratorB *
      m22GeneratorB) ^ 11 = 1
    decide +kernel

/-- The specific candidate for the generator of the cyclic-four kernel. -/
noncomputable def centralWord : Model :=
  (generatorA * generatorB * generatorA * generatorB * generatorA * generatorB⁻¹) ^ 5

/-- The displayed word has trivial native image, independently of recognition. -/
theorem centralWord_mem_kernel : centralWord ∈ projection.ker := by
  change projection centralWord = 1
  simp only [centralWord, map_pow, map_mul, map_inv]
  apply Subtype.ext
  change (m22GeneratorA * m22GeneratorB * m22GeneratorA * m22GeneratorB *
    m22GeneratorA * m22GeneratorB⁻¹) ^ 5 = 1
  decide +kernel

theorem centralWord_zpowers_le_kernel : Subgroup.zpowers centralWord ≤ projection.ker :=
  Subgroup.zpowers_le.mpr centralWord_mem_kernel

end
end Sporadic.Mathieu.M22CyclicFour
