module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.ScalarCoinvariants

/-!
# Fixed vectors of the symplectic Sylow action

Literal root coordinates turn fixedness into three scalar equations. The
index bound sixteen forces a two-dimensional fixed space. If a subgroup
moves the first outside coordinate, those equations place it in a unique
finite-parameter plane subgroup and force moving index sixteen.

The same index is obtained after restriction to the binary field. This
keeps arbitrary binary subgroups, rather than assuming linearity over F4,
in the MS93 (5.4) small-mover classification (printed p.915).
-/

@[expose] public section
open Subgroup Matrix Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2]
abbrev Vector := (Fin 2 ⊕ Fin 2) → F
noncomputable abbrev natural : Representation F (unipotent (F := F)) (Vector (F := F)) :=
  (symplecticNatural 2).comp (unipotent (F := F)).subtype
noncomputable abbrev fixed (E : Subgroup (unipotent (F := F))) : Submodule F (Vector (F := F)) :=
  invariants (natural.comp E.subtype)

theorem element_fixed_iff (b u w v : F) (x : Vector (F := F)) :
    natural (element b u w v) x = x ↔
      b*x (.inl 1) + u*x (.inr 0) + (w+b*v)*x (.inr 1)=0 ∧
      w*x (.inr 0) + v*x (.inr 1)=0 ∧ b*x (.inr 0)=0 := by
  change (element b u w v).val.val *ᵥ x = x ↔ _
  rw [element_matrix]
  simp only [funext_iff, Sum.forall, Fin.forall_fin_two,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply,
    one_mul, zero_mul, zero_add, add_zero]
  constructor
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    refine ⟨?_,?_,?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h4
  · rintro ⟨h1,h2,h3⟩
    constructor
    · constructor
      · linear_combination h1
      · linear_combination h2
    · constructor
      · trivial
      · linear_combination h3

theorem mem_fixed_iff [Finite F] (E : Subgroup (unipotent (F := F))) (x : Vector (F := F)) :
    x ∈ fixed E ↔ ∀ b u w v, element b u w v ∈ E →
      b*x (.inl 1) + u*x (.inr 0) + (w+b*v)*x (.inr 1)=0 ∧
      w*x (.inr 0) + v*x (.inr 1)=0 ∧ b*x (.inr 0)=0 := by
  simp only [fixed, mem_invariants]
  constructor
  · intro hx b u w v h
    exact (element_fixed_iff b u w v x).mp (hx ⟨_,h⟩)
  · intro hx g
    obtain ⟨⟨b,u,w,v⟩,hg⟩ := element_surjective g.val
    have he : natural g.val x=x := by
      rw [←hg]
      exact (element_fixed_iff b u w v x).mpr (hx b u w v (by simpa only [hg] using g.property))
    exact he
noncomputable def movingIndex (E : Subgroup (unipotent (F := F))) : ℕ :=
  Nat.card F ^ Module.finrank F (Vector (F := F) ⧸ fixed E)

omit [CharP F 2] in
theorem movingIndex_mul_card_fixed [Finite F] (E : Subgroup (unipotent (F := F))) :
    movingIndex E * Nat.card (fixed E) = Nat.card F ^ 4 := by
  rw [movingIndex, Module.natCard_eq_pow_finrank (K := F) (V := fixed E), ←pow_add,
    (fixed E).finrank_quotient_add_finrank]
  congr 1
  simp [Vector, Module.finrank_fintype_fun_eq_card]

omit [CharP F 2] in
theorem finrank_fixed_ge_two [Finite F] (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hE : movingIndex E ≤ 16) :
    2 ≤ Module.finrank F (fixed E) := by
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E) ≤ 2 := by
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (4:ℕ))).mp
    simpa [movingIndex,hF] using hE
  have hh := (fixed E).finrank_quotient_add_finrank
  have hdim : Module.finrank F (Vector (F := F)) = 4 := by
    simp [Vector, Module.finrank_fintype_fun_eq_card]
  rw [hdim] at hh
  omega

omit [CharP F 2] in
theorem fixed_finrank_le_one_of_three_zero (E : Subgroup (unipotent (F := F)))
    (h : ∀ x ∈ fixed E, x (.inl 1)=0 ∧ x (.inr 0)=0 ∧ x (.inr 1)=0) :
    Module.finrank F (fixed E) ≤ 1 := by
  let p : fixed E →ₗ[F] F := (LinearMap.proj (.inl 0)).comp (fixed E).subtype
  have hp : Function.Injective p := by
    intro x y he
    apply Subtype.ext
    funext i
    rcases i with i | i <;> fin_cases i
    · exact he
    · exact (h x x.property).1.trans (h y y.property).1.symm
    · exact (h x x.property).2.1.trans (h y y.property).2.1.symm
    · exact (h x x.property).2.2.trans (h y y.property).2.2.symm
  simpa using LinearMap.finrank_le_finrank_of_injective hp

omit [CharP F 2] in
theorem binary_movingIndex [Finite F] [Algebra (ZMod 2) F]
    (E : Subgroup (unipotent (F := F))) :
    2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2) natural) E = movingIndex E := by
  rw [BinaryOffender.fixedCodim_restrictScalars, movingIndex, pow_mul]
  have hc : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [←hc]

theorem exists_plane_coordinates_of_not_le_wing [Finite F] (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hE : movingIndex E ≤ 16)
    (hout : ¬ E ≤ wing true) :
    ∃ lam : F, ∀ b u w v, element b u w v ∈ E → v=0 ∧ w=lam*b := by
  obtain ⟨g,hg,hgb⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hgb
  have hz : ∀ x ∈ fixed E, x (.inr 0)=0 := by
    intro x hx
    exact (mul_eq_zero.mp (((mem_fixed_iff E x).mp hx b u w v hg).2.2)).resolve_left hb
  have ht : ∃ x : fixed E, (x:Vector (F := F)) (.inr 1) ≠ 0 := by
    by_contra hnone
    have hzero : ∀ x : fixed E, (x:Vector (F := F)) (.inr 1)=0 := by
      simpa only [not_exists,not_not] using hnone
    have hdim := fixed_finrank_le_one_of_three_zero E (by
      intro x hx
      have ht : x (.inr 1)=0 := hzero ⟨x,hx⟩
      have hh := ((mem_fixed_iff E x).mp hx b u w v hg).1
      rw [hz x hx,ht,mul_zero,mul_zero,add_zero,add_zero] at hh
      exact ⟨(mul_eq_zero.mp hh).resolve_left hb,hz x hx,ht⟩)
    have htwo := finrank_fixed_ge_two hF E hE
    omega
  obtain ⟨x,hxt⟩ := ht
  refine ⟨-x.val (.inl 1)/x.val (.inr 1),?_⟩
  intro c z t a hc
  have hfix := (mem_fixed_iff E x.val).mp x.property c z t a hc
  have hzero := hz x.val x.property
  have ha : a=0 := by
    have hh := hfix.2.1
    rw [hzero,mul_zero,zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_right hxt
  refine ⟨ha,?_⟩
  have hh := hfix.1
  rw [hzero,ha,mul_zero,add_zero,mul_zero,add_zero] at hh
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hxt).mpr
  calc
    t * x.val (.inr 1) = -(c*x.val (.inl 1)) := eq_neg_of_add_eq_zero_right hh
    _ = -x.val (.inl 1)*c := by ring

theorem finrank_fixed_le_two_of_not_le_wing [Finite F]
    (E : Subgroup (unipotent (F := F))) (hout : ¬ E ≤ wing true) :
    Module.finrank F (fixed E) ≤ 2 := by
  obtain ⟨g,hg,hgb⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hgb
  have hz : ∀ x ∈ fixed E, x (.inr 0)=0 := by
    intro x hx
    exact (mul_eq_zero.mp (((mem_fixed_iff E x).mp hx b u w v hg).2.2)).resolve_left hb
  let p : fixed E →ₗ[F] F × F :=
    ((LinearMap.proj (.inl 0)).comp (fixed E).subtype).prod
      ((LinearMap.proj (.inr 1)).comp (fixed E).subtype)
  have hp : Function.Injective p := by
    intro x y he
    have h0 : x.val (.inl 0)=y.val (.inl 0) := congrArg Prod.fst he
    have ht : x.val (.inr 1)=y.val (.inr 1) := congrArg Prod.snd he
    have hx := ((mem_fixed_iff E x.val).mp x.property b u w v hg).1
    have hy := ((mem_fixed_iff E y.val).mp y.property b u w v hg).1
    rw [hz x x.property,mul_zero,add_zero] at hx
    rw [hz y y.property,mul_zero,add_zero,←ht] at hy
    have h1 : x.val (.inl 1)=y.val (.inl 1) := by
      apply (mul_left_cancel₀ hb)
      linear_combination hx-hy
    apply Subtype.ext
    funext i
    rcases i with i | i <;> fin_cases i
    · exact h0
    · exact h1
    · exact (hz x x.property).trans (hz y y.property).symm
    · exact ht
  simpa using LinearMap.finrank_le_finrank_of_injective hp

theorem movingIndex_eq_sixteen_of_not_le_wing [Finite F] (hF : Nat.card F=4)
    (E : Subgroup (unipotent (F := F))) (hE : movingIndex E ≤ 16)
    (hout : ¬ E ≤ wing true) : movingIndex E = 16 := by
  have heq : Module.finrank F (fixed E)=2 :=
    le_antisymm (finrank_fixed_le_two_of_not_le_wing E hout) (finrank_fixed_ge_two hF E hE)
  have hh := (fixed E).finrank_quotient_add_finrank
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed E)=2 := by
    rw [hdim,heq] at hh
    omega
  norm_num [movingIndex,hF,hquot]

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
