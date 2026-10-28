module

public import Theory.SpecificGroups.PSL3.CartanActions
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Simultaneous Sylow and torus alignment in PSL₃

An upper triangular determinant-one matrix factors as a unitriangular
matrix times diag(a,(ab)⁻¹,b). Their projective images intersect trivially,
so the published torus complements the unipotent subgroup in its Borel.
Its relative index is |E|³.

First Sylow conjugacy moves a supplied Sylow two-subgroup to the standard
unipotent subgroup. An odd p-subgroup of its normalizer acts on the Borel's
cosets of the torus. The index is a power of two, so the p-group has a
fixed coset. The resulting conjugator lies in the Borel and therefore
preserves the first alignment. This proves both conclusions for the same
actual multiplicative equivalence; no Cartan-conjugacy assumption is used.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.15(5),
printed pp.50–51, and the linear case of Proposition 1.3.4, printed p.511.
-/

public section

open scoped MatrixGroups Pointwise
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment

variable (E : Type*) [Field E] [Finite E]

private theorem borelSL_factor (g : SL(3,E)) (hg : g ∈ borelSL E) :
    ∃ u ∈ unipotentSL E, ∃ d : Eˣ × Eˣ, g = u * torusSL E d := by
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff E g).mp hg
  have hdet : g.val 0 0 * g.val 1 1 * g.val 2 2 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_three, h10,h20,h21] at h
    simpa only [zero_mul, mul_zero, add_zero, sub_zero] using h
  have h00 : g.val 0 0 ≠ 0 := by intro h; simp [h] at hdet
  have h22 : g.val 2 2 ≠ 0 := by intro h; simp [h] at hdet
  let d : Eˣ × Eˣ := (Units.mk0 (g.val 0 0) h00, Units.mk0 (g.val 2 2) h22)
  let u := g * torusSL E d⁻¹
  refine ⟨u, ?_, d, ?_⟩
  · rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
    simp [u, Matrix.SpecialLinearGroup.coe_mul, torusSL_val,
      Matrix.mul_diagonal, d, h10,h20,h21,h00,h22]
  · dsimp [u]
    rw [map_inv, inv_mul_cancel_right]

private theorem borel_factor (x : PSL(3,E)) (hx : x ∈ borel E) :
    ∃ u ∈ unipotent E, ∃ t ∈ torus E, x = u * t := by
  obtain ⟨g,hg,rfl⟩ := hx
  obtain ⟨u,hu,d,rfl⟩ := borelSL_factor E g hg
  exact ⟨projection E u, mem_map_of_mem _ hu, torusMap E d, ⟨d,rfl⟩, map_mul _ _ _⟩

omit [Finite E] in
theorem torus_disjoint_unipotent : Disjoint (unipotent E) (torus E) := by
  apply Subgroup.disjoint_def.mpr
  rintro x ⟨u,hu,rfl⟩ ⟨d,hd⟩
  have he : projection E (torusSL E d) = projection E u := hd
  have hc := (projection E).eq_iff.mp he.symm
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hm : u.val = (torusSL E d).val * Matrix.scalar (Fin 3) r := by
    calc
      u.val = (torusSL E d * ((torusSL E d)⁻¹ * u)).val := by simp
      _ = _ := by rw [Matrix.SpecialLinearGroup.coe_mul, ← hr]
  have hoff (i j : Fin 3) (hij : i ≠ j) : u.val i j = 0 := by
    rw [hm, torusSL_val]
    simp [Matrix.scalar, Matrix.mul_diagonal, hij]
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [(mem_unipotentSL_iff E u).mp hu]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hoff]
  simp [hu1]


theorem unipotent_sup_torus : unipotent E ⊔ torus E = borel E := by
  apply le_antisymm (sup_le (unipotent_le_borel E) (torus_le_borel E))
  intro x hx
  obtain ⟨u,hu,t,ht,rfl⟩ := borel_factor E x hx
  exact Subgroup.mul_mem _ (mem_sup_left hu) (mem_sup_right ht)

theorem torus_index_in_borel :
    ((torus E).subgroupOf (borel E)).index = Nat.card E ^ 3 := by
  have hnorm : torus E ≤ normalizer (unipotent E) :=
    (torus_le_borel E).trans (borel_le_normalizer_unipotent E)
  have hcard : Nat.card (borel E) = Nat.card (unipotent E) * Nat.card (torus E) := by
    rw [← unipotent_sup_torus E]
    exact card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm (torus_disjoint_unipotent E)
  have hc := ((torus E).subgroupOf (borel E)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel E)).toEquiv,
    hcard, card_unipotent E, mul_comm (Nat.card E ^ 3)] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

theorem torus_complement :
    IsComplement' ((unipotent E).subgroupOf (borel E))
      ((torus E).subgroupOf (borel E)) := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro x hx hu
    exact Subtype.ext ((torus_disjoint_unipotent E).le_bot ⟨hx,hu⟩)
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨u,hu,t,ht,he⟩ := borel_factor E x x.property
    exact ⟨⟨u,unipotent_le_borel E hu⟩,hu,⟨t,torus_le_borel E ht⟩,ht,Subtype.ext he.symm⟩

private theorem conjugate_le_of_index {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (A C : Subgroup G) (hA : IsPGroup p A)
    (hC : ¬ p ∣ C.index) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ C := by
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ C) hC
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have he : (g : G ⧸ C) = (a * g : G) := (hx (⟨a, ha⟩ : A)).symm
  change g⁻¹ * a * (g⁻¹)⁻¹ ∈ C
  simpa only [inv_inv, mul_assoc] using QuotientGroup.eq.mp he

theorem exists_borel_conjugation {n p : ℕ} [Fact p.Prime]
    (hE : Nat.card E = 2 ^ n) (hp : p ≠ 2)
    (B : Subgroup PSL(3,E)) (hB : IsPGroup p B) (hBN : B ≤ borel E) :
    ∃ g ∈ borel E, B.map (MulAut.conj g).toMonoidHom ≤ torus E := by
  have hnot : ¬ p ∣ ((torus E).subgroupOf (borel E)).index := by
    rw [torus_index_in_borel E, hE, ← pow_mul]
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  obtain ⟨g,hg⟩ := conjugate_le_of_index (B.subgroupOf (borel E))
    ((torus E).subgroupOf (borel E)) hB.comap_subtype hnot
  refine ⟨g,g.property,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  exact hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show (⟨b,hBN hb⟩ : borel E) ∈ B.subgroupOf (borel E) from hb))

theorem exists_simultaneous_alignment {D : Type*} [Group D] [Finite D]
    (e : D ≃* PSL(3,E)) {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hE : Nat.card E = 2 ^ n) (hp : p ≠ 2)
    (T : Sylow 2 D) (B : Subgroup D) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (T : Subgroup D)) :
    ∃ e' : D ≃* PSL(3,E), (T : Subgroup D).map e'.toMonoidHom = unipotent E ∧
      B.map e'.toMonoidHom ≤ torus E := by
  let V := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,E) V (unipotentSylow E hn hE)
  let e₁ := e.trans (MulAut.conj g)
  have hT : (T : Subgroup D).map e₁.toMonoidHom = unipotent E := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((T : Subgroup D).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    rw [Subgroup.map_map, coe_unipotentSylow] at hh
    exact hh
  have hB₁ : B.map e₁.toMonoidHom ≤ borel E := by
    rw [← normalizer_unipotent E hn hE, ← hT, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hBN
  obtain ⟨a,ha,hBa⟩ := exists_borel_conjugation E hE hp
    (B.map e₁.toMonoidHom) (hB.map _) hB₁
  refine ⟨e₁.trans (MulAut.conj a), ?_, ?_⟩
  · change (T : Subgroup D).map ((MulAut.conj a).toMonoidHom.comp e₁.toMonoidHom) = _
    rw [← Subgroup.map_map, hT]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (borel_le_normalizer_unipotent E ha))
  · change B.map ((MulAut.conj a).toMonoidHom.comp e₁.toMonoidHom) ≤ _
    simpa only [Subgroup.map_map] using hBa

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment
