module

public import Theory.GroupTheory.WreathTwoSylowModel
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximality of Sylow two-subgroups in the concrete SL₂(2) wreath product

Every Sylow two-subgroup of `SL₂(2) ≀ᵣ C₂` is maximal. We first prove this
for the range of `wreathTwoDihedralHom`, retaining the actual matrix and wreath
carriers, and then transport it by Sylow conjugacy in the ambient group.

The standard Sylow contains a transvection in each base coordinate and the
factor swap. Removing the permutation part of an outside element leaves a
base element with a coordinate outside the transvection subgroup. Its
commutator with the transvection in that coordinate is one of the two
nonidentity elements of the cubic subgroup of `SL₂(2)`. Thus any proper
extension contains a cubic generator in one coordinate, and conjugation by
the swap supplies it in the other. The cubic generator and transvection
generate each whole base factor, so the extension is the whole wreath product.

Only identities on the six matrices, two coordinates, and eight elements of
the displayed dihedral group are checked by finite kernel reduction. The
argument for arbitrary overgroups uses subgroup closure under products and
inverses; it does not enumerate subgroups.

Source: the intrinsic maximality used in the proof of Aschbacher–Smith,
Lemma 15.3.2(4), combined manuscript (1 March 2004), printed p.1121/PDF p.1138.
-/

private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev Wreath := RegularWreathProduct SL2 C2
private instance : DecidableEq Wreath :=
  fun x y => decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    RegularWreathProduct.ext_iff.symm

private def transvection : SL2 := ⟨!![1, 1; 0, 1], by decide⟩
private def cubic : SL2 := ⟨!![0, 1; 1, 1], by decide⟩
private def coordinateSwitch : C2 := Multiplicative.ofAdd 1
private def swap : Wreath := RegularWreathProduct.inl coordinateSwitch
private def coordinate (i : C2) : SL2 →* Wreath where
  toFun x := ⟨fun j => if j = i then x else 1, 1⟩
  map_one' := by ext j <;> simp
  map_mul' x y := by
    ext j <;> simp only [RegularWreathProduct.mul_left,
      RegularWreathProduct.mul_right, inv_one, one_mul, Pi.mul_apply]
    split_ifs <;> simp

set_option maxRecDepth 10000 in
private theorem sl2_commutator : ∀ x : SL2, x ≠ 1 → x ≠ transvection →
    x * transvection * x⁻¹ * transvection⁻¹ = cubic ∨
      x * transvection * x⁻¹ * transvection⁻¹ = cubic⁻¹ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem sl2_generation : ∀ x : SL2,
    ∃ k : Fin 3, ∃ b : Bool, x = cubic ^ k.val * (if b then transvection else 1) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem coordinate_transvection_mem : ∀ i : C2, ∃ d : DihedralGroup 4,
    wreathTwoDihedralHom d = coordinate i transvection := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem pure_permutation_mem : ∀ q : C2, ∃ d : DihedralGroup 4,
    wreathTwoDihedralHom d = RegularWreathProduct.inl q := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem cubic_not_mem : ∀ d : DihedralGroup 4,
    wreathTwoDihedralHom d ≠ coordinate 1 cubic := by
  decide +kernel

private theorem coordinate_cases (q : C2) : q = 1 ∨ q = coordinateSwitch := by
  revert q
  decide +kernel

private theorem flip_ne_one : coordinateSwitch ≠ 1 := by decide

private theorem wreath_decomposition (g : Wreath) :
    g = coordinate 1 (g.left 1) * coordinate coordinateSwitch (g.left coordinateSwitch) * RegularWreathProduct.inl g.right := by
  ext j
  · rcases coordinate_cases j with rfl | rfl <;>
      simp [coordinate, flip_ne_one, Ne.symm flip_ne_one]
  · simp [coordinate]

private theorem swap_coordinate (i : C2) (x : SL2) :
    swap * coordinate i x * swap⁻¹ = coordinate (coordinateSwitch * i) x := by
  ext j
  · simp [swap, coordinate, inv_mul_eq_iff_eq_mul]
  · simp [swap, coordinate]

private theorem base_commutator (f : C2 → SL2) (i : C2) :
    (⟨f, 1⟩ : Wreath) * coordinate i transvection * (⟨f, 1⟩ : Wreath)⁻¹ *
        (coordinate i transvection)⁻¹ =
      coordinate i (f i * transvection * (f i)⁻¹ * transvection⁻¹) := by
  ext j
  · by_cases h : j = i
    · subst j
      simp [coordinate]
    · simp [coordinate, h]
  · simp [coordinate]

private theorem standard_isCoatom : IsCoatom wreathTwoDihedralHom.range := by
  apply SetLike.isCoatom_iff.mpr
  refine ⟨?_, ?_⟩
  · intro heq
    have hm : coordinate 1 cubic ∈ wreathTwoDihedralHom.range := heq ▸ Subgroup.mem_top _
    obtain ⟨d, hd⟩ := hm
    exact cubic_not_mem d hd
  intro K g hPK hg hgK
  have htK (i : C2) : coordinate i transvection ∈ K := hPK (coordinate_transvection_mem i)
  have hinlK (q : C2) : (RegularWreathProduct.inl q : Wreath) ∈ K := hPK (pure_permutation_mem q)
  have hsK : swap ∈ K := hinlK coordinateSwitch
  have hout : ∃ i : C2, g.left i ≠ 1 ∧ g.left i ≠ transvection := by
    by_contra! h
    apply hg
    rw [wreath_decomposition g]
    apply wreathTwoDihedralHom.range.mul_mem
    · apply wreathTwoDihedralHom.range.mul_mem
      · rcases eq_or_ne (g.left 1) 1 with he | he
        · simp [he]
        · rw [h 1 he]
          exact coordinate_transvection_mem 1
      · rcases eq_or_ne (g.left coordinateSwitch) 1 with he | he
        · simp [he]
        · rw [h coordinateSwitch he]
          exact coordinate_transvection_mem coordinateSwitch
    · exact pure_permutation_mem g.right
  obtain ⟨i, hi1, hit⟩ := hout
  have hbK : (⟨g.left, 1⟩ : Wreath) ∈ K := by
    have heq : (⟨g.left, 1⟩ : Wreath) = g * (RegularWreathProduct.inl g.right)⁻¹ := by
      ext j <;> simp
    rw [heq]
    exact K.mul_mem hgK (K.inv_mem (hinlK g.right))
  have hcomm := K.mul_mem (K.mul_mem (K.mul_mem hbK (htK i)) (K.inv_mem hbK))
    (K.inv_mem (htK i))
  rw [base_commutator] at hcomm
  have haK : coordinate i cubic ∈ K := by
    rcases sl2_commutator (g.left i) hi1 hit with he | he
    · rwa [he] at hcomm
    · rw [he, map_inv] at hcomm
      exact K.inv_mem_iff.mp hcomm
  have haK_all (j : C2) : coordinate j cubic ∈ K := by
    have hcases : j = i ∨ j = coordinateSwitch * i := by
      have hc : ∀ i j : C2, j = i ∨ j = coordinateSwitch * i := by decide +kernel
      exact hc i j
    rcases hcases with rfl | rfl
    · exact haK
    · rw [← swap_coordinate]
      exact K.mul_mem (K.mul_mem hsK haK) (K.inv_mem hsK)
  have hcoordK (j : C2) (x : SL2) : coordinate j x ∈ K := by
    obtain ⟨k, b, rfl⟩ := sl2_generation x
    rw [map_mul, map_pow]
    apply K.mul_mem (K.pow_mem (haK_all j) k.val)
    cases b
    · simp
    · exact htK j
  apply top_unique
  intro x _
  rw [wreath_decomposition x]
  exact K.mul_mem (K.mul_mem (hcoordK 1 _) (hcoordK coordinateSwitch _)) (hinlK x.right)

/-- Every Sylow two-subgroup of the concrete `SL₂(2) ≀ᵣ C₂` is maximal. -/
public theorem wreath_two_sylow_isCoatom
    (P : Sylow 2 (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) :
    IsCoatom (P : Subgroup (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Wreath wreathTwoSylow P
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, wreathTwoSylow_coe]
  exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr standard_isCoatom
