module

public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup

/-!
# The odd index of a normal natural SL₃ layer

The coefficient action embeds the quotient above its linear kernel in the
field automorphism group. On that kernel the determinant has kernel exactly
the given SL₃ layer: faithfulness and the specified natural action identify
every determinant-one actor with its corresponding matrix. Hence the index
divides `(2^m - 1) * m`, which is odd for positive odd m.

The final theorem applies this bound to arbitrary two-subgroups of the same
ambient action. These are the two arithmetic steps used for the literal
normalizer in `Theory.Representation.SL3OddNaturalNormalizer` and for the
natural-three localization in Aschbacher–Smith B.5.10(2), printed p.109 of
the combined manuscript (1 March 2004).
-/

public section
namespace Representation.SL3OddNaturalNormalizer
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- The automorphism group of the actual binary field has order its degree. -/
theorem binaryFieldAut_card {m : ℕ} (hc : Nat.card F = 2 ^ m) :
    Nat.card (F ≃+* F) = m := by
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod 2] F) := {
    toFun σ := AlgEquiv.ofRingEquiv (f := σ) (by
      intro x
      have hh : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun hh x)
    invFun σ := σ.toRingEquiv
    left_inv σ := by ext x; rfl
    right_inv σ := by ext x; rfl
    map_mul' σ τ := by ext x; rfl }
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
  apply Nat.pow_right_injective (by decide : 1 < 2)
  change 2 ^ Module.finrank (ZMod 2) F = 2 ^ m
  rw [← hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- The index of the specified faithful normal natural layer divides the
product of the multiplicative field order and the field degree. -/
theorem index_dvd_field_units_mul_degree {m : ℕ} (hc : Nat.card F = 2 ^ m)
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v) :
    L.index ∣ (2 ^ m - 1) * m := by
  let hsemi := normalizer_semilinear L e ρ hnat
  let φ := fieldAction ρ hsemi
  have hL : L ≤ φ.ker := by
    intro g hg
    apply (fieldAction_eq_one_iff ρ hsemi g).mpr
    intro c v
    change ρ (⟨g, hg⟩ : L) (c • v) = c • ρ (⟨g, hg⟩ : L) v
    rw [hnat, hnat, Matrix.mulVec_smul]
  let τ : Representation F φ.ker (Fin 3 → F) := {
    toFun g := {
      toFun := ρ (g : H)
      map_add' := (ρ (g : H)).map_add
      map_smul' := by
        intro c v
        exact (fieldAction_eq_one_iff ρ hsemi g).mp g.property c v }
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ρ.map_one v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (ρ.map_mul g h) v }
  let μ : φ.ker →* GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp τ.asGroupHom
  let δ : φ.ker →* Fˣ := Matrix.GeneralLinearGroup.det.comp μ
  have hμ (g : φ.ker) (v : Fin 3 → F) : (μ g).val.mulVec v = ρ (g : H) v := by
    change (Matrix.GeneralLinearGroup.toLin (μ g) : Module.End F (Fin 3 → F)) v = _
    have he : Matrix.GeneralLinearGroup.toLin (μ g) = τ.asGroupHom g :=
      Matrix.GeneralLinearGroup.toLin.apply_symm_apply _
    rw [he]
    rfl
  have hker : δ.ker = L.subgroupOf φ.ker := by
    ext g
    constructor
    · intro hg
      have hd : (μ g).val.det = 1 := congrArg Units.val hg
      let s : Matrix.SpecialLinearGroup (Fin 3) F := ⟨(μ g).val, hd⟩
      have he : (g : H) = (e.symm s : L) := by
        apply hfaith
        apply LinearMap.ext
        intro v
        rw [hnat, e.apply_symm_apply]
        exact (hμ g v).symm
      change (g : H) ∈ L
      rw [he]
      exact (e.symm s).property
    · intro hg
      have he : (μ g).val = (e ⟨g, hg⟩).val := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro v
        exact (hμ g v).trans (hnat ⟨g, hg⟩ v)
      apply Units.ext
      change (μ g).val.det = 1
      rw [he]
      exact (e ⟨g, hg⟩).property
  rw [← L.relIndex_mul_index hL]
  apply Nat.mul_dvd_mul
  · change (L.subgroupOf φ.ker).index ∣ _
    rw [← hker, Subgroup.index_ker]
    have hd := δ.range.card_subgroup_dvd_card
    simpa only [Nat.card_units, hc] using hd
  · rw [Subgroup.index_ker]
    exact (φ.range.card_subgroup_dvd_card).trans (dvd_of_eq (binaryFieldAut_card hc))

/-- Odd binary field degree forces the natural SL₃ layer to have odd index. -/
theorem odd_index_of_natural {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m)
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v) :
    Odd L.index := by
  apply Odd.of_dvd_nat _ (index_dvd_field_units_mul_degree hc L e ρ hfaith hnat)
  apply Odd.mul _ hodd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  refine ⟨2 ^ k - 1, ?_⟩
  have hp : 0 < 2 ^ k := by positivity
  rw [pow_succ]
  omega

/-- A two-subgroup of a faithful ambient natural action lies in its normal
SL₃ layer when the binary field degree is odd. -/
theorem two_subgroup_le_of_natural {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m)
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (A : Subgroup H) (hA : IsPGroup 2 A) : A ≤ L := by
  let : Finite (Module.End (ZMod 2) (Fin 3 → F)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Fin 3 → F) =>
      (f : (Fin 3 → F) → (Fin 3 → F))) DFunLike.coe_injective
  let : Finite H := Finite.of_injective ρ hfaith
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hi := odd_index_of_natural hm hodd hc L e ρ hfaith hnat
  rw [← Subgroup.relIndex_eq_one]
  apply Nat.eq_one_of_dvd_coprimes (hi.coprime_two_right.pow_right k)
  · exact L.relIndex_dvd_index_of_normal A
  · rw [← hk]
    exact L.relIndex_dvd_card A

end Representation.SL3OddNaturalNormalizer
