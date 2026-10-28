module
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.Representation.SpecialLinearNatural

/-!
# Irreducibility above a natural Sylow fixed line

In the natural plane for SL₂ in characteristic two, an additive subgroup
containing the Sylow fixed line and invariant under its normalizer is either
the fixed line or the whole plane. In standard coordinates the diagonal torus
supplies every nonzero second coordinate, and subtraction supplies the first.
Sylow conjugacy transports this calculation to the specified Sylow subgroup.

Source application: Aschbacher–Smith, 5.1.17, printed p.640, verification
of G.2.1 on the literal natural module (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SpecialLinearTwo
variable {F : Type*} [Field F]

private theorem upper_fixed_iff (v : Fin 2 → F) :
    (∀ g ∈ upperUnipotent F, toLin' g v = v) ↔ v 1 = 0 := by
  constructor
  · intro hv
    have hh := congrFun (hv (transvection zero_ne_one (1 : F))
      ((mem_upperUnipotent F _).mpr ⟨1, rfl⟩)) 0
    simpa [toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, transvection_coe] using hh
  · intro hv g hg
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F g).mp hg
    funext i
    fin_cases i <;>
      simp [toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, transvection_coe, hv]

private theorem upper_borel_invariant (W : AddSubgroup (Fin 2 → F))
    (hfixed : ∀ v, v 1 = 0 → v ∈ W)
    (hn : ∀ g ∈ rankOneBorel F, ∀ v ∈ W, toLin' g v ∈ W) :
    (∀ v ∈ W, v 1 = 0) ∨ W = ⊤ := by
  classical
  by_cases hh : ∀ v ∈ W, v 1 = 0
  · exact Or.inl hh
  push Not at hh
  obtain ⟨v,hv,hv1⟩ := hh
  right
  apply top_unique
  intro w _
  by_cases hw : w 1 = 0
  · exact hfixed w hw
  let a := v 1 / w 1
  have ha : a ≠ 0 := div_ne_zero hv1 hw
  let u := toLin' (diag2 a ha) v
  have hu : u ∈ W := hn _ (diag_mem_rankOneBorel a ha) v hv
  have hu1 : u 1 = w 1 := by
    dsimp only [u]
    simp [toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, diag2_coe', a, hv1]
  have he : w - u ∈ W := hfixed _ (by simp only [Pi.sub_apply,hu1,sub_self])
  simpa only [sub_add_cancel] using W.add_mem he hu

/-- The normalizer of a Sylow two-subgroup acts irreducibly above its natural fixed line. -/
theorem sylow_normalizer_invariant_interval [Finite F] [CharP F 2]
    (P : Sylow 2 SL(2,F)) (W : AddSubgroup (Fin 2 → F))
    (hfixed : ∀ v, (∀ g ∈ (P : Subgroup SL(2,F)), toLin' g v = v) → v ∈ W)
    (hn : ∀ g ∈ normalizer (P : Set SL(2,F)), ∀ v ∈ W, toLin' g v ∈ W) :
    (∀ v ∈ W, ∀ g ∈ (P : Subgroup SL(2,F)), toLin' g v = v) ∨ W = ⊤ := by
  obtain ⟨a,rfl⟩ := MulAction.exists_smul_eq SL(2,F) (upperUnipotentSylow F 2) P
  let Y := W.comap (toLin' a).toAddMonoidHom
  have hP (g : SL(2,F)) :
      g ∈ (a • upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) ↔
        ∃ b ∈ upperUnipotent F, a * b * a⁻¹ = g := by
    change g ∈ ((a • upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) : Subgroup _) ↔ _
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hyfix : ∀ v, v 1 = 0 → v ∈ Y := by
    intro v hv
    apply hfixed
    intro g hg
    obtain ⟨b,hb,rfl⟩ := (hP g).mp hg
    have he := (upper_fixed_iff v).mpr hv b hb
    simpa using congrArg (toLin' a) he
  have hyn : ∀ g ∈ rankOneBorel F, ∀ v ∈ Y, toLin' g v ∈ Y := by
    intro g hg v hv
    have hng : a * g * a⁻¹ ∈ normalizer
        ((a • upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) : Set SL(2,F)) := by
      have hm := mem_map_of_mem (MulAut.conj a).toMonoidHom hg
      rw [map_equiv_normalizer_eq] at hm
      exact hm
    have he := hn _ hng (toLin' a v) hv
    change toLin' a (toLin' g v) ∈ W
    simpa using he
  rcases upper_borel_invariant Y hyfix hyn with hy | hy
  · left
    intro v hv g hg
    obtain ⟨b,hb,rfl⟩ := (hP g).mp hg
    have hvY : toLin' a⁻¹ v ∈ Y := by change toLin' a (toLin' a⁻¹ v) ∈ W; simpa using hv
    have he := (upper_fixed_iff _).mpr (hy _ hvY) b hb
    simpa using congrArg (toLin' a) he
  · right
    apply top_unique
    intro v _
    have hv : toLin' a⁻¹ v ∈ Y := hy.ge (AddSubgroup.mem_top _)
    change toLin' a (toLin' a⁻¹ v) ∈ W at hv
    simpa using hv
end Representation.SpecialLinearTwo
