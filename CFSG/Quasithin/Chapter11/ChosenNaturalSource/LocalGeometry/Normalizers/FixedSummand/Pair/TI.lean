module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transport

/-!
# The fixed-summand TI argument on the source quotient

An order-generated subgroup L=theta(M) absorbs every conjugate L^g that
lies in M. If a nontrivial intersection of two conjugates of C_{Z1}(L)
occurs, uniqueness over L puts its centralizer in M. Thus g normalizes L,
and also the original fixed summand. Transport along Y -> Y/C_Y(Z1)
gives disjointness of distinct subspaces in the actual fixed-space orbit.

The theta equality and uniqueness over L are explicit source obligations.
The already proved equality N_Y(ZC)=Y intersect M alone does not give TI.
Source: Aschbacher--Smith, 11.1.5, printed p.766, using 11.0.4 and 4.2.13.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G]

/-- The source order-generated subgroup, in the original ambient group. -/
def theta (Δ : Set ℕ) (H : Subgroup G) : Subgroup G :=
  closure {x : G | x ∈ H ∧ orderOf x ∈ Δ}

/-- The exact order set in the Cartan/TI paragraph, including the odd-degree
full SL3 branch; all remaining cases use elements of order three. -/
def sourceOrders (L : Subgroup G) (n : ℕ) : Set ℕ := by
  classical
  exact if Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ n) ∧ Odd n then
    {d : ℕ | d ∣ 2 ^ n - 1} else {3}

omit [Finite G] in
theorem theta_le (Δ : Set ℕ) (H : Subgroup G) : theta Δ H ≤ H :=
  (closure_le _).mpr fun _ h => h.1

omit [Finite G] in
theorem conjugate_le_theta {Δ : Set ℕ} {L M : Subgroup G}
    (hθ : theta Δ M = L) (e : G ≃* G) (he : L.map e.toMonoidHom ≤ M) :
    L.map e.toMonoidHom ≤ L := by
  conv_lhs => rw [← hθ, theta, MonoidHom.map_closure]
  apply (closure_le _).mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← hθ]
  apply Subgroup.subset_closure
  exact ⟨he (mem_map_of_mem _ (hθ ▸ Subgroup.subset_closure hx)),
    (e.orderOf_eq x).symm ▸ hx.2⟩

theorem normalizes_of_conjugate_le {Δ : Set ℕ} {L M : Subgroup G}
    (hθ : theta Δ M = L) (g : G) (hg : L.map (MulAut.conj g).toMonoidHom ≤ M) :
    g ∈ normalizer (L : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge (conjugate_le_theta hθ (MulAut.conj g) hg)
  rw [card_map_of_injective (MulAut.conj g).injective]

theorem fixedCenter_ti_of_control {R L : Subgroup G} {Δ : Set ℕ}
    (hθ : theta Δ (normalizer (L : Set G)) = L)
    (hcontrol : ∀ U : Subgroup G, U ≤ radicalFixedCenter R L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G)) (g : G) (hg : g ∈ normalizer (R : Set G)) :
    radicalFixedCenter R L ⊓
        (radicalFixedCenter R L).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (radicalFixedCenter R L).map (MulAut.conj g).toMonoidHom = radicalFixedCenter R L := by
  let Z := radicalFixedCenter R L
  let U := Z ⊓ Z.map (MulAut.conj g).toMonoidHom
  by_cases hU : U = ⊥
  · exact Or.inl hU
  have hCM := hcontrol U inf_le_left hU
  have hconj : L.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    apply le_trans (show U ≤ Z.map (MulAut.conj g).toMonoidHom from inf_le_right)
    exact (map_mono (show Z ≤ centralizer (L : Set G) from inf_le_right)).trans
      (map_centralizer_le_centralizer_image _ _)
  have hgL := normalizes_of_conjugate_le hθ g (hconj.trans hCM)
  have hgZ : g ∈ normalizer (Z : Set G) :=
    inf_normalizer_le_normalizer_inf
      ⟨normalizes_omegaCenter R hg, normalizer_le_normalizer_centralizer L hgL⟩
  exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hgZ)

/-- The source uniqueness assertion over L supplies exactly the centralizer
control used by the TI argument. No Sylow-normality of U is needed. -/
theorem fixedCenter_centralizer_control_of_unique {R L : Subgroup G}
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N →
      N = normalizer (L : Set G))
    (U : Subgroup G) (hUZ : U ≤ radicalFixedCenter R L) (hU : U ≠ ⊥) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hLU : L ≤ centralizer (U : Set G) :=
    le_centralizer_iff.mp (hUZ.trans inf_le_right)
  have hP : IsPGroup 2 U :=
    (IsElementaryAbelian.isPGroup 2 (radicalOmegaCenter R)).of_injective
      (inclusion (hUZ.trans inf_le_left)) (inclusion_injective _)
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal hunique hP hU
      (hLU.trans (Subgroup.centralizer_le_normalizer _)))

/-- The printed source TI argument, retaining uniqueness over L explicitly. -/
theorem fixedCenter_ti {R L : Subgroup G} {Δ : Set ℕ}
    (hθ : theta Δ (normalizer (L : Set G)) = L)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N →
      N = normalizer (L : Set G)) (g : G) (hg : g ∈ normalizer (R : Set G)) :
    radicalFixedCenter R L ⊓
        (radicalFixedCenter R L).map (MulAut.conj g).toMonoidHom = ⊥ ∨
      (radicalFixedCenter R L).map (MulAut.conj g).toMonoidHom = radicalFixedCenter R L :=
  fixedCenter_ti_of_control hθ (fixedCenter_centralizer_control_of_unique hunique) g hg

omit [Finite G] in
theorem mem_map_fixedSubspace (R L : Subgroup G)
    (y : normalizer (R : Set G)) (z : Additive (radicalOmegaCenter R)) :
    z ∈ (fixedSubspace R L).map (representation R (projection R y)) ↔
      (z.toMul : G) ∈ (radicalFixedCenter R L).map (MulAut.conj (y : G)).toMonoidHom := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.toMul, hw, rfl⟩
  · rintro ⟨w, hw, he⟩
    refine ⟨Additive.ofMul ⟨w, hw.1⟩, hw, ?_⟩
    exact Additive.toMul.injective (Subtype.ext he)

theorem fixedSubspace_ti {R L : Subgroup G} {Δ : Set ℕ}
    (hθ : theta Δ (normalizer (L : Set G)) = L)
    (hcontrol : ∀ U : Subgroup G, U ≤ radicalFixedCenter R L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G)) (a : Actor R) :
    Disjoint (fixedSubspace R L) ((fixedSubspace R L).map (representation R a)) ∨
      (fixedSubspace R L).map (representation R a) = fixedSubspace R L := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (kernel R) a
  rcases fixedCenter_ti_of_control hθ hcontrol (y : G) y.property with hd | he
  · left
    apply Submodule.disjoint_def.mpr
    intro z hz hw
    have hmem : (z.toMul : G) ∈ radicalFixedCenter R L ⊓
        (radicalFixedCenter R L).map (MulAut.conj (y : G)).toMonoidHom :=
      ⟨hz, (mem_map_fixedSubspace R L y z).mp hw⟩
    exact Additive.toMul.injective (Subtype.ext (mem_bot.mp (hd ▸ hmem)))
  · right
    ext z
    change z ∈ (fixedSubspace R L).map (representation R (projection R y)) ↔ _
    rw [mem_map_fixedSubspace R L y z, he]
    rfl

variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- A one-basepoint TI criterion implies disjointness for the whole orbit. -/
theorem orbit_ti_of_base (ρ : Representation (ZMod 2) A E) (W : Submodule (ZMod 2) E)
    (h : ∀ a : A, Disjoint W (W.map (ρ a)) ∨ W.map (ρ a) = W)
    (a b : A) (hne : W.map (ρ a) ≠ W.map (ρ b)) :
    Disjoint (W.map (ρ a)) (W.map (ρ b)) := by
  have hneq : W.map (ρ (a⁻¹ * b)) ≠ W := by
    intro he
    apply hne
    have hh := congrArg (fun U : Submodule (ZMod 2) E => U.map (ρ a)) he
    simpa only [← orbit_map_mul, mul_inv_cancel_left] using hh.symm
  have hd := (h (a⁻¹ * b)).resolve_right hneq
  apply Submodule.disjoint_def.mpr
  rintro v ⟨u, hu, rfl⟩ ⟨w, hw, he⟩
  have hwu : ρ (a⁻¹ * b) w = u := by
    have hh := congrArg (ρ a⁻¹) he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  have hu0 := Submodule.disjoint_def.mp hd u hu ⟨w, hw, hwu⟩
  rw [hu0, map_zero]

theorem fixedOrbit_ti {R L X : Subgroup G} {Δ : Set ℕ}
    (hθ : theta Δ (normalizer (L : Set G)) = L)
    (hcontrol : ∀ U : Subgroup G, U ≤ radicalFixedCenter R L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hfixed : fixedSpace (representation R) (cartanImage R X) = fixedSubspace R L) :
    ∀ U ∈ fixedOrbit (representation R) (cartanImage R X),
      ∀ W ∈ fixedOrbit (representation R) (cartanImage R X), U ≠ W → Disjoint U W := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hne
  rw [hfixed] at hne ⊢
  exact orbit_ti_of_base (representation R) (fixedSubspace R L)
    (fixedSubspace_ti hθ hcontrol) a b hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
