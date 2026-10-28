module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Duality
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.NaturalDual

/-!
# The conditional dimension restriction for the literal tilded action

Restricting the invariant commutator form to Ṽ gives a nonzero map to its
dual: if the map vanished, the form's radical would put V inside Z(U), and
the H-conjugate-span definition would make U abelian. Homogeneous natural
coordinates then contradict the natural-to-dual obstruction when n>3.
Every action and inclusion uses the actual images in G₁/V₁.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 12.8.8(5), printed p.852 (PDF p.869). The source form with its radical
is an earlier 12.8.8(2) input. The equivalence eU is the still-required
12.8.5(1) output, not a proved homogeneity assertion. In this large-dimensional
branch GL_(n-1)(2) equals its derived group; no such equality is used at n=3.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

theorem tilde_seed_le (F : InvariantFlag T V n) : F.tilde V ≤ F.tilde F.U :=
  map_mono (fun _ hx => le_conjugateSpanBy V F.H hx)

variable (F : InvariantFlag T V n)
variable [IsElementaryAbelian 2 (F.tilde V)] [IsElementaryAbelian 2 (F.tilde F.U)]

/-- Inclusion of the actual image of V into the actual image of U in G₁/V₁. -/
def seedTildeLinearInclusion : Additive (F.tilde V) →ₗ[ZMod 2] Additive (F.tilde F.U) :=
  (inclusion F.tilde_seed_le).toAdditive.toZModLinearMap 2

theorem seedTildeLinearInclusion_equivariant (L : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (j : F.Li L 1) (v : Additive (F.tilde V)) :
    F.seedTildeLinearInclusion (Additive.ofMul
      (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
        ((F.Li_le L 1).trans (inf_le_left.trans hLV)) j v.toMul)) =
    Additive.ofMul (F.localTildeAction F.H le_rfl
      ⟨j, (F.Li_le L 1 j.property).2⟩ (F.seedTildeLinearInclusion v).toMul) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

variable [IsElementaryAbelian 2 V]

/-- The radical clause of 12.8.8(2) makes restriction to the seed nonzero in
its nonabelian branch. This uses the actual image of Z(U), not Z(U)=V₁. -/
theorem seed_pairing_ne_zero (hn : 1 ≤ n)
    (B : LinearMap.BilinForm (ZMod 2) (Additive (F.tilde F.U)))
    (hrad : ∀ v : Additive (F.tilde F.U),
      (∀ u, B u v = 0) ↔ (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU)
    (hnonab : ¬ IsMulCommutative F.U) :
    B.compl₂ F.seedTildeLinearInclusion ≠ 0 := by
  intro hzero
  have hVZ : V ≤ F.ZU := by
    intro v hv
    have hvH : v ∈ F.H := F.U_le_H (le_conjugateSpanBy V F.H hv)
    let qv : F.tilde V := F.tildeMap V
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) ⟨v, hv⟩
    have hr : ((F.seedTildeLinearInclusion (Additive.ofMul qv)).toMul : F.G₁tilde) ∈
        F.tilde F.ZU := by
      apply (hrad _).mp
      intro u
      exact congrArg (fun f : Additive (F.tilde F.U) →ₗ[ZMod 2]
        Additive (F.tilde V) →ₗ[ZMod 2] ZMod 2 => f u (Additive.ofMul qv)) hzero
    exact (F.mem_tilde_iff_of_point_le F.ZU (F.point_le_ZU hn) ⟨v, hvH⟩).mp hr
  apply hnonab
  apply le_centralizer_iff_isMulCommutative.mp
  exact (conjugateSpanBy_le hVZ F.H_normalizes_ZU).trans (centerIn_le_centralizer F.U)

/-- The large-dimensional case of 12.8.8(5), conditional on the homogeneous
natural coordinates to be supplied by 12.8.5(1). All action equations refer to
the literal quotient actions. For n>3 the derived group L_(n-1)(2)' is GL_(n-1)(2).
The conclusion is obtained from the commutator form's map to the dual. -/
theorem nonabelian_homogeneous_natural_exclusion (L : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (hn : 3 < n) (r : ℕ)
    (α : F.Li L 1 →* ((Fin (n - 1) → ZMod 2) ≃ₗ[ZMod 2] (Fin (n - 1) → ZMod 2)))
    (hα : Function.Surjective α)
    (eV : Additive (F.tilde V) ≃ₗ[ZMod 2] (Fin (n - 1) → ZMod 2))
    (eU : Additive (F.tilde F.U) ≃ₗ[ZMod 2] (Fin r → Fin (n - 1) → ZMod 2))
    (heV : ∀ j v, eV (Additive.ofMul
      (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
        ((F.Li_le L 1).trans (inf_le_left.trans hLV)) j v.toMul)) = α j (eV v))
    (heU : ∀ (j : F.Li L 1) u i, eU (Additive.ofMul (F.localTildeAction F.H le_rfl
      ⟨j, (F.Li_le L 1 j.property).2⟩ u.toMul)) i = α j (eU u i))
    (B : LinearMap.BilinForm (ZMod 2) (Additive (F.tilde F.U)))
    (hB : ∀ (j : F.Li L 1) u v,
      B (Additive.ofMul (F.localTildeAction F.H le_rfl
        ⟨j, (F.Li_le L 1 j.property).2⟩ u.toMul))
        (Additive.ofMul (F.localTildeAction F.H le_rfl
          ⟨j, (F.Li_le L 1 j.property).2⟩ v.toMul)) = B u v)
    (hrad : ∀ v : Additive (F.tilde F.U),
      (∀ u, B u v = 0) ↔ (v.toMul : F.G₁tilde) ∈ F.tilde F.ZU)
    (hnonab : ¬ IsMulCommutative F.U) : False := by
  let f := B.compl₂ (F.seedTildeLinearInclusion.comp eV.symm.toLinearMap)
  have hf : f ≠ 0 := by
    intro hz
    apply F.seed_pairing_ne_zero (by omega) B hrad hnonab
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f : Additive (F.tilde F.U) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin (n - 1) → ZMod 2) => f u (eV v)) hz
    simpa [f] using h
  have hz : f.comp eU.symm.toLinearMap = 0 := by
    apply NormalL1.natural_power_to_dual_eq_zero (by omega)
    intro g u v
    obtain ⟨j, rfl⟩ := hα g
    have hu : eU.symm (fun i => α j (u i)) = Additive.ofMul
        (F.localTildeAction F.H le_rfl
          ⟨j, (F.Li_le L 1 j.property).2⟩ (eU.symm u).toMul) := by
      apply eU.injective
      exact (eU.apply_symm_apply _).trans (funext fun i =>
        (congrArg (fun w => α j (w i)) (eU.apply_symm_apply u)).symm.trans
          (heU j (eU.symm u) i).symm)
    have hv : eV.symm (α j v) = Additive.ofMul
        (F.tildeAction (F.Li L 1) V ((F.Li_le L 1).trans inf_le_right)
          ((F.Li_le L 1).trans (inf_le_left.trans hLV)) j (eV.symm v).toMul) := by
      apply eV.injective
      exact (eV.apply_symm_apply _).trans
        ((congrArg (α j) (eV.apply_symm_apply v)).symm.trans (heV j (eV.symm v)).symm)
    change B (eU.symm (fun i => α j (u i)))
      (F.seedTildeLinearInclusion (eV.symm (α j v))) =
        B (eU.symm u) (F.seedTildeLinearInclusion (eV.symm v))
    rw [hu, hv, F.seedTildeLinearInclusion_equivariant L hLV]
    exact hB j _ _
  apply hf
  apply LinearMap.ext
  intro u
  have h := LinearMap.congr_fun hz (eU u)
  simpa using h

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
