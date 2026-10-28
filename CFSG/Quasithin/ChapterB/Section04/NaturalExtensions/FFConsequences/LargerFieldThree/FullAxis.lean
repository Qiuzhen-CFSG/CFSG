module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.FieldBounds

/-!
# Recognition of the full axis actor in B.4.9(2)

A pointwise hyperplane stabilizer in SL₃ embeds into the hyperplane by
its displacement on one complementary vector. The determinant-one equation
puts that displacement in the hyperplane. Its order is therefore at most
2^(2f). An elementary actor of that order and fixed codimension f is the
entire pointwise stabilizer, with the original matrix marking preserved.

The parent module applies this equality case to the actual Thompson
replacement in a DoubleNatural extension. Source: Aschbacher–Smith,
combined manuscript of 1 March 2004, B.4.9(2), printed p.94.
-/

public section
open Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree
variable (F : BinaryField)

private theorem axisCentralizer_card_le
    (C : Submodule F.Carrier (Fin 3 → F.Carrier))
    (hC : Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ C) = 1) :
    Nat.card (subspaceKernel (linearNatural F 3) (C.restrictScalars (ZMod 2)) ⊤) ≤
      2 ^ (2 * F.degree) := by
  classical
  let σ := specialLinearNatural (k := F.Carrier) 3
  let Q := subspaceKernel (linearNatural F 3) (C.restrictScalars (ZMod 2)) ⊤
  let e : ((Fin 3 → F.Carrier) ⧸ C) ≃ₗ[F.Carrier] F.Carrier :=
    LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_self] using hC)
  let f := e.toLinearMap.comp C.mkQ
  have hf : Function.Surjective f := e.surjective.comp C.mkQ_surjective
  have hfker (v : Fin 3 → F.Carrier) : f v = 0 ↔ v ∈ C := by
    change e (C.mkQ v) = 0 ↔ v ∈ C
    rw [map_eq_zero_iff e e.injective]
    exact Submodule.Quotient.mk_eq_zero C
  obtain ⟨v₀, hv₀⟩ := hf 1
  let w (g : Q) : Fin 3 → F.Carrier := σ g.val v₀ - v₀
  have hact (g : Q) (v : Fin 3 → F.Carrier) : σ g.val v = v + f v • w g := by
    have hz : v - f v • v₀ ∈ C := (hfker _).mp (by
      rw [map_sub, map_smul, hv₀, smul_eq_mul, mul_one, sub_self])
    have hh := g.property.2 _ hz
    change σ g.val (v - f v • v₀) = v - f v • v₀ at hh
    rw [map_sub, map_smul] at hh
    dsimp only [w]
    rw [smul_sub]
    linear_combination hh
  let u : Fin 3 → F.Carrier := fun i => f (Pi.single i 1)
  have hfu (v : Fin 3 → F.Carrier) : u ⬝ᵥ v = f v := by
    have hs (i : Fin 3) : f (Pi.single i (v i)) = v i * u i := by
      rw [show Pi.single i (v i) = v i • Pi.single i (1 : F.Carrier) by
        rw [← Pi.single_smul]; simp only [smul_eq_mul, mul_one]]
      exact f.map_smul (v i) (Pi.single i 1)
    calc
      u ⬝ᵥ v = ∑ i, f (Pi.single i (v i)) := by
        simp only [dotProduct, hs]
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      _ = f (∑ i, Pi.single i (v i)) := (map_sum f _ _).symm
      _ = f v := by rw [Finset.univ_sum_single]
  have hw (g : Q) : w g ∈ C := by
    have hmat : g.val.val = 1 + vecMulVec (w g) u := by
      apply Matrix.mulVec_injective
      funext v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, hfu,
        op_smul_eq_smul]
      exact hact g v
    have hd := g.val.property
    rw [hmat, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow] at hd
    change 1 + u ⬝ᵥ w g = 1 at hd
    rw [hfu] at hd
    exact (hfker _).mp (add_left_cancel (hd.trans (add_zero 1).symm))
  let D (g : Q) : C := ⟨w g, hw g⟩
  have hinj : Function.Injective D := by
    intro a b he
    have hwab : w a = w b := congrArg Subtype.val he
    apply Subtype.ext
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    rw [hact, hact, hwab]
  have hdim : Module.finrank F.Carrier C = 2 := by
    have hd := C.finrank_quotient_add_finrank
    rw [hC, Module.finrank_pi, Fintype.card_fin] at hd
    omega
  have hc := Nat.card_le_card_of_injective D hinj
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier) (V := C), F.card_eq,
    hdim, ← pow_mul, mul_comm F.degree 2] at hc
  exact hc

theorem full_axis_of_rank_cost
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)}
    (hA : IsElementaryTwo A) (hr : rank A = 2 * F.degree)
    (hc : fixedCodim (linearNatural F 3) A = F.degree) : IsFullAxisGroup F 3 A := by
  let C := fieldFixedSpace F 3 A
  have hC : Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ C) = 1 := by
    rw [fixedCodim_eq_field_codim] at hc
    have hp := F.degree_pos
    change F.degree * Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸ C) = F.degree at hc
    exact Nat.eq_of_mul_eq_mul_left hp (hc.trans (mul_one F.degree).symm)
  let Q := subspaceKernel (linearNatural F 3) (C.restrictScalars (ZMod 2)) ⊤
  have hle : A ≤ Q := by
    intro g hg
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨g, hg⟩⟩
  have hcard := axisCentralizer_card_le F C hC
  have heq : A = Q := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hA.card_eq_two_pow_rank, hr]
    exact hcard)
  refine ⟨C, hC, ?_⟩
  intro g
  rw [heq]
  exact ⟨fun hg => hg.2, fun hg => ⟨Subgroup.mem_top _, hg⟩⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree
