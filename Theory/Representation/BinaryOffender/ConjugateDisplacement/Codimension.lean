module
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
/-!
# Fixed codimension from conjugate generators

The fixed space of an actor containing L lies inside C_V(L). Intersecting
fixed spaces of conjugate cyclic generators bounds its codimension by the
sum of their equal codimensions. No zero-fixed-space hypothesis is needed.
This is the central-quotient form of the displacement estimate used in
Aschbacher--Smith, Chapter K, and in the full-orbit argument of 3.2.5.
-/
public section
namespace Representation.BinaryOffender
open Subgroup
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
theorem fixedCodim_le_mul_of_conjugate_generation (L : Subgroup G)
    (t : G) {n : ℕ} (g : Fin n → G)
    (hgen : L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹)) :
    fixedCodim ρ L ≤ n * fixedCodim ρ (zpowers t) := by
  let X (i : Fin n) := (zpowers t).map (MulAut.conj (g i)).toMonoidHom
  have hL : L ≤ ⨆ i, X i := hgen.trans <| (closure_le _).mpr <| by
    rintro _ ⟨i, rfl⟩
    exact (le_iSup X i) (mem_map_of_mem _ (mem_zpowers t))
  have hle := ρ.invariants_comp_subtype_antitone hL
  have hdim : Module.finrank (ZMod 2) (fixedSpace ρ (⨆ i, X i)) ≤
      Module.finrank (ZMod 2) (fixedSpace ρ L) := Submodule.finrank_mono hle
  have hdL := fixedCodim_add_finrank ρ L
  have hdX := fixedCodim_add_finrank ρ (⨆ i, X i)
  have hcod : fixedCodim ρ L ≤ fixedCodim ρ (⨆ i, X i) := by omega
  have hi := Submodule.finrank_quotient_iInf_le_sum (fun i => fixedSpace ρ (X i))
  have he : fixedSpace ρ (⨆ i, X i) = ⨅ i, fixedSpace ρ (X i) :=
    ρ.invariants_comp_iSup X
  rw [← he] at hi
  change fixedCodim ρ (⨆ i, X i) ≤ ∑ i, fixedCodim ρ (X i) at hi
  apply hcod.trans
  simpa only [X, fixedCodim_map_conj, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using hi

end Representation.BinaryOffender
