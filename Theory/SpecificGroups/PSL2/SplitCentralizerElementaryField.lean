module

public import Theory.SpecificGroups.PSL2.SplitTorusSemilinearSquares
public import Theory.GroupTheory.ElementaryCoreNormalAbelianSquares
/-!
# Elementary two-core actors in the actual semilinear centralizer

The full split torus is a normal abelian subgroup of the actual
canonical involution centralizer. Original Sylow normalization and
two-core containment force elementary actors to fix its squares,
so the proved coefficient obstruction kills their field coordinate.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
/-- In the full canonical quadratic semilinear involution centralizer, the
original elementary two-core actor normalized by a Sylow has no field part. -/
theorem split_centralizer_elementary_commute_squares
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (_hp : 3 < p) :
    let C := centralizer ({(SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F)} : Set (PGammaL2 F))
    ∀ T : Sylow 2 C, ∀ V : Subgroup C, V ≤ pCore 2 C →
      (T : Subgroup C) ≤ normalizer (V : Set C) → (∀ v ∈ V, v ^ 2 = 1) →
      ∀ v ∈ V, ∀ a : Fˣ, Commute v.val
        ((SemidirectProduct.inl (pGammaL2FullSplitTorus F a) : PGammaL2 F) ^ 2) := by
  intro C T V hV hVN hpow v hv
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let : Finite (PGammaL2 F) := Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right))
    (fun _ _ he => SemidirectProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he))
  let i : Fˣ →* PGammaL2 F := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (pGammaL2FullSplitTorus F)
  have hiC (a : Fˣ) : i a ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    change i a * i (-1) = i (-1) * i a
    rw [← map_mul, ← map_mul, mul_comm]
  let f : Fˣ →* C := i.codRestrict C hiC
  let R := f.range
  let : IsCyclic R := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  let : R.Normal := ⟨by
    intro r hr g
    obtain ⟨a, rfl⟩ := hr
    obtain ha | ha := split_involution_centralizer_torus_action hodd g.val
      (mem_centralizer_singleton_iff.mp g.property)
    · refine ⟨Units.map g.val.right.toRingHom a, ?_⟩
      apply Subtype.ext
      exact (ha a).symm
    · refine ⟨(Units.map g.val.right.toRingHom a)⁻¹, ?_⟩
      apply Subtype.ext
      change i ((Units.map g.val.right.toRingHom a)⁻¹) = g.val * i a * g.val⁻¹
      simpa only [i, MonoidHom.comp_apply, map_inv] using (ha a).symm⟩
  have hc := Theory.GroupTheory.elementary_core_commute_normal_abelian_squares T V R hV hVN hpow
  intro a
  have hh := hc v hv (f a) ⟨a, rfl⟩
  exact congrArg C.subtype hh.eq
/-- The original elementary two-core actor in the full canonical centralizer has no field part. -/
theorem split_centralizer_elementary_field_eq_one
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p) :
    let C := centralizer ({(SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F)} : Set (PGammaL2 F))
    ∀ T : Sylow 2 C, ∀ V : Subgroup C, V ≤ pCore 2 C →
      (T : Subgroup C) ≤ normalizer (V : Set C) → (∀ v ∈ V, v ^ 2 = 1) →
      ∀ v ∈ V, v.val.right = 1 := by
  intro C T V hV hVN hpow v hv
  exact field_eq_one_of_centralizes_split_torus_squares ho hF hp v.val
    (mem_centralizer_singleton_iff.mp v.property)
    (split_centralizer_elementary_commute_squares ho hF hp T V hV hVN hpow v hv)
end Theory.PSL2
