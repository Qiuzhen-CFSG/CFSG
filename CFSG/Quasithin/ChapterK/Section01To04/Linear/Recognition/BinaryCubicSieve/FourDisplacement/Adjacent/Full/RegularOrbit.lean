module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.RootNorm
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.Representation.PGroupRegularOrbit

/-!
# A regular orbit from the full-support SL₄ root norm

The ordered six root factors parametrize the actual upper unitriangular
subgroup. Their product coordinates and their polynomial inverse identify
its 64 elements without enumerating SL₄(2). Summing their translates turns
the six-root difference in `RootNorm` into the subgroup norm. The regular
orbit lemma for two-groups therefore embeds a 64-dimensional submodule.

This supplies the lower bound used in the full-support case of
Aschbacher–Smith K.3.2, printed pp.454–455, and Guralnick–Malle,
Classification of 2F-modules, II, author manuscript Proposition4.8(3B).
It does not identify the module as Steinberg or assume absolute irreducibility.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open Theory.SpecificGroups.LinearSylowNormalizers
open scoped BigOperators
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
private abbrev Coordinates := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private abbrev U := unipotent 4 (ZMod 2)

private def root (k : Fin 6) (c : ZMod 2) : Group := ![
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) c,
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 2) (by decide) c,
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 3) (by decide) c,
  Matrix.SpecialLinearGroup.transvection (i := 1) (j := 2) (by decide) c,
  Matrix.SpecialLinearGroup.transvection (i := 1) (j := 3) (by decide) c,
  Matrix.SpecialLinearGroup.transvection (i := 2) (j := 3) (by decide) c] k

private lemma root_zero (k : Fin 6) : root k 0 = 1 := by
  fin_cases k <;> apply Subtype.ext <;> ext i j <;> simp [root]
private lemma root_one (k : Fin 6) : root k 1 = fullSupportPositiveRoot k := by
  revert k
  decide
private lemma transvection_mem (i j : Fin 4) (hij : i < j) (c : ZMod 2) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ U := by
  rw [mem_unipotent, mem_borel]
  refine ⟨Matrix.blockTriangular_transvection hij.le c, ?_⟩
  intro k
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  simp [Matrix.single_apply]
  aesop

private lemma root_mem (k : Fin 6) (c : ZMod 2) : root k c ∈ U := by
  fin_cases k <;> exact transvection_mem _ _ (by decide) c

private def rootProduct (x : Coordinates) : Group :=
  root 0 x.1 * root 1 x.2.1 * root 2 x.2.2.1 *
    root 3 x.2.2.2.1 * root 4 x.2.2.2.2.1 * root 5 x.2.2.2.2.2

private lemma rootProduct_mem (x : Coordinates) : rootProduct x ∈ U :=
  U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem
    (root_mem _ _) (root_mem _ _)) (root_mem _ _)) (root_mem _ _))
      (root_mem _ _)) (root_mem _ _)

private def parameterization (x : Coordinates) : U := ⟨rootProduct x, rootProduct_mem x⟩
private def entries (g : U) : Coordinates :=
  (g.val.val 0 1, g.val.val 0 2, g.val.val 0 3,
    g.val.val 1 2, g.val.val 1 3, g.val.val 2 3)

private lemma entries_injective : Function.Injective entries := by
  intro g h he
  obtain ⟨hg, dg⟩ := (mem_unipotent 4 (ZMod 2) g.val).mp g.property
  obtain ⟨hh, dh⟩ := (mem_unipotent 4 (ZMod 2) h.val).mp h.property
  rw [mem_borel] at hg hh
  have h01 := congrArg (fun x : Coordinates => x.1) he
  have h02 := congrArg (fun x : Coordinates => x.2.1) he
  have h03 := congrArg (fun x : Coordinates => x.2.2.1) he
  have h12 := congrArg (fun x : Coordinates => x.2.2.2.1) he
  have h13 := congrArg (fun x : Coordinates => x.2.2.2.2.1) he
  have h23 := congrArg (fun x : Coordinates => x.2.2.2.2.2) he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact h01
    | exact h02
    | exact h03
    | exact h12
    | exact h13
    | exact h23
    | exact (dg _).trans (dh _).symm
    | exact (hg (by decide)).trans (hh (by decide)).symm

private lemma entries_parameterization (a b c d e f : ZMod 2) :
    entries (parameterization (a,b,c,d,e,f)) =
      (a, b+a*d, c+a*e+(b+a*d)*f, d, e+d*f, f) := by
  dsimp [entries, parameterization, rootProduct, root]
  simp [Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply]
  ring_nf
  simp

private def inverseParameters (x : Coordinates) : Coordinates :=
  (x.1, x.2.1 + x.1*x.2.2.2.1,
    x.2.2.1 + x.1*(x.2.2.2.2.1 + x.2.2.2.1*x.2.2.2.2.2) + x.2.1*x.2.2.2.2.2,
    x.2.2.2.1, x.2.2.2.2.1 + x.2.2.2.1*x.2.2.2.2.2, x.2.2.2.2.2)

private lemma left_inverse (x : Coordinates) : inverseParameters (entries (parameterization x)) = x := by
  rcases x with ⟨a,b,c,d,e,f⟩
  rw [entries_parameterization]
  dsimp [inverseParameters]
  ext <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 from by decide, show (4 : ZMod 2) = 0 from by decide]

private lemma right_inverse (g : U) : parameterization (inverseParameters (entries g)) = g := by
  apply entries_injective
  generalize entries g = x
  rcases x with ⟨a,b,c,d,e,f⟩
  dsimp [inverseParameters]
  rw [entries_parameterization]
  ext <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 from by decide, show (4 : ZMod 2) = 0 from by decide]

private def coordinateEquiv : Coordinates ≃ U where
  toFun := parameterization
  invFun := inverseParameters ∘ entries
  left_inv := left_inverse
  right_inv := right_inverse

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma vector_neg (x : V) : -x = x := by
  calc
    -x = (-1 : ZMod 2) • x := (neg_one_smul (ZMod 2) x).symm
    _ = x := by rw [show (-1 : ZMod 2) = 1 from by decide, one_smul]

private lemma sum_root (σ : Representation (ZMod 2) Group V) (k : Fin 6) (w : V) :
    (∑ c : ZMod 2, σ (root k c) w) = displacement σ (fullSupportPositiveRoot k) w := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), root_zero, root_one, map_one]
  change w + σ (fullSupportPositiveRoot k) w = σ (fullSupportPositiveRoot k) w - w
  rw [sub_eq_add_neg, vector_neg, add_comm]

private lemma sum_parameterization (σ : Representation (ZMod 2) Group V) (w : V) :
    (∑ x : Coordinates, σ (rootProduct x) w) =
    displacement σ (fullSupportPositiveRoot 0)
      (displacement σ (fullSupportPositiveRoot 1)
        (displacement σ (fullSupportPositiveRoot 2)
          (displacement σ (fullSupportPositiveRoot 3)
            (displacement σ (fullSupportPositiveRoot 4)
              (displacement σ (fullSupportPositiveRoot 5) w))))) := by
  simp only [Fintype.sum_prod_type, rootProduct, map_mul, Module.End.mul_apply]
  simp_rw [← map_sum]
  simp_rw [sum_root]

private noncomputable instance : Fintype U := Fintype.ofFinite U

private lemma card_U : Fintype.card U = 64 := by
  rw [← Fintype.card_congr coordinateEquiv]
  norm_num [Coordinates, Fintype.card_prod, ZMod.card]

private lemma sum_unipotent (σ : Representation (ZMod 2) Group V) {v : V}
    (h : LocalHighestVector σ Finset.univ v) :
    (∑ g : U, σ g.val (σ longestExchange v)) = v := by
  have he := Fintype.sum_equiv coordinateEquiv
    (fun x => σ (rootProduct x) (σ longestExchange v))
    (fun g : U => σ g.val (σ longestExchange v)) (fun _ => rfl)
  rw [← he, sum_parameterization]
  exact full_support_six_root_norm h

/-- The six-root norm embeds a regular upper-unitriangular module. Thus every
nonzero full-support local highest vector forces at least 64 dimensions,
without an irreducibility or module-identification assumption. -/
theorem sixty_four_le_finrank_of_full_support [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) Group V} {v : V}
    (h : LocalHighestVector σ Finset.univ v) (hv : v ≠ 0) :
    64 ≤ Module.finrank (ZMod 2) V := by
  let τ := σ.comp U.subtype
  have hn : (∑ g : U, τ g (σ longestExchange v)) ≠ 0 := by
    change (∑ g : U, σ g.val (σ longestExchange v)) ≠ 0
    rwa [sum_unipotent σ h]
  have hp : IsPGroup (ringChar (ZMod 2)) U := by
    simpa only [ZMod.ringChar_zmod_n] using unipotent_isPGroup 4 (ZMod 2) (by decide)
  have hi := PGroupRegularOrbit.orbitMap_injective (by simp only [ZMod.ringChar_zmod_n]; decide) hp τ
    (σ longestExchange v) hn
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_fintype_fun_eq_card, card_U] using hd

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
