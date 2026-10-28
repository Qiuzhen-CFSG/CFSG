module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetModule
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.GeneratorColumns
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.MarkedNorm

/-!
# Finite norm quotients mapping onto the universal HS module

For a finite table with two transition maps, form the binary coordinate space
and factor out all word translates of its five-term B-norm columns. If its
coordinate vectors in the literal universal module contain the fixed seed and
intertwine both generators, their linear lift is surjective and kills all these
relations. Consequently the universal module has dimension no larger than this
finite norm quotient. The table need not first be certified as a group action.

This separates a finite binary calculation from the actual-carrier comparison.
Neither the comparison nor a numerical dimension bound is assumed to exist.
`of_quotient_bound` applies the result to the literal `of_cosetNorm_action`
consumer, with the independent kernel-nilpotence premise retained explicitly.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS case; Aschbacher--Smith K.4, printed p.457.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
noncomputable section

abbrev Coordinates (n : ℕ) := Fin n → ZMod 2

def columnAction {n : ℕ} (t : Fin 2 → Fin n → Fin n) (s : Fin 2) :
    Module.End (ZMod 2) (Coordinates n) :=
  ∑ j, (LinearMap.proj j).smulRight (Pi.single (t s j) 1)

theorem columnAction_single {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (s : Fin 2) (i : Fin n) :
    columnAction t s (Pi.single i 1) = Pi.single (t s i) 1 := by
  classical
  simp [columnAction, LinearMap.sum_apply, Pi.single_apply]

def wordAction {n : ℕ} (t : Fin 2 → Fin n → Fin n) (w : List (Fin 2)) :
    Module.End (ZMod 2) (Coordinates n) := (w.map (columnAction t)).prod

def normAction {n : ℕ} (t : Fin 2 → Fin n → Fin n) :
    Module.End (ZMod 2) (Coordinates n) := ∑ k : Fin 5, columnAction t 1 ^ k.val

/-- The span of all translates of the five-term norm columns. -/
def relations {n : ℕ} (t : Fin 2 → Fin n → Fin n) :
    Submodule (ZMod 2) (Coordinates n) :=
  Submodule.span (ZMod 2) (Set.range fun wi : List (Fin 2) × Fin n =>
    wordAction t wi.1 (normAction t (Pi.single wi.2 1)))

abbrev NormQuotient {n : ℕ} (t : Fin 2 → Fin n → Fin n) :=
  Coordinates n ⧸ relations t

def vectorMap : BinaryAlgebra →ₗ[ZMod 2] CosetNormModule :=
  (LinearMap.applyₗ (cosetNormVector 1)).comp
    cosetNormRepresentation.asAlgebraHom.toLinearMap

theorem vectorMap_apply (x : BinaryAlgebra) : vectorMap x = cosetNormVector x := by
  exact (cosetNorm_action_vector x 1).trans (congrArg cosetNormVector (mul_one x))

def coordinateLift {n : ℕ} (v : Fin n → CosetNormModule) :
    Coordinates n →ₗ[ZMod 2] CosetNormModule :=
  ∑ j, (LinearMap.proj j).smulRight (v j)

theorem coordinateLift_single {n : ℕ} (v : Fin n → CosetNormModule) (j : Fin n) :
    coordinateLift v (Pi.single j 1) = v j := by
  classical
  simp [coordinateLift, LinearMap.sum_apply, Pi.single_apply]

private theorem generator_closure : Submonoid.closure (Set.range generator) = ⊤ := by
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  have h : Subgroup.closure (Set.range generator) = ⊤ := by
    apply _root_.Sporadic.LeechRelated.HS.eq_top_of_generators_mem
    · exact Subgroup.subset_closure ⟨0, by simp [generator]; rfl⟩
    · exact Subgroup.subset_closure ⟨1, by simp [generator]; rfl⟩
  rw [← Subgroup.closure_toSubmonoid_of_finite, h]
  rfl

theorem coordinateLift_intertwines {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (v : Fin n → CosetNormModule)
    (h : ∀ s i, cosetNormRepresentation (generator s) (v i) = v (t s i))
    (s : Fin 2) (x : Coordinates n) :
    coordinateLift v (columnAction t s x) =
      cosetNormRepresentation (generator s) (coordinateLift v x) := by
  classical
  have he : (coordinateLift v).comp (columnAction t s) =
      (cosetNormRepresentation (generator s)).comp (coordinateLift v) := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      simp [← Pi.single_smul]
    rw [hs]
    simp only [map_smul, LinearMap.comp_apply, columnAction_single, coordinateLift_single, h]
  exact LinearMap.congr_fun he x

theorem coordinateLift_surjective {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (v : Fin n → CosetNormModule) (e : Fin n) (he : v e = cosetNormVector 1)
    (h : ∀ s i, cosetNormRepresentation (generator s) (v i) = v (t s i)) :
    Function.Surjective (coordinateLift v) := by
  have hc (g : KnownSimple.SporadicName.hs.Carrier) :
      cosetNormRepresentation g (cosetNormVector 1) ∈ (coordinateLift v).range := by
    apply Submonoid.induction_of_closure_eq_top_left
      (motive := fun g => cosetNormRepresentation g (cosetNormVector 1) ∈
        (coordinateLift v).range) generator_closure g
    · refine ⟨Pi.single e 1, ?_⟩
      simpa using (coordinateLift_single v e).trans he
    · rintro _ ⟨s, rfl⟩ y ⟨x, hx⟩
      refine ⟨columnAction t s x, ?_⟩
      rw [coordinateLift_intertwines t v h, hx, map_mul]
      rfl
  have hm (x : BinaryAlgebra) : vectorMap x ∈ (coordinateLift v).range := by
    induction x using MonoidAlgebra.induction_on with
    | of g => simpa [vectorMap, Representation.asAlgebraHom_single] using hc g
    | add x y hx hy => simpa only [map_add] using (coordinateLift v).range.add_mem hx hy
    | smul c x hx => simpa only [map_smul] using (coordinateLift v).range.smul_mem c hx
  intro u
  obtain ⟨x, rfl⟩ := cosetNormVector_surjective u
  exact (LinearMap.mem_range.mp (by simpa only [vectorMap_apply] using hm x))

set_option backward.isDefEq.respectTransparency false in
private theorem norm_annihilates (u : CosetNormModule) :
    (∑ k : Fin 5, cosetNormRepresentation (generator 1) ^ k.val) u = 0 := by
  have hn := (TwoSidedIdeal.mem_ker _).mp
    (normIdeal_le_cosetKernel generatorNorm_mem_fiveNormIdeal)
  have he : cosetNormRepresentation.asAlgebraHom generatorNorm =
      ∑ k : Fin 5, cosetNormRepresentation (generator 1) ^ k.val := by
    simp [generatorNorm, generator, Representation.asAlgebraHom_single, map_pow]
  rw [← he, hn]
  rfl

theorem relations_le_ker {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (v : Fin n → CosetNormModule)
    (h : ∀ s i, cosetNormRepresentation (generator s) (v i) = v (t s i)) :
    relations t ≤ (coordinateLift v).ker := by
  have hp (k : ℕ) (x : Coordinates n) :
      coordinateLift v ((columnAction t 1 ^ k) x) =
        (cosetNormRepresentation (generator 1) ^ k) (coordinateLift v x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [pow_succ', Module.End.mul_apply, coordinateLift_intertwines t v h, ih]
  have hn (x : Coordinates n) : coordinateLift v (normAction t x) = 0 := by
    simp only [normAction, LinearMap.sum_apply, map_sum, hp]
    simpa only [LinearMap.sum_apply] using norm_annihilates (coordinateLift v x)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨w, i⟩, rfl⟩
  change coordinateLift v (wordAction t w (normAction t (Pi.single i 1))) = 0
  induction w with
  | nil => exact hn _
  | cons s w ih =>
    change coordinateLift v (columnAction t s
      (wordAction t w (normAction t (Pi.single i 1)))) = 0
    rw [coordinateLift_intertwines t v h, ih, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem finrank_le_quotient {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (v : Fin n → CosetNormModule) (e : Fin n) (he : v e = cosetNormVector 1)
    (h : ∀ s i, cosetNormRepresentation (generator s) (v i) = v (t s i)) :
    Module.finrank (ZMod 2) CosetNormModule ≤ Module.finrank (ZMod 2) (NormQuotient t) := by
  let := RestrictScalars.module (ZMod 2) BinaryAlgebra
    (BinaryAlgebra ⧸ cosetNormRelations)
  let f := (relations t).liftQ (coordinateLift v) (relations_le_ker t v h)
  apply LinearMap.finrank_le_finrank_of_surjective (f := f)
  intro u
  obtain ⟨x, hx⟩ := coordinateLift_surjective t v e he h u
  exact ⟨Submodule.Quotient.mk x, hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- An application to the original norm certificate. The two finite-table
premises and the independently owned kernel-nilpotence premise remain explicit. -/
def of_quotient_bound {n : ℕ} (t : Fin 2 → Fin n → Fin n)
    (v : Fin n → CosetNormModule) (e : Fin n) (he : v e = cosetNormVector 1)
    (h : ∀ s i, cosetNormRepresentation (generator s) (v i) = v (t s i))
    (hd : Module.finrank (ZMod 2) (NormQuotient t) < 40)
    (r : ℕ)
    (hr : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, cosetNormRepresentation.asAlgebraHom x = 0) →
        xs.prod ∈ fiveNormIdeal) : NormCertificate := by
  letI := RestrictScalars.module (ZMod 2) BinaryAlgebra
    (BinaryAlgebra ⧸ cosetNormRelations)
  have hdim : Module.finrank (ZMod 2) CosetNormModule < 40 :=
    lt_of_le_of_lt (finrank_le_quotient t v e he h) hd
  apply of_cosetNorm_action cosetNormRepresentation (by nlinarith) r 1 hr
  intro xs hlen hx
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
  simpa using hx x (by simp)

end
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetFiniteAction
