module

public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
public import Theory.SpecificGroups.SL2.DefiningRank

/-!
# Ordinary and local defining-characteristic rank in the octonion G₂ model

The first three positive-root coordinates multiply additively and are
independent. They give ordinary rank at least 3e over a field of order p^e.
The concrete split-quaternion action of SL₂ × SL₂ has diagonal scalar
kernel. Its two upper root groups survive independently and centralize the
scalar of the first factor, giving local rank at least 2e in odd characteristic.
The block SL₂ action is also faithful and proper, with properness witnessed
by a moved octonion basis vector.

These are the rank witnesses used in Aschbacher–Smith A.2.17, printed p.39
of `refs/quasithin.pdf`. They require no simplicity or order formula.
The exact residual centralizer of a fundamental SL₂ is a separate structural
statement. The imported octonion coordinates retain the ATLAS attribution
and license in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2
variable {F : Type*} [Field F]

/-- The first three positive-root coordinates give an additive three-space in G₂. -/
def abelianRootTripleHom : Multiplicative (Fin 3 → F) →* Model F where
  toFun a := unipotentProduct ![a.toAdd 0,a.toAdd 1,a.toAdd 2,0,0,0]
  map_one' := by
    change unipotentProduct ![0,0,0,0,0,0] = 1
    have hz : (![0,0,0,0,0,0] : Fin 6 → F) = 0 := by
      ext i; fin_cases i <;> rfl
    rw [hz, unipotentProduct_zero]
  map_mul' a b := by
    rw [unipotentProduct_mul]
    congr 1
    ext i
    fin_cases i <;> simp [unipotentProductParameters, add_comm]

/-- Uniqueness of the six unipotent coordinates recovers the three parameters. -/
theorem abelianRootTripleHom_injective : Function.Injective (abelianRootTripleHom (F := F)) := by
  intro a b h
  have hh := unipotentProduct_injective h
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · exact congrFun hh 0
  · exact congrFun hh 1
  · exact congrFun hh 2

/-- Three commuting independent root groups give defining-characteristic rank at least 3e. -/
theorem three_mul_fieldExponent_le_primeRank [Finite F]
    {p e : ℕ} [Fact p.Prime] [CharP F p] (hcard : Nat.card F = p^e) :
    3*e ≤ primeRank p (Model F) := by
  have hp : ∀ a : Multiplicative (Fin 3 → F), a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    change p • a.toAdd = 0
    ext i
    simp [nsmul_eq_mul]
  have hc : Nat.card (Multiplicative (Fin 3 → F)) = p^(3*e) := by
    change Nat.card (Fin 3 → F) = _
    rw [Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, Nat.mul_comm e 3]
  exact primeRank_ge_of_elementary_embedding hp hc abelianRootTripleHom abelianRootTripleHom_injective
end Atlas.G2

namespace Atlas.G2
open PairStabilizer Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

/-- The determinant-one block action is faithful in every characteristic. -/
theorem blockSL2_injective : Function.Injective (blockHom (F := F)) := by
  intro a b h
  exact blockToPair_injective (Subtype.ext h)

/-- A highest-root element moves a vector fixed by every block matrix, so the block SL₂ is proper. -/
theorem blockSL2_proper : (blockHom (F := F)).range ≠ ⊤ := by
  intro h
  have hm : rootA (1 : F) ∈ (blockHom (F := F)).range := h ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := hm
  have hfix := block_mem_fixingPair a
  rw [ha] at hfix
  have hc := congrFun hfix.2 1
  norm_num [rootA, rootAEquiv, rootALinear, rootAApply, E, basisVector] at hc
end Atlas.G2

namespace Atlas.G2
open Matrix
open SpecialLinearGroup
open MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
variable {F : Type*} [Field F]
local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

/-- The first SL₂ factor of the concrete split-quaternion central-product action. -/
def orthogonalLeftHom : SpecialLinearGroup (Fin 2) F →* Model F :=
  productHom.comp (MonoidHom.inl _ _)

/-- The diagonal scalar kernel meets the first factor trivially. -/
theorem orthogonalLeftHom_injective : Function.Injective (orthogonalLeftHom (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  exact (kernel_scalar a 1 ha).1.symm

/-- The upper root groups of the two orthogonal SL₂ factors. -/
def orthogonalRootPairHom : Multiplicative F × Multiplicative F →* Model F :=
  productHom.comp ((upperUnipotentHom F).prodMap (upperUnipotentHom F))

/-- The scalar-kernel calculation proves independence of the two root parameters. -/
theorem orthogonalRootPairHom_injective :
    Function.Injective (orthogonalRootPairHom (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hs := kernel_scalar (upperUnipotentHom F a.1) (upperUnipotentHom F a.2) ha
  have ha0 : a.1.toAdd = 0 := by
    simpa [upperUnipotentHom, transvection_coe] using hs.2.1
  have hb0 : a.2.toAdd = 0 := by
    have hh := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 1) hs.1
    simpa [upperUnipotentHom, transvection_coe, ha0] using hh
  exact Prod.ext (Multiplicative.toAdd.injective ha0) (Multiplicative.toAdd.injective hb0)

/-- Both root groups commute with the central scalar of the first SL₂ factor. -/
theorem orthogonalRootPairHom_commute (a : Multiplicative F × Multiplicative F) :
    Commute (orthogonalLeftHom (-1)) (orthogonalRootPairHom a) := by
  change productHom (-1,1) * productHom _ = productHom _ * productHom (-1,1)
  rw [← map_mul, ← map_mul]
  congr 1
  ext <;> simp

/-- The two root groups inside the centralizer of the transported scalar. -/
noncomputable def orthogonalRootPairCentralizerHom {G : Type*} [Group G]
    (f : Model F →* G) :
    Multiplicative F × Multiplicative F →*
      Subgroup.centralizer ({f (orthogonalLeftHom (-1))} : Set G) :=
  (f.comp orthogonalRootPairHom).codRestrict _ fun a => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((orthogonalRootPairHom_commute a).map f).eq.symm

/-- The two orthogonal root groups give rank at least 2e in the scalar centralizer. -/
theorem two_mul_fieldExponent_le_primeRank_centralizer {G : Type*} [Group G] [Finite G]
    [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p^e) (f : Model F →* G) (hf : Function.Injective f) :
    2*e ≤ primeRank p (Subgroup.centralizer ({f (orthogonalLeftHom (-1))} : Set G)) := by
  have hp : ∀ a : Multiplicative F × Multiplicative F, a^p=1 := by
    intro a
    apply Prod.ext <;> apply Multiplicative.toAdd.injective
    · change p • a.1.toAdd = 0
      simp [nsmul_eq_mul]
    · change p • a.2.toAdd = 0
      simp [nsmul_eq_mul]
  have hc : Nat.card (Multiplicative F × Multiplicative F) = p^(2*e) := by
    change Nat.card (F × F) = _
    rw [Nat.card_prod, hcard, ← pow_two, ← pow_mul, Nat.mul_comm e 2]
  apply primeRank_ge_of_elementary_embedding hp hc (orthogonalRootPairCentralizerHom f)
  intro a b h
  exact orthogonalRootPairHom_injective (hf (congrArg Subtype.val h))

/-- In odd characteristic the scalar is a genuine involution, giving a local rank witness. -/
theorem exists_involution_two_mul_fieldExponent_le_primeRank {G : Type*}
    [Group G] [Finite G] [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p^e)
    (f : Model F →* G) (hf : Function.Injective f) :
    ∃ z : G, z ≠ 1 ∧ z^2=1 ∧ 2*e ≤ primeRank p (Subgroup.centralizer ({z} : Set G)) := by
  let j := f.comp orthogonalLeftHom
  have hj : Function.Injective j := hf.comp orthogonalLeftHom_injective
  obtain ⟨hz, hz2⟩ := map_neg_one_isInvolution hp j hj
  exact ⟨j (-1), hz, hz2, two_mul_fieldExponent_le_primeRank_centralizer hcard f hf⟩
end Atlas.G2
