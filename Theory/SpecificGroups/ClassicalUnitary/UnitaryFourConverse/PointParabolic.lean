module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear

/-!
# Local properties of the full unitary-four point parabolic

The stabilizer of the first isotropic line has a normal vector stabilizer,
with cyclic scalar quotient. The vector stabilizer's middle-block quotient
is SL₂ over the fixed field and its Heisenberg radical is a two-group.
This gives odd-prime rank at most two for the full parabolic.

The radical is characteristic in the vector stabilizer, hence normal in the
full parabolic. Its common fixed space is exactly the first coordinate line,
so its ambient normalizer is the full parabolic. Two explicit root elements
also force every element centralizing the radical to be upper triangular
with constant diagonal. Unit determinant makes that diagonal one in
characteristic two, proving the intrinsic two-core centralizer bound.

These calculations hold for every finite field of characteristic two and
every involutive field automorphism. In particular they include all the
requested standard fields of order `(2^n)^2`, including `n = 1`.

Source: Aschbacher--Smith, Theorem 0.1.2(1), printed p.4 (restated as
Theorem 0.1.1(1), printed p.482), `refs/quasithin.pdf`; the parabolic and
radical conventions are those of GLS III, §§3.1--3.2,
`refs/KGroup/GLS3/chapter3.tex`. This module proves the full line-stabilizer
properties; arbitrary-form transport and classification assembly are separate.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic

variable (F : Type*) [Field F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
/-- Every radical element has fourth power one, with no restriction on field size. -/
theorem radical_isTwoGroup : IsPGroup 2 (radical F σ hσ) := by
  intro a
  refine ⟨2, ?_⟩
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change radicalMatrix F σ c ^ (2 ^ 2) = 1
  change radicalMatrix F σ c ^ (2 * 2) = 1
  rw [pow_mul, pow_two, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      CharTwo.add_self_eq_zero]

variable [Finite F]

local notation "P" => pointParabolicSU F (form F σ hσ)
local notation "L" => localSU F (form F σ hσ)

/-- The full line stabilizer acts on its line through the cyclic group of field units. -/
def scalarHom : P →* Fˣ := (pointScalar F (form F σ hσ)).toHomUnits

omit [CharP F 2] in
/-- The kernel fixes the first vector, and is relative to the full parabolic. -/
theorem scalarHom_ker : (scalarHom F σ hσ).ker =
    (L).subgroupOf (P) := by
  rw [localSU_subgroupOf_eq_ker]
  ext g
  change scalarHom F σ hσ g = 1 ↔ pointScalar F (form F σ hσ) g = 1
  exact Units.ext_iff

/-- The Heisenberg radical embedded in the full line stabilizer. -/
def parabolicRadical : Subgroup (P) :=
  (radical F σ hσ).map (Subgroup.inclusion (localSU_le_pointParabolicSU F _))

/-- The embedded radical is a two-group. -/
theorem parabolicRadical_isTwoGroup : IsPGroup 2 (parabolicRadical F σ hσ) :=
  (radical_isTwoGroup F σ hσ).map _

/-- The radical is characteristic in the normal vector stabilizer. -/
instance parabolicRadical_normal : (parabolicRadical F σ hσ).Normal := by
  let e := (Subgroup.subgroupOfEquivOfLe (localSU_le_pointParabolicSU F (form F σ hσ))).symm
  have hi : Subgroup.inclusion (localSU_le_pointParabolicSU F (form F σ hσ)) =
      ((L).subgroupOf (P)).subtype.comp e.toMonoidHom := rfl
  rw [parabolicRadical, radical_eq_twoCore F σ hσ (radical_isTwoGroup F σ hσ),
    hi, ← Subgroup.map_map, pCore_map_iso]
  infer_instance

/-- Relative normality places the radical in the intrinsic two-core. -/
theorem parabolicRadical_le_twoCore : parabolicRadical F σ hσ ≤ pCore 2 (P) :=
  le_sSup ⟨inferInstance, parabolicRadical_isTwoGroup F σ hσ⟩

/-- The SL₂ quotient and the cyclic scalar quotient each contribute at most one to odd rank. -/
theorem primeRank_le_two {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (P) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let f := (middleEquivSL F σ hσ).toMonoidHom.comp (middleSU F σ hσ)
  have hk : f.ker = radical F σ hσ := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ (middleEquivSL F σ hσ).injective]
    exact middleSU_ker F σ hσ
  have hz : primeRank p f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    intro hd
    have hker : IsPGroup 2 f.ker := hk ▸ radical_isTwoGroup F σ hσ
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn] at hd
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    rw [hp2] at ho
    exact ho.not_two_dvd_nat (dvd_refl 2)
  have hsl : primeRank p (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) ≤ 1 := by
    let T : Sylow p (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) := default
    apply T.primeRank_le_one_of_isCyclic
    exact Matrix.SL2.odd_pGroup_isCyclic_of_injective T.isPGroup'
      (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2))
      (T : Subgroup (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ))).subtype
      (T : Subgroup (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ))).subtype_injective
  have hl : primeRank p (L) ≤ 1 := by
    have hb := Theory.GroupTheory.primeRank_le_ker_add (p := p) f
    rw [hz, zero_add] at hb
    exact hb.trans hsl
  have hc : primeRank p (scalarHom F σ hσ).ker ≤ 1 := by
    rw [scalarHom_ker, Theory.GroupTheory.primeRank_equiv p
      (Subgroup.subgroupOfEquivOfLe (localSU_le_pointParabolicSU F _))]
    exact hl
  have hu : primeRank p Fˣ ≤ 1 := by
    let T : Sylow p Fˣ := default
    exact T.primeRank_le_one_of_isCyclic inferInstance
  exact (Theory.GroupTheory.primeRank_le_ker_add (scalarHom F σ hσ)).trans
    (Nat.add_le_add hc hu)


/-- The same radical embedded in the ambient special unitary group. -/
def ambientRadical : Subgroup (SU F (form F σ hσ)) :=
  (radical F σ hσ).map (localSU F (form F σ hσ)).subtype

omit [CharP F 2] [Finite F] in
/-- Radical matrices fix the first vector. -/
theorem ambientRadical_le_local : ambientRadical F σ hσ ≤ L :=
  Subgroup.map_subtype_le _

omit [CharP F 2] in
/-- The ambient radical lies in the full line stabilizer. -/
theorem ambientRadical_le_parabolic : ambientRadical F σ hσ ≤ P :=
  (ambientRadical_le_local F σ hσ).trans (localSU_le_pointParabolicSU F _)

omit [CharP F 2] in
/-- Restricting the ambient radical to the parabolic recovers its intrinsic embedding. -/
theorem ambientRadical_subgroupOf : (ambientRadical F σ hσ).subgroupOf (P) =
    parabolicRadical F σ hσ := by
  ext x
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, Subtype.ext h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, congrArg Subtype.val h⟩

/-- The full parabolic normalizes the ambient radical. -/
theorem parabolic_le_normalizer :
    P ≤ Subgroup.normalizer (ambientRadical F σ hσ : Set (SU F (form F σ hσ))) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientRadical_le_parabolic F σ hσ)).mp
  rw [ambientRadical_subgroupOf]
  infer_instance

omit [CharP F 2] [Finite F] in
private theorem column_fixed (g : SU F (form F σ hσ))
    (hg : g ∈ Subgroup.normalizer (ambientRadical F σ hσ : Set (SU F (form F σ hσ)))) (r : radical F σ hσ) (i : Fin 4) :
    (r.val.val.val.val * g.val.val) i 0 = g.val.val i 0 := by
  have ht : g⁻¹ * r.val.val * g ∈ ambientRadical F σ hσ :=
    (Subgroup.mem_normalizer_iff''.mp hg r.val.val).mp ⟨r.val, r.property, rfl⟩
  obtain ⟨t0,t1,t2,t3⟩ := (mem_localSU F _ _).mp (ambientRadical_le_local F σ hσ ht)
  have he : r.val.val * g = g * (g⁻¹ * r.val.val * g) := by simp [mul_assoc]
  have hei := congrArg (fun x : SU F (form F σ hσ) => x.val.val i 0) he
  change (r.val.val.val.val * g.val.val) i 0 =
    (g.val.val * (g⁻¹ * r.val.val * g).val.val) i 0 at hei
  generalize g⁻¹ * r.val.val * g = t at t0 t1 t2 t3 hei
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, t0,t1,t2,t3] using hei

/-- The radical has exactly the first coordinate line as its common fixed space. -/
theorem normalizer_ambientRadical :
    Subgroup.normalizer (ambientRadical F σ hσ : Set (SU F (form F σ hσ))) = P := by
  apply le_antisymm _ (parabolic_le_normalizer F σ hσ)
  intro g hg
  rw [mem_pointParabolicSU]
  have hx0 := column_fixed F σ hσ g hg (radicalOfCoordinates F σ hσ ⟨1,0,0,by simp⟩) 0
  have hx1 := column_fixed F σ hσ g hg (radicalOfCoordinates F σ hσ ⟨1,0,0,by simp⟩) 1
  have hy0 := column_fixed F σ hσ g hg (radicalOfCoordinates F σ hσ ⟨0,1,0,by simp⟩) 0
  simp [radicalOfCoordinates, radicalElement, radicalMatrix,
    Matrix.mul_apply, Fin.sum_univ_succ] at hx0 hx1 hy0
  exact ⟨hy0, hx0, hx1⟩

omit [Finite F] in
/-- The root element with horizontal coordinate `(1,0)` is nonidentity. -/
theorem ambientRadical_ne_bot : ambientRadical F σ hσ ≠ ⊥ := by
  intro he
  let r := radicalOfCoordinates F σ hσ ⟨1,0,0,by simp⟩
  have hr : r.val.val ∈ ambientRadical F σ hσ := ⟨r.val, r.property, rfl⟩
  rw [he] at hr
  have h := congrArg (fun x : SU F (form F σ hσ) => x.val.val 1 3) (Subgroup.mem_bot.mp hr)
  exact one_ne_zero h

/-- The full point parabolic is the normalizer of a nontrivial two-subgroup. -/
theorem isTwoLocal : IsTwoLocal (P) :=
  ⟨ambientRadical F σ hσ, ambientRadical_ne_bot F σ hσ,
    (radical_isTwoGroup F σ hσ).map _, (normalizer_ambientRadical F σ hσ).symm⟩


/-- Commuting with two explicit radical matrices forces a scalar diagonal;
unit determinant and characteristic two make that diagonal the identity. -/
theorem centralizer_ambientRadical_le :
    Subgroup.centralizer (ambientRadical F σ hσ : Set (SU F (form F σ hσ))) ≤
      ambientRadical F σ hσ := by
  intro g hg
  have hc (c : RadicalCoordinates F σ) :
      g.val.val * radicalMatrix F σ c = radicalMatrix F σ c * g.val.val := by
    exact congrArg (fun x : SU F (form F σ hσ) => x.val.val)
      ((Subgroup.mem_centralizer_iff.mp hg (radicalElement F σ hσ c)
        ⟨(radicalOfCoordinates F σ hσ c).val,
          (radicalOfCoordinates F σ hσ c).property, rfl⟩).symm)
  have hx (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j)
    (hc ⟨1,0,0,by simp⟩)
  have hy (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i j)
    (hc ⟨0,1,0,by simp⟩)
  have h20 := hx 0 0
  have h10 := hy 0 0
  have h30 := hx 1 0
  have h21 := hx 0 1
  have h12 := hy 0 2
  have h31 := hx 1 1
  have h32 := hy 2 2
  have h22 := hx 0 2
  have h11 := hy 0 1
  have h33 := hx 1 3
  simp [radicalMatrix, Matrix.mul_apply, Fin.sum_univ_succ] at h20 h10 h30 h21 h12 h31 h32 h22 h11 h33
  have h22' : g.val.val 0 0 = g.val.val 2 2 := by linear_combination h22
  have h11' : g.val.val 0 0 = g.val.val 1 1 := by linear_combination h11
  have h33' : g.val.val 1 1 = g.val.val 3 3 := by linear_combination h33
  have hdiag : g.val.val 0 0 ^ 4 = 1 := by
    have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
    rw [Matrix.det_of_isUpperTriangular] at hd
    · simpa [Fin.prod_univ_succ, ← h11', ← h22', ← h33', pow_succ, mul_assoc] using hd
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have h00 : g.val.val 0 0 = 1 := (iterateFrobeniusEquiv F 2 2).injective (by
    change g.val.val 0 0 ^ (2 ^ 2) = (1 : F) ^ (2 ^ 2)
    simpa using hdiag)
  have hlocal : g ∈ localSU F (form F σ hσ) :=
    (mem_localSU F _ g).mpr ⟨h00,h10,h20,h30⟩
  refine ⟨⟨g,hlocal⟩, ?_, rfl⟩
  exact (mem_radical F σ hσ ⟨g,hlocal⟩).mpr
    ⟨h11'.symm.trans h00, h12, h21, h22'.symm.trans h00⟩

/-- The intrinsic two-core of the full point parabolic contains its centralizer. -/
theorem centralizer_twoCore_le :
    Subgroup.centralizer (pCore 2 (P) : Set (P)) ≤ pCore 2 (P) := by
  intro g hg
  apply parabolicRadical_le_twoCore F σ hσ
  rw [← ambientRadical_subgroupOf]
  apply centralizer_ambientRadical_le F σ hσ
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  let rP : P := ⟨r, ambientRadical_le_parabolic F σ hσ hr⟩
  have hrP : rP ∈ parabolicRadical F σ hσ := by
    rw [← ambientRadical_subgroupOf]
    exact hr
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg) rP
    (parabolicRadical_le_twoCore F σ hσ hrP))

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic
