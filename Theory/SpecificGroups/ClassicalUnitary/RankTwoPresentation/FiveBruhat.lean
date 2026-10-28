module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveWeyl
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixRankOne
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.RankOneCollection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group

/-!
# Rank-one Bruhat equations in the literal general unitary five-space

The two Bruhat root parameters retain the Hermitian trace condition. The
middle determinant correction belongs to the full torus, and all equations
hold in the existing identity-form SU₅ after the one fixed basis permutation.
Source: Steinberg, Lectures on Chevalley Groups, Lemma 24 and Lemma 63(c).
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveBruhat
open FivePositive FiveWeyl
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

/-- A nonidentity Hermitian parameter has nonzero second coordinate. -/
theorem snd_ne_zero {p : Parameter J} (hp : p≠1) : p.val.2≠0 := by
  intro hz
  have hn := parameter_relation J p
  rw [hz,map_zero,zero_add] at hn
  have hx : p.val.1=0 := by
    rcases mul_eq_zero.mp hn.symm with hx|hx
    · exact hx
    · exact (map_eq_zero J.conj).mp hx
  apply hp
  apply Subtype.ext
  exact Prod.ext hx hz

/-- Left root parameter in the Hermitian rank-one Bruhat equation. -/
def leftParameter (p : Parameter J) (hz : p.val.2≠0) : Parameter J :=
  ⟨(p.val.1/J.conj p.val.2,p.val.2⁻¹),by
    have hsz : J.conj p.val.2≠0 := (map_ne_zero J.conj).mpr hz
    change p.val.2⁻¹+J.conj (p.val.2⁻¹)+
      (p.val.1/J.conj p.val.2)*J.conj (p.val.1/J.conj p.val.2)=0
    rw [map_inv₀,map_div₀,J.conj_involutive]
    field_simp
    linear_combination p.property⟩

/-- Right root parameter in the same Hermitian rank-one Bruhat equation. -/
def rightParameter (p : Parameter J) (hz : p.val.2≠0) : Parameter J :=
  ⟨(p.val.1/p.val.2,p.val.2⁻¹),by
    have hsz : J.conj p.val.2≠0 := (map_ne_zero J.conj).mpr hz
    change p.val.2⁻¹+J.conj (p.val.2⁻¹)+
      (p.val.1/p.val.2)*J.conj (p.val.1/p.val.2)=0
    rw [map_inv₀,map_div₀]
    field_simp
    linear_combination p.property⟩

def aTorus (v : E) (hv : v≠0) : Eˣ × Eˣ := ((Units.mk0 v hv)⁻¹,Units.mk0 v hv)
def bTorus (p : Parameter J) (hz : p.val.2≠0) : Eˣ × Eˣ :=
  (1,(Units.map J.conj.toMonoidHom (Units.mk0 p.val.2 hz))⁻¹)

theorem s_A (v : E) (hv : v≠0) :
    s J κ hκ hJ*A J κ hκ hJ v*s J κ hκ hJ =
      A J κ hκ hJ v⁻¹*h J κ hκ hJ (aTorus v hv)*s J κ hκ hJ*A J κ hκ hJ v⁻¹ := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_s,evaluate_A,evaluate_h]
  simp only [aTorus,Units.val_inv_eq_inv_val,Units.val_mk0]
  exact Matrix5.S_A_bruhat J.conj v hv

theorem t_B (p : Parameter J) (hz : p.val.2≠0) :
    t J κ hκ hJ*B J hJ p*t J κ hκ hJ =
      B J hJ (leftParameter J p hz)*h J κ hκ hJ (bTorus J p hz)*
        t J κ hκ hJ*B J hJ (rightParameter J p hz) := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_t,evaluate_B,evaluate_h]
  simp only [leftParameter,rightParameter,bTorus,Units.val_one,Units.val_inv_eq_inv_val,
    Units.coe_map,Units.val_mk0]
  exact Matrix5.T_B_bruhat J.conj J.conj_involutive p.val.1 p.val.2 hz (parameter_relation J p)

private theorem involution_transport {G : Type*} [Group G] (w x y : G)
    (hw : w^2=1) (he : w*x*w=y) : w*y*w=x := by
  have hww : w*w=1 := by simpa only [pow_two] using hw
  rw [←he]
  calc
    w*(w*x*w)*w=(w*w)*x*(w*w) := by simp only [mul_assoc]
    _ = x := by rw [hww,one_mul,mul_one]

/-- The complete reflection input for the relative BC₂ model, at arbitrary q. -/
theorem reflectionLaws : ReflectionLaws (roots J κ hκ hJ) (h J κ hκ hJ) (s J κ hκ hJ) (t J κ hκ hJ) where
  ss := by simpa only [pow_two] using s_sq J κ hκ hJ
  tt := by simpa only [pow_two] using t_sq J κ hκ hJ
  sD d := ⟨d,involution_transport _ _ _ (s_sq J κ hκ hJ) (s_B J κ hκ hJ d)⟩
  sC c := ⟨Multiplicative.ofAdd (J.conj c.toAdd),s_C J κ hκ hJ c.toAdd⟩
  sB b := ⟨b,s_B J κ hκ hJ b⟩
  tA a := ⟨Multiplicative.ofAdd a.toAdd,t_A J κ hκ hJ a.toAdd⟩
  tD d := ⟨d,t_D J κ hκ hJ d⟩
  tC c := ⟨Multiplicative.ofAdd c.toAdd,
    involution_transport _ _ _ (t_sq J κ hκ hJ) (t_A J κ hκ hJ c.toAdd)⟩
  sA a := by
    by_cases ha : a=1
    · left; subst a
      simp only [map_one,mul_one]
      simpa only [pow_two] using s_sq J κ hκ hJ
    · right
      have hv : a.toAdd≠0 := by simpa using ha
      exact ⟨Multiplicative.ofAdd a.toAdd⁻¹,aTorus a.toAdd hv,
        Multiplicative.ofAdd a.toAdd⁻¹,s_A J κ hκ hJ a.toAdd hv⟩
  tB b := by
    by_cases hb : b=1
    · left; subst b
      simp only [map_one,mul_one]
      simpa only [pow_two] using t_sq J κ hκ hJ
    · right
      have hz := snd_ne_zero J hb
      exact ⟨leftParameter J b hz,bTorus J b hz,rightParameter J b hz,t_B J κ hκ hJ b hz⟩

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveBruhat
