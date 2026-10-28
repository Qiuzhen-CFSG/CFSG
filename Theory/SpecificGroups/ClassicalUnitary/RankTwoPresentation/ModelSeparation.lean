module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelEightCells
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixCells

/-!
# Faithful Borel coordinates and separated unitary Weyl representatives

The first two diagonal entries recover the entire torus parameter. Cancelling
that torus reduces equality to the already proved positive-coordinate
uniqueness. The matrix pivots then show that only the identity Weyl word
belongs to the generated Borel. These are the concrete faithfulness inputs
for Steinberg's Bruhat presentation argument, Lectures on Chevalley Groups,
Theorem 4(b) and the proof of Theorem 9. Both full Hermitian parameters and
the literal SU₅ basis transport are retained.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace FourCells
open UnitaryFourFlag UnitaryFourSylow FourPositive FourWeyl
variable (E : Type*) [Field E] [Finite E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ
local notation "K" => FixedField E σ

def evaluate : SU E J →* Matrix (Fin 4) (Fin 4) E :=
  (Units.coeHom _).comp (form E σ hσ).specialSubgroup.subtype

omit [Finite E] in
theorem borel_coordinates_injective : Function.Injective
    (fun p : Multiplicative E × Multiplicative K × Multiplicative E × Multiplicative K × torusParameters E σ =>
      (roots E σ hσ).word p.1 p.2.1 p.2.2.1 p.2.2.2.1*hHom E σ hσ p.2.2.2.2) := by
  rintro ⟨a,d,c,b,k⟩ ⟨a',d',c',b',k'⟩ he
  have hm := congrArg (evaluate E σ hσ) he
  change (A E σ hσ a.toAdd).val.val*(D E σ hσ d.toAdd).val.val*(C E σ hσ c.toAdd).val.val*
    (B E σ hσ b.toAdd).val.val*(h E σ hσ k).val.val =
    (A E σ hσ a'.toAdd).val.val*(D E σ hσ d'.toAdd).val.val*(C E σ hσ c'.toAdd).val.val*
    (B E σ hσ b'.toAdd).val.val*(h E σ hσ k').val.val at hm
  simp only [A_val,D_val,C_val,B_val,h_val] at hm
  have h0 := congrArg (fun m : Matrix (Fin 4) (Fin 4) E => m 0 0) hm
  have h1 := congrArg (fun m : Matrix (Fin 4) (Fin 4) E => m 1 1) hm
  simp only [Matrix4.word_torus_diagonal] at h0 h1
  change (k.val.1:E)=(k'.val.1:E) at h0
  change (k.val.2:E)=(k'.val.2:E) at h1
  have hk : k=k' := Subtype.ext (Prod.ext (Units.ext h0) (Units.ext h1))
  subst k'
  have hw := mul_right_cancel he
  have hp : (a.toAdd,d.toAdd,c.toAdd,b.toAdd)=(a'.toAdd,d'.toAdd,c'.toAdd,b'.toAdd) :=
    FourPositive.word_injective E σ hσ hw
  have hp' : (a,d,c,b)=(a',d',c',b') := congrArg
    (fun p : E × K × E × K => (Multiplicative.ofAdd p.1,Multiplicative.ofAdd p.2.1,
      Multiplicative.ofAdd p.2.2.1,Multiplicative.ofAdd p.2.2.2)) hp
  cases hp'
  rfl

omit [Finite E] in
theorem borel_triangular {x : SU E J} (hx : x∈(roots E σ hσ).borel (hHom E σ hσ)) :
    (evaluate E σ hσ x).IsUpperTriangular := by
  obtain ⟨a,d,c,b,k,rfl⟩ := (FourTorus.torusLaws E σ hσ).exists_word (collects E σ hσ) hx
  change ((A E σ hσ a.toAdd).val.val*(D E σ hσ d.toAdd).val.val*(C E σ hσ c.toAdd).val.val*
    (B E σ hσ b.toAdd).val.val*(h E σ hσ k).val.val).IsUpperTriangular
  simp only [A_val,D_val,C_val,B_val,h_val]
  exact Matrix4.word_torus_triangular σ _ _ _ _ _ _

theorem weyl_mem_borel_iff (w : WeylWord) :
    w.eval (s E σ hσ) (t E σ hσ)∈(roots E σ hσ).borel (hHom E σ hσ) ↔ w=.one := by
  constructor
  · intro hw
    have hm := borel_triangular E σ hσ hw
    rw [WeylWord.map_eval] at hm
    exact (Matrix4.weyl_triangular_iff w).mp hm
  · rintro rfl
    exact (roots E σ hσ).borel (hHom E σ hσ) |>.one_mem
end FourCells
namespace FiveCells
open FivePositive FiveWeyl
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

theorem borel_coordinates_injective : Function.Injective
    (fun p : Multiplicative E × Parameter J × Multiplicative E × Parameter J × (Eˣ × Eˣ) =>
      (roots J κ hκ hJ).word p.1 p.2.1 p.2.2.1 p.2.2.2.1*h J κ hκ hJ p.2.2.2.2) := by
  rintro ⟨a,d,c,b,k⟩ ⟨a',d',c',b',k'⟩ he
  have hm := congrArg (evaluate J κ) he
  change evaluate J κ (A J κ hκ hJ a.toAdd*D J hJ d*C J hJ c.toAdd*B J hJ b*h J κ hκ hJ k)=
    evaluate J κ (A J κ hκ hJ a'.toAdd*D J hJ d'*C J hJ c'.toAdd*B J hJ b'*h J κ hκ hJ k') at hm
  simp only [map_mul,evaluate_A,evaluate_D,evaluate_C,evaluate_B,evaluate_h] at hm
  have h0 := congrArg (fun m : Matrix (Fin 5) (Fin 5) E => m 0 0) hm
  have h1 := congrArg (fun m : Matrix (Fin 5) (Fin 5) E => m 1 1) hm
  simp only [Matrix5.word_torus_diagonal] at h0 h1
  change (k.1:E)=(k'.1:E) at h0
  change (k.2:E)=(k'.2:E) at h1
  have hk : k=k' := Prod.ext (Units.ext h0) (Units.ext h1)
  subst k'
  have hw := mul_right_cancel he
  have hp : (a.toAdd,d,c.toAdd,b)=(a'.toAdd,d',c'.toAdd,b') :=
    FivePositive.word_injective J κ hκ hJ hw
  have hp' : (a,d,c,b)=(a',d',c',b') := congrArg
    (fun p : E × Parameter J × E × Parameter J =>
      (Multiplicative.ofAdd p.1,p.2.1,Multiplicative.ofAdd p.2.2.1,p.2.2.2)) hp
  cases hp'
  rfl

theorem borel_triangular {x : J.specialSubgroup} (hx : x∈(roots J κ hκ hJ).borel (h J κ hκ hJ)) :
    (evaluate J κ x).IsUpperTriangular := by
  obtain ⟨a,d,c,b,k,rfl⟩ := (FiveTorus.torusLaws J κ hκ hJ).exists_word (collects J κ hκ hJ) hx
  change (evaluate J κ (A J κ hκ hJ a.toAdd*D J hJ d*C J hJ c.toAdd*B J hJ b*h J κ hκ hJ k)).IsUpperTriangular
  simp only [map_mul,evaluate_A,evaluate_D,evaluate_C,evaluate_B,evaluate_h]
  exact Matrix5.word_torus_triangular J.conj _ _ _ _ _ _ _ _

theorem weyl_mem_borel_iff (w : WeylWord) :
    w.eval (s J κ hκ hJ) (t J κ hκ hJ)∈(roots J κ hκ hJ).borel (h J κ hκ hJ) ↔ w=.one := by
  constructor
  · intro hw
    have hm := borel_triangular J κ hκ hJ hw
    rw [WeylWord.map_eval,evaluate_s,evaluate_t] at hm
    exact (Matrix5.weyl_triangular_iff w).mp hm
  · rintro rfl
    exact (roots J κ hκ hJ).borel (h J κ hκ hJ) |>.one_mem
end FiveCells
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
