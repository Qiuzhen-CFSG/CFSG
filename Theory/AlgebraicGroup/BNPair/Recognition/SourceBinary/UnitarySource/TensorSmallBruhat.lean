module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorSecondCartan

/-!
# Exact smaller rank-one Bruhat coefficients in the source U₄ roots

The actual smaller SL₂ actor supplies an unlabelled two-cell equation on
the specified reflection. Compare its conjugation on C(1) and A(1) in
the same A–D–C coordinates. The first comparison forces the reciprocal
root coefficient; the second determines the remaining torus weight.
The two weights identify the entire Cartan parameter, including q=2.

The coordinate uniqueness proof uses the disjoint actual simple root and
complementary subgroup and the same Hermitian intertwiner. The source
application constructs every premise and assembles all FourData equations.
No identification between the two actor fields is assumed here.
Source: Fong--Seitz II (8B), pp.201--202, especially (8.7)--(8.9),
and the rank-one decomposition of §7. The exact reciprocal convention is
FourBruhat.bTorus. Consumer: UnitarySource/TensorEquationApplication.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace FourTensor
variable {Y E : Type*} [Group Y] [Field E] [CharP E 2]
  (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "K" => Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ
variable (R : PositiveMaps Y (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)) (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
  (rel : FourPositive.Relations E σ hσ R)

def coreWord (a : E) (d : K) (c : E) : Y := R.A (Multiplicative.ofAdd a) * R.D (Multiplicative.ofAdd d) * R.C (Multiplicative.ofAdd c)

omit [CharP E 2] in
include rel in
theorem conj_B_coreWord (b : K) (a : E) (d : K) (c : E) :
    MulAut.conj (R.B (Multiplicative.ofAdd b)) (coreWord σ R a d c) =
      coreWord σ R a (FourPositive.normParameter E σ hσ a b + d) (a*(b:E)+c) := by
  have hA : MulAut.conj (R.B (Multiplicative.ofAdd b)) (R.A (Multiplicative.ofAdd a)) = coreWord σ R a (FourPositive.normParameter E σ hσ a b) (a*(b:E)) := by
    change R.B (Multiplicative.ofAdd b) * R.A (Multiplicative.ofAdd a) * (R.B (Multiplicative.ofAdd b))⁻¹ = _
    rw [rel.BA,mul_inv_cancel_right]
    rfl
  have hD : MulAut.conj (R.B (Multiplicative.ofAdd b)) (R.D (Multiplicative.ofAdd d)) = R.D (Multiplicative.ofAdd d) := by
    change R.B (Multiplicative.ofAdd b) * R.D (Multiplicative.ofAdd d) * (R.B (Multiplicative.ofAdd b))⁻¹ = _
    rw [(rel.BD _ _).eq,mul_inv_cancel_right]
  have hC : MulAut.conj (R.B (Multiplicative.ofAdd b)) (R.C (Multiplicative.ofAdd c)) = R.C (Multiplicative.ofAdd c) := by
    change R.B (Multiplicative.ofAdd b) * R.C (Multiplicative.ofAdd c) * (R.B (Multiplicative.ofAdd b))⁻¹ = _
    rw [(rel.BC _ _).eq,mul_inv_cancel_right]
  simp only [coreWord,map_mul,hA,hD,hC]
  change (R.A (Multiplicative.ofAdd a) * R.D (Multiplicative.ofAdd _) * R.C (Multiplicative.ofAdd _)) * R.D (Multiplicative.ofAdd d) * R.C (Multiplicative.ofAdd c) = R.A (Multiplicative.ofAdd a) * R.D (Multiplicative.ofAdd _) * R.C (Multiplicative.ofAdd _)
  calc
    _ = R.A (.ofAdd a) * (R.D (.ofAdd (FourPositive.normParameter E σ hσ a b)) *
      (R.C (.ofAdd (a*(b:E))) * R.D (.ofAdd d))) * R.C (.ofAdd c) := by group
    _ = R.A (.ofAdd a) * (R.D (.ofAdd (FourPositive.normParameter E σ hσ a b)) *
      (R.D (.ofAdd d) * R.C (.ofAdd (a*(b:E))))) * R.C (.ofAdd c) := by rw [(rel.CD _ _).eq]
    _ = R.A (.ofAdd a) * (R.D (.ofAdd (FourPositive.normParameter E σ hσ a b)) * R.D (.ofAdd d)) *
      (R.C (.ofAdd (a*(b:E))) * R.C (.ofAdd c)) := by group
    _ = _ := by rw [←map_mul R.D,←map_mul R.C,←ofAdd_add,←ofAdd_add]


variable (t : Y) (ht2 : t*t=1)
  (htA : ∀ a, t*R.A (Multiplicative.ofAdd a)*t=R.C (Multiplicative.ofAdd a)) (htC : ∀ c, t*R.C (Multiplicative.ofAdd c)*t=R.A (Multiplicative.ofAdd c))
  (htD : ∀ d, t*R.D (Multiplicative.ofAdd d)*t=R.D (Multiplicative.ofAdd d))

omit [CharP E 2] in
include rel ht2 htA htC htD in
theorem conj_t_coreWord (a : E) (d : K) (c : E) :
    MulAut.conj t (coreWord σ R a d c) =
      coreWord σ R c (FourPositive.traceParameter E σ hσ c a + d) a := by
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right ht2
  have htA' a : MulAut.conj t (R.A (Multiplicative.ofAdd a)) = R.C (Multiplicative.ofAdd a) := by simpa only [MulAut.conj_apply,hti] using htA a
  have htC' c : MulAut.conj t (R.C (Multiplicative.ofAdd c)) = R.A (Multiplicative.ofAdd c) := by simpa only [MulAut.conj_apply,hti] using htC c
  have htD' d : MulAut.conj t (R.D (Multiplicative.ofAdd d)) = R.D (Multiplicative.ofAdd d) := by simpa only [MulAut.conj_apply,hti] using htD d
  simp only [coreWord,map_mul,htA',htD',htC']
  rw [(rel.CD _ _).eq,mul_assoc,rel.CA]
  rw [←mul_assoc,←mul_assoc,←(rel.AD (.ofAdd c) (.ofAdd d)).eq]
  rw [mul_assoc (R.A (.ofAdd c)),←map_mul,←ofAdd_add,add_comm d]

variable (cartan : FourWeyl.torusParameters E σ →* Y)
  (hwA : ∀ p a, cartan p*R.A (Multiplicative.ofAdd a)*(cartan p)⁻¹ = R.A (Multiplicative.ofAdd (((p.val.1:E)/(p.val.2:E))*a)))
  (hwD : ∀ p d, cartan p*R.D (Multiplicative.ofAdd d)*(cartan p)⁻¹ = R.D (Multiplicative.ofAdd (FourPositive.normParameter E σ hσ p.val.1 d)))
  (hwC : ∀ p c, cartan p*R.C (Multiplicative.ofAdd c)*(cartan p)⁻¹ = R.C (Multiplicative.ofAdd (((p.val.1:E)*σ (p.val.2:E))*c)))

omit [CharP E 2] in
include hwA hwD hwC in
theorem conj_cartan_coreWord (p : FourWeyl.torusParameters E σ) (a : E) (d : K) (c : E) :
    MulAut.conj (cartan p) (coreWord σ R a d c) =
      coreWord σ R (((p.val.1:E)/(p.val.2:E))*a)
        (FourPositive.normParameter E σ hσ p.val.1 d) (((p.val.1:E)*σ (p.val.2:E))*c) := by
  simp only [coreWord,map_mul,MulAut.conj_apply,hwA,hwD,hwC]

variable [Finite E]
variable (huniq : ∀ a d c a' d' c', coreWord σ R a d c = coreWord σ R a' d' c' → a=a' ∧ c=c')

include rel ht2 htA htC htD hwA hwD hwC huniq in
/-- The existing unlabelled Bruhat word has the exact fixed-field
reciprocal and full Cartan parameter, forced by its action on A and C. -/
theorem small_bruhat_coefficients (b u : K) (hb : b ≠ 0) (p : FourWeyl.torusParameters E σ)
    (heq : t*R.B (.ofAdd b)*t = R.B (.ofAdd u)*cartan p*t*R.B (.ofAdd u)) :
    u=b⁻¹ ∧ p=FourBruhat.bTorus E σ b hb := by
  have heC := congrArg (fun x : Y => MulAut.conj x (coreWord σ R 0 0 1)) heq
  have heA := congrArg (fun x : Y => MulAut.conj x (coreWord σ R 1 0 0)) heq
  simp only [map_mul,MulAut.mul_apply,
    conj_t_coreWord σ hσ R rel t ht2 htA htC htD,
    conj_B_coreWord σ hσ R rel,
    conj_cartan_coreWord σ hσ R cartan hwA hwD hwC,
    mul_zero,zero_mul,mul_one,one_mul,zero_add,add_zero] at heC heA
  obtain ⟨ha,hc⟩ := huniq _ _ _ _ _ _ heC
  obtain ⟨_,hd⟩ := huniq _ _ _ _ _ _ heA
  have hau : (b:E)*(u:E)=1 := by simpa only [←ha] using hc.symm
  have hu : u=b⁻¹ := by
    apply Subtype.ext
    have hbE : (b:E) ≠ 0 := fun hz => hb (Subtype.ext hz)
    apply mul_left_cancel₀ hbE
    change (b:E)*(u:E)=(b:E)*(b:E)⁻¹
    rw [hau,mul_inv_cancel₀ hbE]
  have hwc : (p.val.1:E)*σ (p.val.2:E) = (u:E) := by
    rw [←ha,hau,one_mul] at hd
    exact (CharTwo.add_eq_zero.mp hd.symm).symm
  refine ⟨hu,FourCartan.parameter_ext_AC E σ p _ ?_ ?_⟩
  · change (p.val.1:E)/(p.val.2:E) = 1/(b:E)⁻¹
    simpa only [one_div,inv_inv] using ha.symm
  · change (p.val.1:E)*σ (p.val.2:E) = 1*σ ((b:E)⁻¹)
    rw [one_mul,map_inv₀,show σ (b:E)=(b:E) from b.property,hwc,hu]
    rfl

end FourTensor
open RootCoordinates HexagonStructure GTwoSource
open scoped MatrixGroups
open Theory.PSL2.SemilinearCoverage
variable {X E F : Type*} [Group X] [Field E] [CharP E 2] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "K" => Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ
variable (R : PositiveMaps (X ⧸ Q.D) (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)) (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
  (cartan : FourWeyl.torusParameters E σ →* X ⧸ Q.D)
  (ht : cartan.range = Q.tits.B ⊓ Q.tits.N)
  (j : Fin 2) (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (μ : localGroup Q split j ≃* PSL(2,F)) (t : RootReflection Q split j)
  (hB : R.B.range = simpleRoot Q split j) (hBi : Function.Injective R.B)

omit [CharP E 2] in
include ht hB hBi hVj μ in
/-- The existing smaller SL₂ pinning supplies an unlabelled Bruhat word
on the same reflection and the entire source Cartan. -/
theorem exists_second_bruhat (b : K) (hb : b ≠ 0) :
    ∃ (u : K) (p : FourWeyl.torusParameters E σ),
      (t.val : X ⧸ Q.D)*R.B (.ofAdd b)*t.val =
        R.B (.ofAdd u)*cartan p*t.val*R.B (.ofAdd u) := by
  let l := alignedPinningHom Q split j hVj μ t
  let A := alignedSimpleParameter Q split j hVj μ t
  have hmem : R.B (.ofAdd b) ∈ A.range := by
    rw [alignedSimpleParameter_range,←hB]
    exact ⟨_,rfl⟩
  obtain ⟨x,hx⟩ := hmem
  have hx0 : x.toAdd ≠ 0 := by
    intro hz
    have hx1 : x = 1 := hz
    have hh : R.B (.ofAdd b) = 1 := by rw [←hx,hx1,map_one]
    exact hb (Multiplicative.ofAdd.injective (hBi (hh.trans (map_one R.B).symm)))
  have hu : A (.ofAdd x.toAdd⁻¹) ∈ R.B.range := by
    rw [hB,←alignedSimpleParameter_range Q split j hVj μ t]
    exact ⟨_,rfl⟩
  obtain ⟨u,hu⟩ := hu
  obtain ⟨p,hp⟩ := (ht.symm ▸ alignedTorus_mem_cartan Q split j hVj μ t (Units.mk0 x.toAdd hx0)⁻¹)
  refine ⟨u.toAdd,p,?_⟩
  simp only [ofAdd_toAdd]
  rw [hu,hp,←hx]
  change (t.val : X ⧸ Q.D)*l (uni x.toAdd)*t.val =
    l (uni x.toAdd⁻¹)*l (tor (Units.mk0 x.toAdd hx0)⁻¹)*t.val*l (uni x.toAdd⁻¹)
  rw [←alignedPinningHom_weyl Q split j hVj μ t]
  change l (weyl F)*l (uni x.toAdd)*l (weyl F) =
    l (uni x.toAdd⁻¹)*l (tor (Units.mk0 x.toAdd hx0)⁻¹)*l (weyl F)*l (uni x.toAdd⁻¹)
  simp only [←map_mul]
  apply congrArg l
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,hx0,CharTwo.add_self_eq_zero]


open Matrix
namespace FourTensor
variable {X E : Type*} [Group X] [Field E] [CharP E 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : E ≃+* E) (hσ : Function.Involutive σ) (i : Fin 2)
  (l : SpecialLinearGroup (Fin 2) E →* X ⧸ Q.D)
  (e : Multiplicative (Core E σ hσ) ≃* simpleRemainder Q split i)
omit [CharP E 2] in
theorem tensor_coreWord_unique :
    let r := roots E σ hσ l ((simpleRemainder Q split i).subtype.comp e.toMonoidHom)
    r.A.range = simpleRoot Q split i → Function.Injective r.A →
    ∀ (a a' : E) (d d' : Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ) (c c' : E),
      coreWord σ r a d c = coreWord σ r a' d' c' → a=a' ∧ d=d' ∧ c=c'  := by
  dsimp only
  intro hA hAi a a' d d' c c' heq
  let v := (simpleRemainder Q split i).subtype.comp e.toMonoidHom
  let r := roots E σ hσ l v
  have hmem (x : E) : (r).A (.ofAdd x) ∈ simpleRoot Q split i := hA ▸ ⟨_,rfl⟩
  let p (a : E) (d : Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ) (c : E) : simpleRoot Q split i × simpleRemainder Q split i :=
    (⟨(r).A (.ofAdd a),hmem a⟩,e (.ofAdd (diagonalTop E σ hσ d + offDiagonal E σ hσ c)))
  have hprod (a : E) (d : Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ) (c : E) :
      (p a d c).1.val * (p a d c).2.val = coreWord σ r a d c := by
    change (r).A (.ofAdd a) * v (.ofAdd (diagonalTop E σ hσ d + offDiagonal E σ hσ c)) = _
    rw [ofAdd_add,map_mul]
    exact (mul_assoc _ _ _).symm
  have hp : p a d c = p a' d' c' :=
    mul_injective_of_disjoint (simpleRoot_disjoint_remainder Q split i)
      ((hprod a d c).trans (heq.trans (hprod a' d' c').symm))
  have ha : a=a' := Multiplicative.ofAdd.injective
    (hAi (congrArg (fun x : simpleRoot Q split i × simpleRemainder Q split i => x.1.val) hp))
  have hv := Multiplicative.ofAdd.injective
    (e.injective (congrArg Prod.snd hp))
  have hd : d=d' := by
    apply Subtype.ext
    simpa [diagonalTop,offDiagonal] using congrArg (fun x : Core E σ hσ => x.val 0 0) hv
  have hc : c=c' := by
    simpa [diagonalTop,offDiagonal] using congrArg (fun x : Core E σ hσ => x.val 0 1) hv
  exact ⟨ha,hd,hc⟩
end FourTensor

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
