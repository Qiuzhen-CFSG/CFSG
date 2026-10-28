module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.AlignedPositive
public import Theory.SpecificGroups.G2.RootPresentationRecognition.BruhatCollection

/-!
# Actual source Borel--Weyl maps and their rank-one equations

Combine the two reflection-aligned coroot maps inside the original full
Cartan H. Assuming the genuine earlier assertion that H is abelian, their
product h(l,m) = h_short(l) h_long(lm) is a homomorphism. Together with
the six existing source root maps and the specified reflections, this
constructs the consumer's BorelWeylData on the SAME marked quotient.

The two rank-one words, the two involution equations, and all eight
non-fixed Weyl root interchanges follow from the whole SL₂ pinnings and
conjugation transport. The actual source assumption G = normalClosure(U)
then gives the consumer's generator closure. No perfectness or lower
bound on the field size is used; in particular F₂ and F₄ are included.

This is not a construction of Relations: the full Cartan's abelianness
must still be discharged, as must the mixed positive equations, torus
weights and Weyl action, braid, and the two orthogonal-root fixed-point
equations. The two-parameter torus is proved to lie in H; its surjectivity
onto H is not asserted. CartanApplication retains the original quotient,
Sylow and both endpoint maps in the literal positive consumer.

Source: Fong--Seitz II §7, (7D), and (9.9)--(9.21), printed pp.192,
194--196 and 213--217. All conjugations here are left conjugations,
with r long and s short as in the published G₂ presentation.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hH : IsMulCommutative ↥(Q.tits.B ⊓ Q.tits.N))

include hH in
theorem alignedTori_commute (a b : Fˣ) :
    Commute (alignedTorusHom Q split short (hK short) (μ short) (n short) a)
      (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) b) := by
  let := hH
  exact congrArg Subtype.val (mul_comm
    (⟨_,alignedTorus_mem_cartan Q split short (hK short) (μ short) (n short) a⟩ : ↥(Q.tits.B ⊓ Q.tits.N))
    (⟨_,alignedTorus_mem_cartan Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) b⟩ :
      ↥(Q.tits.B ⊓ Q.tits.N)))

/-- The source h(l,m) is h_short(l) h_long(lm), in the consumer's convention. -/
def alignedPairTorus : Fˣ × Fˣ →* X ⧸ Q.D where
  toFun p := alignedTorusHom Q split short (hK short) (μ short) (n short) p.1 *
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (p.1*p.2)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, one_mul, map_one]
  map_mul' p q := by
    dsimp only [Prod.fst_mul,Prod.snd_mul]
    rw [show p.1*q.1*(p.2*q.2) = (p.1*p.2)*(q.1*q.2) by ac_rfl]
    rw [map_mul,map_mul]
    exact (alignedTori_commute Q split hK μ n short hH q.1 (p.1*p.2)).mul_mul_mul_comm _ _

@[simp] theorem alignedPairTorus_apply (l m : Fˣ) :
    alignedPairTorus Q split hK μ n short hH (l,m) =
      alignedTorus Q split short (hK short) (μ short) (n short) l *
      alignedTorus Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (l*m) := rfl

@[simp] theorem alignedPairTorus_long (a : Fˣ) :
    alignedPairTorus Q split hK μ n short hH (1,a) =
      alignedTorus Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a := by
  change alignedTorusHom Q split short (hK short) (μ short) (n short) 1 *
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (1*a) = _
  rw [map_one,one_mul,one_mul,alignedTorusHom_apply]

@[simp] theorem alignedPairTorus_short (a : Fˣ) :
    alignedPairTorus Q split hK μ n short hH (a,a⁻¹) =
      alignedTorus Q split short (hK short) (μ short) (n short) a := by
  change alignedTorusHom Q split short (hK short) (μ short) (n short) a *
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (a*a⁻¹) = _
  rw [mul_inv_cancel,map_one,mul_one,alignedTorusHom_apply]

theorem alignedPairTorus_mem (p : Fˣ × Fˣ) :
    alignedPairTorus Q split hK μ n short hH p ∈ Q.tits.B ⊓ Q.tits.N :=
  (Q.tits.B ⊓ Q.tits.N).mul_mem
    (alignedTorus_mem_cartan Q split short (hK short) (μ short) (n short) p.1)
    (alignedTorus_mem_cartan Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) (p.1*p.2))

/-- Actual maps in Y. This definition makes no assertion of the missing relations. -/
def sourceBorelWeyl : BorelWeylData F (X ⧸ Q.D) where
  toPositiveRoots := alignedSourceRoots Q split hK μ n short
  torus := alignedPairTorus Q split hK μ n short hH
  r := (n (1-short)).val
  s := (n short).val

local notation "d" => sourceBorelWeyl Q split hK μ n short hH

theorem sourceBorelWeyl_positive (hm : rotationOrder Q = 6) :
    (d).toPositiveRoots.generated = split.U := alignedSourceRoots_generated Q split hK μ n short hm

theorem sourceBorelWeyl_highest : (d).x 0 1 ≠ 1 := alignedSourceRoots_highest_nontrivial Q split hK μ n short

theorem sourceBorelWeyl_r_sq : (d).r^2 = 1 := by
  simpa only [sourceBorelWeyl,pow_two] using sourceReflection_sq Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
theorem sourceBorelWeyl_s_sq : (d).s^2 = 1 := by
  simpa only [sourceBorelWeyl,pow_two] using sourceReflection_sq Q split short (hK short) (μ short) (n short)

theorem sourceBorelWeyl_long_word (a : Fˣ) :
    (d).x 4 (a:F) * ((d).r*(d).x 4 (↑a⁻¹:F)*(d).r⁻¹) * (d).x 4 (a:F) = (d).torus (1,a)*(d).r := by
  change _ = alignedPairTorus Q split hK μ n short hH (1,a) * (n (1-short)).val
  rw [alignedPairTorus_long]
  exact aligned_rankOne_word Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a

theorem sourceBorelWeyl_short_word (a : Fˣ) :
    (d).x 5 (a:F) * ((d).s*(d).x 5 (↑a⁻¹:F)*(d).s⁻¹) * (d).x 5 (a:F) = (d).torus (a,a⁻¹)*(d).s := by
  change _ = alignedPairTorus Q split hK μ n short hH (a,a⁻¹) * (n short).val
  rw [alignedPairTorus_short]
  exact aligned_rankOne_word Q split short (hK short) (μ short) (n short) a

include hK μ in
private theorem reflection_inv (i : Fin 2) : ((n i).val : X ⧸ Q.D)⁻¹ = (n i).val :=
  inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split i (hK i) (μ i) (n i))

theorem sourceBorelWeyl_rA (a : F) : (d).r*(d).x 0 a*(d).r⁻¹ = (d).x 1 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [mul_inv_rev,inv_inv]
  group

theorem sourceBorelWeyl_rB (a : F) : (d).r*(d).x 1 a*(d).r⁻¹ = (d).x 0 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [mul_inv_rev,reflection_inv Q split hK μ n]
  group

theorem sourceBorelWeyl_rD (a : F) : (d).r*(d).x 3 a*(d).r⁻¹ = (d).x 5 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [inv_inv]
  group

theorem sourceBorelWeyl_rF (a : F) : (d).r*(d).x 5 a*(d).r⁻¹ = (d).x 3 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [reflection_inv Q split hK μ n]

theorem sourceBorelWeyl_sB (a : F) : (d).s*(d).x 1 a*(d).s⁻¹ = (d).x 4 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [inv_inv]
  group

theorem sourceBorelWeyl_sE (a : F) : (d).s*(d).x 4 a*(d).s⁻¹ = (d).x 1 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [reflection_inv Q split hK μ n]

theorem sourceBorelWeyl_sC (a : F) : (d).s*(d).x 2 a*(d).s⁻¹ = (d).x 3 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [mul_inv_rev,inv_inv]
  group

theorem sourceBorelWeyl_sD (a : F) : (d).s*(d).x 3 a*(d).s⁻¹ = (d).x 2 a := by
  dsimp [sourceBorelWeyl,PositiveRoots.x,alignedSourceRoots,alignedConjugateParameter]
  simp only [mul_inv_rev,reflection_inv Q split hK μ n]
  group

/-- Normal generation in the source supplies the consumer's actual generator closure. -/
theorem sourceBorelWeyl_whole (hm : rotationOrder Q = 6)
    (hgen : split.unipotentClosure = ⊤) : (d).whole = ⊤ := by
  apply top_unique
  rw [← hgen, ← RootGeneration.weylRootSpan_eq_unipotentClosure Q split]
  apply UnitarySource.weylRootSpan_le_of_unipotent_and_lifts Q split
    (fun i => (n i).val) (fun i => (n i).class_eq) (d).whole
  · rw [← sourceBorelWeyl_positive Q split hK μ n short hH hm]
    intro x hx
    exact subset_closure (Or.inl (mem_sup_left hx))
  · intro i
    have hi : i = short ∨ i = 1-short := by fin_cases i <;> fin_cases short <;> decide
    rcases hi with rfl | rfl
    · exact subset_closure (Or.inr (by simp [sourceBorelWeyl]))
    · exact subset_closure (Or.inr (by simp [sourceBorelWeyl]))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
