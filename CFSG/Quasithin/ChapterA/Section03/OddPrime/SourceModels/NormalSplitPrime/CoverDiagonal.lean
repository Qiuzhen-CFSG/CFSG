module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverStructure
public import Theory.SpecificGroups.SU3.OddPrimeDiagonal
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage

/-!
# Actual diagonal markings on odd prime-field cubic covers

The existing projective automorphism theorems put the square of an
odd-prime-field automorphism in the inner-diagonal image. A cubic actor
is the square of its square, so it has a genuine general linear or unitary
implementer. Faithfulness of the action on the central quotient lifts this
identity to the whole perfect cover. In the unitary case a Hermitian basis
change retains the original quadratic coefficient field and involution.

The original split-prime domain now has its exact star quotient and
residual product, and the cover marking is diagonal whenever its parameter
is an odd prime. Binary cover actions, the Singer centralizer and
outside-subgroup conjugacy remain source obligations.

Source: Aschbacher–Smith A.3.18, printed pp.51–53; GLS3 Theorem 2.5.12.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverDiagonal
section Models
variable {L : Type*} [Group L] [IsQuasisimple L]

/-- Cubic automorphisms of an odd prime-field SL₃ cover have an actual GL₃ marking. -/
theorem linear_odd {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : IsSL L 3 q) (α : MulAut L) (hα : α ^ 3 = 1) :
    IsLinearDiagonal L q α := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsQuasisimple SL(3,F) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup PSL(3,F) := IsQuasisimple.simple
  let α' : MulAut SL(3,F) := MulAut.congr e α
  let β := Matrix.PSL3.OuterSolvable.centerAction F α'
  have hβ : β ^ 3 = 1 := by
    rw [← map_pow,show α' ^ 3 = 1 from by change (MulAut.congr _ α)^3=1; rw [←map_pow,hα,map_one],map_one]
  have hb : β ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F := by
    have hs := (Matrix.PSL3.OuterSolvable.innerDiagonal F).pow_mem
      (Matrix.PSL3.OuterSolvable.OddPrimeSquares.square_mem_innerDiagonal
        (Group.IsPerfect.not_isSolvable PSL(3,F)) hq ho hF β) 2
    have he : (β^2)^2 = β := by
      rw [← pow_mul,show 2*2=3+1 from rfl,pow_succ,hβ,one_mul]
    exact he ▸ hs
  obtain ⟨g,hg⟩ := hb
  have hg' : Matrix.PSL3.OuterSolvable.linearConjSL F g = α' :=
    Matrix.PSL3.CartanActions.ActorCoverage.centerAction_injective F hg
  refine ⟨F,inferInstance,inferInstance,hF,e,g,?_⟩
  intro l
  have hh := Matrix.PSL3.OuterSolvable.linearConjSL_toGL F g (e l)
  rw [hg'] at hh
  simpa only [α',MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply] using hh

open HermitianForm HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport

private def specialConj {F : Type*} [Field F] (J : HermitianForm 3 F)
    (u : J.unitarySubgroup) : MulAut J.specialSubgroup where
  toFun := J.specialUnitaryConj u
  invFun := J.specialUnitaryConj u⁻¹
  left_inv x := by apply Subtype.ext; simp [J.specialUnitaryConj_val,mul_assoc]
  right_inv x := by apply Subtype.ext; simp [J.specialUnitaryConj_val,mul_assoc]
  map_mul' x y := by apply Subtype.ext; simp [J.specialUnitaryConj_val,mul_assoc]

/-- Cubic automorphisms of an odd prime-field SU₃ cover have an actual unitary marking. -/
theorem unitary_odd {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : IsSU L 3 q) (α : MulAut L) (hα : α ^ 3 = 1) :
    IsUnitaryDiagonal L q α := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : Fact q.Prime := ⟨hq⟩
  have hfixed : Nat.card {x : F // J.conj x=x} = q := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius J.conj q 1
      (by decide) (by simpa only [pow_one] using hF) (by simpa only [pow_one] using hconj)
  obtain ⟨C,hC⟩ := exists_standard_basis J q hF hfixed
  let J₀ := standardForm J
  let e' : L ≃* J₀.specialSubgroup := e.trans (specialEquiv J C hC)
  let : IsQuasisimple J₀.specialSubgroup := IsQuasisimple.of_mulEquiv e'
  have hlarge : 2 < q := by have := hq.two_le; have := Nat.odd_iff.mp ho; omega
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    BenderSuzuki.External.huppert_II_10_13 J₀ q hlarge hF hfixed
  let := J₀.projective_isPerfect_of_fixed_card hlarge hF hfixed
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J₀) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J₀)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  let E : (J₀.specialSubgroup ⧸ center J₀.specialSubgroup) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J₀ :=
    (QuotientGroup.quotientMulEquivOfEq (J₀.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J₀.specialToProjective J₀.specialToProjective_surjective)
  have hE (x : J₀.specialSubgroup) : E (QuotientGroup.mk' (center J₀.specialSubgroup) x) =
      J₀.specialToProjective x := rfl
  let α' := MulAut.congr e' α
  let β := MulAut.centralQuotientAction E α'
  have hβ : β ^ 3 = 1 := by
    rw [← map_pow,show α' ^ 3 = 1 from by change (MulAut.congr _ α)^3=1; rw [←map_pow,hα,map_one],map_one]
  obtain ⟨u,hu⟩ := J₀.cubic_mem_unitary_of_odd_prime rfl hq ho hF hfixed β hβ
  have hquot : MulAut.centralQuotientAction E (specialConj J₀ u) = J₀.unitaryConjHom u := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y,rfl⟩ := J₀.specialToProjective_surjective x
    rw [←hE y,MulAut.centralQuotientAction_apply,hE,hE,J₀.unitaryConjHom_apply,
      J₀.unitaryConj_specialToProjective]
    rfl
  have he : α' = specialConj J₀ u :=
    MulAut.centralQuotientAction_injective E (hu.symm.trans hquot.symm)
  refine ⟨F,inferInstance,inferInstance,J₀,hF,hconj,e',u,?_⟩
  intro l
  have hh := congrArg (fun b : MulAut J₀.specialSubgroup => (b (e' l)).val) he
  change (e' (α (e'.symm (e' l)))).val = (J₀.specialUnitaryConj u (e' l)).val at hh
  rw [J₀.specialUnitaryConj_val,e'.symm_apply_apply] at hh
  exact hh

end Models

variable {G : Type*} [Group G] [Finite G]

/-- The complete elementary splitting clauses, with a diagonal marking
unless the actual cover parameter is a power of two. -/
structure MarkedStarCover (K : Subgroup G) (a : G) : Prop extends
    CoverStructure.StarCover K a where
  marking : ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
    IsSLSign (starComponent 3 K) unitary 3 q ∧
    ∃ α : MulAut (starComponent 3 K),
      (∀ l : starComponent 3 K, (α l).val = starMap 3 G a * l.val * (starMap 3 G a)⁻¹) ∧
      α ∉ MulAut.innerSubgroup (starComponent 3 K) ∧
      ((∃ n : ℕ, 1 ≤ n ∧ q = 2 ^ n) ∨ IsDiagonalSign (starComponent 3 K) unitary q α)

omit [Finite G] in
/-- The same original actor acquires a matrix marking on every odd-prime
cover row; the whole central three-cover is retained. -/
theorem marked_star_cover {K : Subgroup G} [K.Normal] (a : G)
    (hs : CoverStructure.StarCover K a) : MarkedStarCover K a := by
  let : (starComponent 3 K).Normal :=
    (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective _)
  let := hs.quasisimple
  obtain ⟨_,u,q,hq,hm,α,ha,ho⟩ := hs.outer
  have he : α = (MulAut.conjNormal (starMap 3 G a) : MulAut (starComponent 3 K)) := by
    apply MulEquiv.ext
    intro l
    exact Subtype.ext (ha l)
  have hc : α ^ 3 = 1 := by
    have hp : starMap 3 G a ^ 3 = 1 := by
      simpa only [hs.order] using pow_orderOf_eq_one (starMap 3 G a)
    rw [he,←map_pow,hp,map_one]
  refine ⟨hs,u,q,hq,hm,α,ha,ho,?_⟩
  rcases hq with ⟨n,hn,hq,_⟩ | ⟨hp,hodd⟩
  · exact Or.inl ⟨n,hn,hq⟩
  · right
    cases u with
    | false => exact linear_odd hp hodd hm α hc
    | true => exact unitary_odd hp hodd hm α hc

/-- Apply the literal star-cover and odd diagonal calculations on the
universal normal split-prime domain. The remaining source clauses are explicit. -/
theorem alternatives_or_marked_star_cover
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {K : Subgroup G} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : G) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ (p = 3 ∧ MarkedStarCover K a) := by
  rcases CoverStructure.alternatives_or_star_cover hG hK hp ho hr a ha haK hgen with halt | ⟨rfl,hs⟩
  · exact Or.inl halt
  · exact Or.inr ⟨rfl,marked_star_cover a hs⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverDiagonal
