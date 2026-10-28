module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedUnitaryFour
public import Theory.Mathieu.M22.CoverDegreeFive
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The odd four-dimensional models cannot contain a Mathieu cover

A full involution-fixed M₂₂ component lifts through the literal symplectic
or unitary projective map to a perfect central cover acting faithfully in
four dimensions. The native eleven-by-five Frobenius subgroup forces degree
at least five outside characteristic eleven. Sp₄(11) is excluded by its
order, while eleven is not a Mersenne prime. The comparison therefore
leaves only odd G₂ and McL, with the actual model isomorphisms retained.

Source: Aschbacher--Smith 4.2.13, printed p.612, Theorem B, p.33, and
H.12.1's native Frobenius subgroup, p.394. The literal Hall consumer is
MathieuGeneration.HallFaithfulness.OddModelResidue.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu ChapterA.Section02 BenderSuzuki.MatrixGroups

private theorem eleven_ne_zero_of_prime {F : Type*} [Field F] [Finite F]
    {p n : ℕ} [Fact p.Prime] (hc : Nat.card F = p ^ n) (hp : p ≠ 11) : (11 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact (CharP.cast_eq_zero_iff F p 11).not.mpr
    (fun hd => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_eleven).mp hd))

/-- No odd-prime projective symplectic four-space has a fixed M₂₂ cover. -/
theorem HasMathieuFixedComponent.not_odd_symplectic_four
    {S : Type*} [Group S] (h : HasMathieuFixedComponent S)
    {p : ℕ} (hp : p.Prime) (_ho : Odd p) (hm : ClassicalGroup.IsPSp S 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hm' := h.of_mulEquiv e
  by_cases h11 : p = 11
  · have hd := hm'.card_dvd.trans (card_quotient_dvd_card
      (center (Matrix.symplecticGroup (Fin 2) F)))
    rw [Theory.SpecificGroups.SymplecticFour.card_sp,hF,h11] at hd
    norm_num at hd
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := hm'
  let := hB.quasisimple
  let j : (Matrix.symplecticGroup (Fin 2) F) →*
      Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F := {
    toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.prop)
    map_one' := by apply Units.ext; rfl
    map_mul' _ _ := by apply Units.ext; rfl }
  have hj : Function.Injective j := fun _ _ he => Subtype.ext (congrArg Units.val he)
  let ρ : Representation F (Matrix.symplecticGroup (Fin 2) F) ((Fin 2 ⊕ Fin 2) → F) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom _).comp j)
  have hi : Function.Injective ρ := Matrix.toLinAlgEquiv'.injective.comp
    (Units.val_injective.comp hj)
  have hd := M22CentralCover.faithful_degree_ge_five_of_central_image
    (QuotientGroup.mk' (center (Matrix.symplecticGroup (Fin 2) F)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) B b ρ hi
    (eleven_ne_zero_of_prime (n := 1) (by simpa only [pow_one] using hF) h11)
  norm_num [Module.finrank_fin_fun,Module.finrank_pi] at hd

private theorem mersenne_ne_eleven {p : ℕ} (hp : ∃ b : ℕ, p + 1 = 2 ^ b) : p ≠ 11 := by
  rintro rfl
  obtain ⟨b,hb⟩ := hp
  by_cases hsmall : b < 4
  · interval_cases b <;> norm_num at hb
  · have hh : 16 ≤ 2 ^ b := show 2 ^ 4 ≤ 2 ^ b from Nat.pow_le_pow_right (by decide) (by omega : 4 ≤ b)
    omega

/-- No Mersenne-prime projective unitary four-space has a fixed M₂₂ cover. -/
theorem HasMathieuFixedComponent.not_mersenne_unitary_four
    {S : Type*} [Group S] (h : HasMathieuFixedComponent S)
    {p : ℕ} (hp : p.Prime) (hmer : ∃ b : ℕ, p + 1 = 2 ^ b)
    (hm : ClassicalGroup.IsPSU S 4 p) : False := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let := hB.quasisimple
  let q := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project F J
  have hq := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective F J
  have hk : q.ker ≤ center J.specialSubgroup := by
    intro x hx
    have hz : x.val ∈ center (Matrix.GeneralLinearGroup (Fin 4) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hz y.val)
  let ρ : Representation F J.specialSubgroup (Fin 4 → F) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom _).comp J.specialSubgroup.subtype)
  have hi : Function.Injective ρ := Matrix.toLinAlgEquiv'.injective.comp
    (Units.val_injective.comp J.specialSubgroup.subtype_injective)
  have hd := M22CentralCover.faithful_degree_ge_five_of_central_image q hq hk B b ρ hi
    (eleven_ne_zero_of_prime hF (mersenne_ne_eleven hmer))
  norm_num [Module.finrank_fin_fun] at hd

/-- The two remaining nontrivial-involution models, with their actual carriers. -/
@[expose] def RemainingMathieuG2McLModel (S : Type*) [Group S] : Prop :=
  (∃ p, p.Prime ∧ Odd p ∧ ClassificationModels.IsG2At S p) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- The full fixed Mathieu cover excludes both remaining odd classical rows. -/
theorem HasMathieuFixedComponent.g2_mcl_model_rows
    {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBModel S) :
    RemainingMathieuG2McLModel S := by
  rcases h.odd_sporadic_model_rows hm with ho | hmc
  · rcases ho with ⟨p,hp,ho,he⟩ | hg | ⟨p,hp,hmer,he⟩
    · exact (h.not_odd_symplectic_four hp ho he).elim
    · exact Or.inl hg
    · exact (h.not_mersenne_unitary_four hp hmer he).elim
  · exact Or.inr hmc

end CFSG.Quasithin.ChapterI.MathieuPumpup
