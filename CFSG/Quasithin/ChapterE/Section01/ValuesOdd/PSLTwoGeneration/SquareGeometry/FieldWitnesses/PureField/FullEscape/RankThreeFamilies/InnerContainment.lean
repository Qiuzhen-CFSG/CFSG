module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.FieldCentralizer
public import GorensteinWalter.PGammaL2OuterAbelian
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Rank-three actors lie in the canonical inner extension

Every rank-three elementary actor maps onto the quadratic field factor.
Choose a field involution in it and straighten that involution by projective
Hilbert--90. Fixed-field descent puts its entire centralizer in
`PSL₂(F)⟨σ⟩`: the marked subfield PGL₂ embeds in the ambient PSL₂.
The outer quotient is abelian, so the inner extension is normal and the
original actor lies there too. No conjugacy class is substituted for an
arbitrary invariant family.

The outer product quotient also shows that every ambient Sylow supplements
this normal subgroup. `RankThreeFamilies` uses both facts to restrict the
whole source family and lift escaping E-members. The argument includes
characteristics three and five.

Source: Aschbacher--Smith, A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209--210 and 214; projective involution descent is proved in
`GorensteinWalter.PGammaL2PureSemilinear`.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies
variable {F : Type*} [Field F] [Finite F]

/-- The canonical inner extension is normal in the full semilinear group. -/
theorem innerModel_normal {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) :
    (innerModel F σ).Normal :=
  Subgroup.Normal.of_commutator_le _
    ((pGammaL2_commutator_le_psl_range F ⟨p, 2, hp, hodd, by decide, hF⟩).trans
      le_sup_left)

/-- Every Sylow two-subgroup supplements the canonical inner extension. -/
theorem sylow_sup_innerModel {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) [Finite (PGammaL2 F)]
    (T : Sylow 2 (PGammaL2 F)) :
    (T : Subgroup (PGammaL2 F)) ⊔ innerModel F σ = ⊤ := by
  let : Fact (IsOddPrimePower (Nat.card F)) := ⟨⟨p, 2, hp, hodd, by decide, hF⟩⟩
  let f := pGammaL2OuterProduct F
  have hc : Nat.card (PGammaL2 F ⧸ f.ker) = 4 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (pGammaL2OuterProduct_surjective F)).toEquiv, Nat.card_prod]
    rw [FiniteField.card_ringAut_of_card_prime_pow hp hF]
    have hlinear : Nat.card (PGL2 F ⧸
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) = 2 :=
      pgl2_psl2Range_index_eq_two F Fact.out
    rw [hlinear]
  have htwo : IsPGroup 2 (PGammaL2 F ⧸ f.ker) :=
    IsPGroup.of_card (n := 2) (by simpa using hc)
  apply top_unique
  rw [← T.sup_eq_top_of_quotient_isPGroup f.ker htwo]
  apply sup_le_sup_left
  rw [show f.ker = pGammaL2PSLRange F from pGammaL2OuterProduct_ker F]
  exact le_sup_left

/-- The literal pure-field centralizer lies in the canonical inner extension. -/
theorem pureCentralizer_le_innerModel {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1) :
    centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) ≤ innerModel F σ := by
  intro x hx
  obtain ⟨y, hy⟩ := (mem_fieldCentralizer_iff hp hF σ hne x).mp hx
  have hl : SemidirectProduct.inl x.left ∈ pGammaL2PSLRange F := by
    rw [← hy]
    exact subfieldEmbedding_range_le_psl hodd hF σ hsq hne ⟨y, rfl⟩
  have hr : SemidirectProduct.inr x.right ∈ zpowers (SemidirectProduct.inr σ : PGammaL2 F) := by
    rcases fieldAut_eq_one_or hp hF σ hne x.right with h | h
    · rw [h, map_one]; exact one_mem _
    · rw [h]; exact mem_zpowers _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact mul_mem_sup hl hr

/-- Every rank-three elementary actor lies in the same canonical inner extension,
including actors not originally containing the chosen pure field involution. -/
theorem rank_three_le_innerModel {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hsq : σ ^ 2 = 1) (hne : σ ≠ 1)
    (S : Subgroup (PGammaL2 F)) [Finite S] (hS : pGammaL2PSLRange F ≤ S)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 3) :
    A.map S.subtype ≤ innerModel F σ := by
  let := hA
  let : (innerModel F σ).Normal := innerModel_normal hp hodd hF σ
  obtain ⟨x, hx⟩ := rank_three_fieldProjection_surjective hp hodd hF S hS A hA hr σ
  have hxf : (x.val : PGammaL2 F).right = σ := hx
  have hxn : (x.val : PGammaL2 F) ≠ 1 := by
    intro h
    exact hne (hxf.symm.trans (congrArg SemidirectProduct.right h))
  have hxo : orderOf (x.val : PGammaL2 F) = 2 := by
    apply (orderOf_eq_prime_iff (x := (x.val : PGammaL2 F))).mpr
    exact ⟨congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian
      (A := A) x.val x.property), hxn⟩
  obtain ⟨C, hC⟩ := projective_semilinear_involution_conj_inr
    ⟨p, 2, hp, hodd, by decide, hF⟩ (x.val : PGammaL2 F) hxo (hxf ▸ hne)
  let c : PGammaL2 F := SemidirectProduct.inl C
  let a := MulAut.conj c⁻¹
  have hxconj : a (x.val : PGammaL2 F) = SemidirectProduct.inr σ := by
    simpa [a, c, MulAut.conj_apply, hxf] using hC
  rintro b ⟨y, hy, rfl⟩
  have hyC : a (y : PGammaL2 F) ∈
      centralizer ({SemidirectProduct.inr σ} : Set (PGammaL2 F)) := by
    rw [mem_centralizer_singleton_iff, ← hxconj, ← map_mul, ← map_mul]
    congr 1
    exact congrArg (fun z : A => (z.val : PGammaL2 F))
      (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : A) x)
  have hyN := pureCentralizer_le_innerModel hp hodd hF σ hsq hne hyC
  have hconj := (inferInstance : (innerModel F σ).Normal).conj_mem
    (a (y : PGammaL2 F)) hyN c
  simpa [a, MulAut.conj_apply, mul_assoc] using hconj

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankThreeFamilies
