module

public import Theory.SpecificGroups.PSL2.OddSquareFieldFixedIndex
public import Theory.SpecificGroups.PSL2.QuadraticNonsolvableSylowOvergroups
public import Theory.FieldTheory.QuadraticFrobenius
public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# Sylow-normalized alternating five subgroups of prime PGL₂

PGL₂(p) embeds with odd index in PSL₂(p²), as the fixed subgroup of the
coefficient involution. Thus a full Sylow two-subgroup normalizing A₅ gives
a proper nonsolvable Sylow overgroup in the quadratic group. Dickson's
classification identifies its simple normal A₅ with PSL₂(p), forcing p = 5.

Source: Huppert II.8.27; the prime linear centralizer step in
Aschbacher–Smith C.5.8, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup GorensteinWalter BenderSuzuki.MatrixGroups
namespace Theory.PSL2

/-- The prime projective general linear group has a proper odd-index
embedding in the quadratic projective special linear group. -/
theorem pgl2_exists_quadratic_odd_index_embedding
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p) :
    ∃ f : PGL2 F →* PSL2MatrixGroup (GaloisField p 2),
      Function.Injective f ∧ Odd f.range.index ∧ f.range ≠ ⊤ := by
  let E := GaloisField p 2
  have hE : Nat.card E = p ^ 2 := GaloisField.card p 2 (by decide)
  let σ : E ≃+* E := frobeniusEquiv E p
  have hσ : orderOf σ = 2 := FiniteField.frobeniusEquiv_orderOf_of_card hE
  let K := FixedPoints.subfield (zpowers σ) E
  let P := (psl2FieldAut E σ).fixedSubgroup
  have hK : Nat.card K = p := OddSquareFieldFixed.fixed_subfield_card hE σ hσ
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  let eK : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hF.trans hK.symm)
  obtain ⟨d⟩ := OddSquareFieldFixed.coefficient_fixed_equiv ho hE σ hσ
  let e : PGL2 F ≃* P := (pgl2RingEquiv eK).trans d.symm
  let f : PGL2 F →* PSL2MatrixGroup E := P.subtype.comp e.toMonoidHom
  have hr : f.range = P := by
    rw [MonoidHom.range_comp, e.toMonoidHom.range_eq_top_of_surjective e.surjective,
      ← MonoidHom.range_eq_map, P.range_subtype]
  obtain ⟨hi, hn, _⟩ :=
    OddSquareFieldFixed.coefficient_fixed_odd_index_nonsolvable ho hp hE σ hσ
  exact ⟨f, P.subtype_injective.comp e.injective, hr ▸ hi, hr ▸ hn⟩

/-- An A₅ subgroup normalized by a full Sylow two-subgroup of PGL₂(p)
can occur only over the prime field of order five. -/
theorem pgl2_prime_eq_five_of_sylow_normalizes_alternating_five
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (S : Sylow 2 (PGL2 F)) (B : Subgroup (PGL2 F))
    (hB : Nonempty (B ≃* alternatingGroup (Fin 5)))
    (hSB : (S : Subgroup _) ≤ normalizer (B : Set (PGL2 F))) : p = 5 := by
  let : Finite (PGL2 F) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨eB⟩ := hB
  have hBcard : Nat.card B = 60 := by
    rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hp : 3 < p := by
    have hd := B.card_subgroup_dvd_card
    rw [hBcard, pgl2_card_formula, hF] at hd
    have hp2 := (Fact.out : p.Prime).two_le
    have hpne2 : p ≠ 2 := by
      intro he
      exact ho.not_two_dvd_nat (he ▸ dvd_rfl)
    by_contra hh
    have he : p = 3 := by omega
    norm_num [he] at hd
  obtain ⟨f, hf, hi, hn⟩ := pgl2_exists_quadratic_odd_index_embedding ho hp hF
  let A := B.map f
  let T := (S : Subgroup (PGL2 F)).map f
  have hTp : IsPGroup 2 T := S.isPGroup'.map f
  have hTi : ¬ 2 ∣ T.index := by
    rw [show T = (S : Subgroup (PGL2 F)).map f from rfl,
      (S : Subgroup (PGL2 F)).index_map_of_injective hf]
    exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index hi.not_two_dvd_nat
  let R : Sylow 2 (PSL2MatrixGroup (GaloisField p 2)) := hTp.toSylow hTi
  let H := A ⊔ T
  have hHA : H ≤ normalizer (A : Set _) :=
    sup_le A.le_normalizer ((map_mono hSB).trans (B.le_normalizer_map f))
  let C := A.subgroupOf H
  have hCH : C.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHA
  let eA : A ≃* alternatingGroup (Fin 5) := (B.equivMapOfInjective f hf).symm.trans eB
  let eC : C ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).trans eA
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup C := eC.isSimpleGroup
  let : Group.IsPerfect C :=
    Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
  have hc : C.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect hCH.isSubnormal
  have hHne : H ≠ ⊤ := by
    intro he
    apply hn
    apply top_unique
    rw [← he]
    exact sup_le (map_le_range _ _) (map_le_range _ _)
  have hHns : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable C inferInstance
  have hm := quadratic_nonsolvable_proper_sylow_models ho
    (GaloisField.card p 2 (by decide)) R H le_sup_right hHne hHns
  obtain ⟨_, ⟨d⟩⟩ := cComponent_prime_linear_model ho C hc hm
  have hcard : Nat.card (PSL2MatrixGroup (GaloisField p 1)) = 60 := by
    rw [← Nat.card_congr d.toEquiv, Nat.card_congr eC.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hfield : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 (by decide)
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := GaloisField p 1) (hfield.symm ▸ ho)
  rw [hfield, hcard] at horder
  have hp5 : p ≤ 5 := by
    by_contra hh
    have hh : 6 ≤ p := by omega
    have hs : 35 ≤ p ^ 2 - 1 := by
      have : 36 ≤ p ^ 2 := by nlinarith
      omega
    nlinarith
  have hpne4 : p ≠ 4 := by
    intro he
    have ht := Fact.out (p := p.Prime)
    norm_num [he] at ht
  omega

end Theory.PSL2
