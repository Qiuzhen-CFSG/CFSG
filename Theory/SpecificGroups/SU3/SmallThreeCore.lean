module
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.GroupAction.SolvablePrimitiveRegular
public import Theory.ElementaryAbelian.Injective
public import Theory.PGroupCore

/-!
# The three-core of the degree-one projective unitary group

The genuine action on nine isotropic points is faithful and doubly transitive.
Solvability gives a characteristic regular abelian subgroup, and double
transitivity makes it elementary. Its order nine and index eight identify it
with O₃(PSU₃(2)); regularity identifies its full centralizer. A Hermitian
basis change transports the result to every stored form.

This is the projective input to the small special-unitary scalar-cover and
Borel-core action calculation. Source: DGS, Groups and Graphs (1985), p.104
(the 3-closed small unitary groups) and 6.1, pp.118--119; Huppert II.10.12
for the literal isotropic-point action.
-/

public noncomputable section
open Subgroup MulAction BenderSuzuki.External
open scoped LinearAlgebra.Projectivization IsMulCommutative
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private abbrev Points := {x : Projectivization F (Fin 3 → F) // x ∈
  {x | ∃ (v : Fin 3 → F) (hv : v ≠ 0), x = Projectivization.mk F v hv ∧
    dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}

private theorem standard_core
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2) :
    Nat.card (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) = 9 ∧
    IsElementaryAbelian 3 (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
    centralizer (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) : Set _) =
      pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf : Nat.card {x : F // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hc) (by simpa using hconj)
  obtain ⟨hX,rho,o,hi,_,_,_,ht,_⟩ := huppert_II_10_12 J 2 hc hf hJ
  let D : Type _ := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [FixedFieldTwo.card_projective J hc hconj]; decide)
  let : Finite (Points J) := Nat.finite_of_card_ne_zero (by change Nat.card (Points J) = 9 at hX; omega)
  let : Nontrivial (Points J) := Finite.one_lt_card_iff_nontrivial.mp (by
    change Nat.card (Points J) = 9 at hX; omega)
  let : MulAction D (Points J) := MulAction.compHom _ rho
  let : FaithfulSMul D (Points J) := ⟨fun {g h} he => hi (Equiv.ext he)⟩
  have ht' : IsMultiplyPretransitive D (Points J) 2 := is_two_pretransitive_iff.mpr (fun {a b c d} => ht a b c d)
  let : IsPreprimitive D (Points J) := isPreprimitive_of_is_two_pretransitive ht'
  let : Group.IsSolvable D := FixedFieldTwo.projective_isSolvable J hc hconj
  obtain ⟨A,hAchar,hAb,hA,hr,hself⟩ := exists_characteristic_abelian_regular (G := D) (X := Points J) o
  let := hAchar
  let := hAb
  have hbij : Function.Bijective (fun a : A => (a : D) • o) := by
    refine ⟨?_,fun y => (hr o y).exists⟩
    intro a b he
    obtain ⟨c,_,hu⟩ := hr o ((a : D) • o)
    exact (hu a rfl).trans (hu b he.symm).symm
  have hAc : Nat.card A = 9 := (Nat.card_congr (Equiv.ofBijective _ hbij)).trans hX
  obtain ⟨p,hp,he⟩ := regular_normal_elementaryAbelian ht' o A inferInstance hA hr
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hp3 : p = 3 := by
    have hd : p ∣ Nat.card A := (IsElementaryAbelian.isPGroup p A).card_eq_or_dvd.resolve_left (by omega)
    rw [hAc,show 9 = 3^2 by decide] at hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)
  have he3 : IsElementaryAbelian 3 A := hp3 ▸ he
  let := he3
  have hiA : A.index = 8 := by
    have hh := A.card_mul_index
    rw [hAc,FixedFieldTwo.card_projective J hc hconj] at hh
    omega
  let T : Sylow 3 D := (IsElementaryAbelian.isPGroup 3 A).toSylow (by rw [hiA]; decide)
  have heA : pCore 3 D = A := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal T)
    (le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 3 A⟩)
  change Nat.card (pCore 3 D) = 9 ∧ IsElementaryAbelian 3 (pCore 3 D) ∧
    centralizer (pCore 3 D : Set D) = pCore 3 D
  rw [heA]
  exact ⟨hAc,he3,hself⟩

/-- The actual PSU₃(2) three-core is a self-centralizing elementary group of order nine, for any Hermitian form. -/
theorem projective_core_structure
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2) :
    Nat.card (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) = 9 ∧
    IsElementaryAbelian 3 (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
    centralizer (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) : Set _) =
      pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf : Nat.card {x : F // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hc) (by simpa using hconj)
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J 2 hc hf
  obtain ⟨hN,hE,hC⟩ := standard_core J₀ rfl hc hconj
  let := hE
  let N := pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)
  let N₀ := pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J₀)
  have hm : N.map e.toMonoidHom = N₀ := pCore_map_iso 3 e
  let f : N ≃* N₀ := (N.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hm)
  have hEN : IsElementaryAbelian 3 N := IsElementaryAbelian.of_injective f.toMonoidHom f.injective
  let : IsMulCommutative (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) := hEN.toIsMulCommutative
  refine ⟨(Nat.card_congr f.toEquiv).trans hN,hEN,le_antisymm ?_ ?_⟩
  · intro x hx
    have he : e x ∈ centralizer (N₀ : Set _) := by
      rintro y hy
      rw [←hm] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      exact (map_mul e z x).symm.trans ((congrArg e (hx z hz)).trans (map_mul e x z))
    rw [hC] at he
    change e x ∈ N₀ at he
    rw [←hm] at he
    obtain ⟨y,hy,hh⟩ := he
    exact e.injective hh ▸ hy
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

private theorem aut_eq_one_of_selfcentralizing_complement
    {D : Type*} [Group D] (N T : Subgroup D) [N.Normal]
    (hc : centralizer (N : Set D) ≤ N) (hgen : N ⊔ T = ⊤) (hd : Disjoint N T)
    (a : MulAut D) (hT : T.map a.toMonoidHom = T)
    (hfix : ∀ n ∈ N, a n = n) : a = 1 := by
  have hfixT (s : D) (hs : s ∈ T) : a s = s := by
    have hdisp : s⁻¹*a s ∈ centralizer (N : Set D) := by
      intro n hn
      have he := hfix (s*n*s⁻¹) ((inferInstance : N.Normal).conj_mem n hn s)
      rw [map_mul,map_mul,map_inv,hfix n hn] at he
      calc
        n*(s⁻¹*a s) = s⁻¹*(s*n*s⁻¹)*a s := by group
        _ = s⁻¹*(a s*n*(a s)⁻¹)*a s := congrArg (fun x : D => s⁻¹*x*a s) he.symm
        _ = (s⁻¹*a s)*n := by group
    have haT : a s ∈ T := hT ▸ mem_map_of_mem a.toMonoidHom hs
    have he : s⁻¹*a s = 1 := mem_bot.mp (hd.le_bot
      ⟨hc hdisp,T.mul_mem (T.inv_mem hs) haT⟩)
    exact (inv_mul_eq_one.mp he).symm
  have he : N ⊔ T ≤ a.toMonoidHom.eqLocus (MonoidHom.id D) := sup_le hfix hfixT
  exact MulEquiv.ext fun x => he (hgen ▸ mem_top x)

/-- On PSU₃(2), an automorphism preserving a Sylow two-subgroup is detected faithfully on the characteristic elementary nine. -/
theorem projective_aut_eq_one_of_core_and_sylow
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hfix : ∀ n ∈ pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J), a n = n) : a = 1 := by
  let D : Type _ := ProjectiveSpecialUnitaryMatrixGroup J
  let N := pCore 3 D
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [FixedFieldTwo.card_projective J hc hconj]; decide)
  obtain ⟨hN,_,hC⟩ := projective_core_structure J hc hconj
  have hSc : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,FixedFieldTwo.card_projective J hc hconj]
    decide +kernel
  have hcomp : N.IsComplement' (S : Subgroup D) := isComplement'_of_coprime
    (by rw [hN,hSc,FixedFieldTwo.card_projective J hc hconj])
    (by rw [hN,hSc]; decide)
  exact aut_eq_one_of_selfcentralizing_complement N S hC.le hcomp.sup_eq_top hcomp.disjoint a hS hfix
end BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
