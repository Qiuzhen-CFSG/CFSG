module
public import Theory.SpecificGroups.SU3.OrdinaryThompson
public import BenderSuzuki.External.Huppert.II.theorem_10_13

/-!
# Transporting the unitary Borel geometry to the original Sylow intersection

A Hermitian basis change and Sylow conjugacy align S∩L with the concrete
root group. The fixed-field torus subgroup then transports back inside
the literal normalizer N_L(S∩L), preserving two-perfectness, Thompson
normalization and the centralizer comparison. This packages the matrix
transport independently of the source component data.
Source: Aschbacher--Smith 15.1.21(iii), printed pp.1097--1098.
-/

public section
open Subgroup BenderSuzuki.External Stellmacher
namespace BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel
open BorelTorus
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- Every marked binary unitary Sylow intersection has a two-perfect Borel
subgroup normalizing the original Thompson subgroup and detecting its centralizer. -/
theorem exists_thompson_borel_subgroup
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2≤n)
    (hF : Nat.card F=(2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n))
    (L S : Subgroup G) (hSL : S ≤ normalizer (L:Set G))
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 L) (hSP : S.subgroupOf L=(P:Subgroup L)) :
    ∃ B : Subgroup G, B ≤ (normalizer (P:Set L)).map L.subtype ∧
      IsPPerfect 2 B ∧ B ≤ normalizer (elementaryAbelianMaxJ S : Set G) ∧
      S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hF)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
  obtain ⟨eJ⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hF hf
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  have hJ₀ : J₀.form = !![0,0,1;0,1,0;1,0,0] := rfl
  let e₀ := e.trans eJ
  have hc₀ : ∀ x, J₀.conj x=x^(2^n) := hconj
  have hf₀ : Nat.card {x : F // J₀.conj x=x}=2^n := hf
  have hq : 2<2^n := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    BenderSuzuki.External.huppert_II_10_13 J₀ (2^n) hq hF hf₀
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective J₀.specialToProjective J₀.specialToProjective_surjective
  let R := P.mapSurjective (f:=e₀.toMonoidHom) e₀.surjective
  let U := EvenTwoRank.rootSylow J₀ hJ₀ (by omega : 0<n) hF hf₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J₀) R U
  let e₁ := e₀.trans (MulAut.conj g)
  have hroot : (S.subgroupOf L).map e₁.toMonoidHom=projectiveRoot J₀ hJ₀ := by
    change (S.subgroupOf L).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom)=_
    rw [←map_map,hSP]
    exact congrArg Sylow.toSubgroup hg
  let D := rootFixedTorus J₀ hJ₀
  let B := (D.map e₁.symm.toMonoidHom).map L.subtype
  refine ⟨B,?_,?_,?_,?_⟩
  · have hDN : D ≤ normalizer (projectiveRoot J₀ hJ₀ : Set _) := by
      apply sup_le (projectiveRoot J₀ hJ₀).le_normalizer
      rintro _ ⟨k,rfl⟩
      exact BorelCoprimeFieldAction.torus_normalizes_root J₀ hJ₀ ⟨fixedUnit J₀ k,rfl⟩
    have hback : (projectiveRoot J₀ hJ₀).map e₁.symm.toMonoidHom= (P : Subgroup L) := by
      rw [←hroot,map_map]
      have hi : e₁.symm.toMonoidHom.comp e₁.toMonoidHom=MonoidHom.id L := MonoidHom.ext (fun x => e₁.symm_apply_apply x)
      rw [hi,map_id]
      exact hSP
    have hnorm := map_mono (f:=e₁.symm.toMonoidHom) hDN
    rw [map_equiv_normalizer_eq,hback] at hnorm
    exact map_mono hnorm
  · have hD : IsPPerfect 2 D := rootFixedTorus_twoPerfect J₀ hJ₀ hn hF hf₀
    have hD' := hD.of_surjective (e₁.symm.toMonoidHom.subgroupMap D)
      (e₁.symm.toMonoidHom.subgroupMap_surjective D)
    exact hD'.of_surjective (L.subtype.subgroupMap _) (L.subtype.subgroupMap_surjective _)
  · exact rootFixedTorus_normalizes_thompson J₀ hJ₀ hn hF hc₀ L S hSL e₁ hroot
  · exact rootFixedTorus_centralizers J₀ hJ₀ hn hF hc₀ L S hSL e₁
end BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel
