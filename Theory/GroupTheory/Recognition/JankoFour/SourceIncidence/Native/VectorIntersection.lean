module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneCardinality
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit.Generators
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry
/-!
# Sextet-vector detection in the original Todd module

The zero vector, 276 pair vectors and 1771 sextet vectors exhaust the
2048-element cocode, using the existing injectivity and minimum-distance
proofs. For every pair, one of the four already certified sextet permutations
moves it to a disjoint pair whose union is not a part of the fixed sextet.
The sum is therefore the vector of a different sextet. The 276-pair check
uses only those original permutations, with no new orbit enumeration; the
representative probe used 42.81 seconds including imports and 2,310,784 KiB.

This is the local calculation used to exclude non-marker elements from
nonadjacent point-radical intersections in AS91 (5.3)(2) and (6.2)(3).
The actual subgroup application is in `SourceIncidence.CoreIntersections`.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), pp.600–602; the native
Golay minimum-distance port retains its attribution in CocodeLocal.lean.
-/
public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeVectors
private noncomputable def parameter : Option (PointPair ⊕ Sextet) → Cocode
  | none => 0
  | some (.inl P) => pairVector P
  | some (.inr S) => sextetVector S

private theorem parameter_injective : Function.Injective parameter := by
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      cases b with
      | inl P => exact (pairVector_ne_zero P he.symm).elim
      | inr S => exact (sextetVector_ne_zero S he.symm).elim
  | some a =>
    cases b with
    | none =>
      cases a with
      | inl P => exact (pairVector_ne_zero P he).elim
      | inr S => exact (sextetVector_ne_zero S he).elim
    | some b =>
      cases a with
      | inl P =>
        cases b with
        | inl Q => exact congrArg (fun P => some (Sum.inl P)) (pairVector_injective he)
        | inr S => exact (pairVector_ne_sextetVector S P he).elim
      | inr S =>
        cases b with
        | inl P => exact (pairVector_ne_sextetVector S P he.symm).elim
        | inr T => exact congrArg (fun S => some (Sum.inr S)) (sextetVector_injective he)

private theorem parameter_surjective : Function.Surjective parameter := by
  apply (parameter_injective.bijective_of_nat_card_le ?_).2
  have hp : Nat.card PointPair = 276 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_finset_len]
    decide
  let : Fintype Sextet := Fintype.ofFinite _
  have ho : Nat.card (Option (PointPair ⊕ Sextet)) = Nat.card PointPair + Nat.card Sextet + 1 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_sum]
  rw [ho,hp,show Nat.card Sextet = 1771 from plane_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_cocode]
  norm_num

theorem cocode_cases (v : Cocode) : v = 0 ∨ (∃ P, v = pairVector P) ∨ ∃ S, v = sextetVector S := by
  obtain ⟨p,rfl⟩ := parameter_surjective v
  cases p with
  | none => exact Or.inl rfl
  | some p =>
    cases p with
    | inl P => exact Or.inr (Or.inl ⟨P,rfl⟩)
    | inr S => exact Or.inr (Or.inr ⟨S,rfl⟩)

theorem sextetVector_smul (g : M24) (S : Sextet) :
    cocodeRepresentation g (sextetVector S) = sextetVector (g • S) := by
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  have hgB : g • B ∈ (g • S).parts := Finset.smul_mem_smul_finset hB
  rw [sextetVector_eq S hB,evenSetVector_equivariant,sextetVector_eq (g • S) hgB]

private theorem tetrad_is_sextet (B : Finset (Fin 24)) (hB : B.card = 4) :
    ∃ S, evenSetVector B (by rw [hB]; decide) = sextetVector S := by
  rcases cocode_cases (evenSetVector B (by rw [hB]; decide)) with hz | ⟨P,hP⟩ | hs
  · exact (evenSetVector_ne_zero_of_card_lt_eight B _ (by omega) (by omega) hz).elim
  · exfalso
    have hm : wordOfSet B - wordOfSet P.val ∈ golay :=
      (Submodule.Quotient.eq codeInCore).mp hP
    have hn : wordOfSet B - wordOfSet P.val ≠ 0 := by
      intro hz
      have hc := congrArg Finset.card (wordOfSet_injective (sub_eq_zero.mp hz))
      rw [hB,P.property] at hc
      omega
    have hl := native_golay_minimum hm hn
    have hu := wordOfSet_sub_weight_le B P.val
    rw [hB,P.property] at hu
    omega
  · exact hs

private theorem generator_moves_pair (x y : Fin 24) (hne : x ≠ y) :
    ∃ k : Fin 4, Disjoint ({x,y} : Finset (Fin 24))
      (({x,y} : Finset (Fin 24)).image (FarOrbit.generatorPerm k)) ∧
      ({x,y} ∪ ({x,y} : Finset (Fin 24)).image (FarOrbit.generatorPerm k)) ∉ standardSextet.parts := by
  revert x y; decide +kernel

private theorem pair_add_of_disjoint (P Q : PointPair) (hd : Disjoint P.val Q.val) :
    pairVector P + pairVector Q =
      evenSetVector (P.val ∪ Q.val) (by rw [Finset.card_union_of_disjoint hd,P.property,Q.property]; decide) := by
  change codeInCore.mkQ _ + codeInCore.mkQ _ = codeInCore.mkQ _
  rw [←map_add]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  ext i
  have hdis := Finset.disjoint_left.mp hd
  by_cases hi : i ∈ P.val <;> by_cases hj : i ∈ Q.val
  · exact (hdis hi hj).elim
  all_goals simp [wordOfSet,hi,hj]

private theorem pair_displacement_standard (P : PointPair) :
    ∃ g : sextetStabilizer standardSextet, ∃ S : Sextet, S ≠ standardSextet ∧
      pairVector P + cocodeRepresentation g.val (pairVector P) = sextetVector S := by
  obtain ⟨x,y,hxy,hP⟩ := Finset.card_eq_two.mp P.property
  obtain ⟨k,hdis,hnot⟩ := generator_moves_pair x y hxy
  let g := FarOrbit.nativeGenerator k
  let Q := mapPair g.val P
  have hQ : Q.val = P.val.image (FarOrbit.generatorPerm k) := rfl
  have hd : Disjoint P.val Q.val := by rw [hQ,hP]; exact hdis
  have hc : (P.val ∪ Q.val).card = 4 := by
    rw [Finset.card_union_of_disjoint hd,P.property,Q.property]
  obtain ⟨S,hS⟩ := tetrad_is_sextet (P.val ∪ Q.val) hc
  refine ⟨g,S,?_,?_⟩
  · intro he
    subst S
    have hh := (evenSetVector_eq_sextetVector_iff standardSextet hc).mp hS
    rw [hQ,hP] at hh
    exact hnot hh
  · rw [pairVector_equivariant]
    exact (pair_add_of_disjoint P Q hd).trans hS

theorem pair_displacement (S : Sextet) (P : PointPair) :
    ∃ g : sextetStabilizer S, ∃ T : Sextet, T ≠ S ∧
      pairVector P + cocodeRepresentation g.val (pairVector P) = sextetVector T := by
  obtain ⟨k,hk⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator S
  have hkS : k • standardSextet = S := plane_parts_injective hk
  obtain ⟨g,T,hne,he⟩ := pair_displacement_standard (mapPair k⁻¹ P)
  let g' : sextetStabilizer S := ⟨k*g.val*k⁻¹,by
    change (k*g.val*k⁻¹) • S.parts = S.parts
    rw [←hk,mul_smul,mul_smul,inv_smul_smul,g.property]⟩
  refine ⟨g',k • T,?_,?_⟩
  · rw [←hkS]
    exact fun hh => hne (MulAction.injective k hh)
  · have hh := congrArg (cocodeRepresentation k) he
    rw [map_add,sextetVector_smul,←pairVector_equivariant] at hh
    have hl : cocodeRepresentation k (cocodeRepresentation k⁻¹ (pairVector P)) = pairVector P := by
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [hl] at hh
    change pairVector P + cocodeRepresentation (k*g.val*k⁻¹) (pairVector P) = _
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply]
    exact hh
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeVectors
