module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryCartanFixed

/-!
# Marking the actual special-unitary Cartan

The canonical simple root is a full Sylow subgroup of its actual special-unitary
actor. Its Borel normalizer and the source involutory reflection identify
R_j intersect H with the literal two-point subgroup. Simultaneous unitary pair
normalization then supplies a single group equivalence carrying that subgroup
to the full standard special torus. Scalar centers and right conjugation are
retained.

Source: Fong--Seitz I (6D), pp.42--43; Huppert II.10.12 and the proved unitary
Sylow/involution pair normalization used in GLS4, Chapter 4, Lemma 3.2.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External BenderSuzuki.PFAppendixIII
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates HermitianForm ReeSource BenderSuzuki.ZD.RankOneModelGeometry
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

include hJ in
private theorem source_special_sylow {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F=(2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n))
    (j : Fin 2) (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j)=(2^n)^3) :
    ∃ S : Sylow 2 (rankOne Q split j),
      (S : Subgroup (rankOne Q split j))=(simpleRoot Q split j).subgroupOf (rankOne Q split j) := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨S,hS⟩:=hA.exists_le_sylow
  let S' := S.mapSurjective (f:=μ.toMonoidHom) μ.surjective
  have hcA : Nat.card A=(2^n)^3 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).toEquiv).trans hroot
  have hf:=FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let U:=EvenTwoRank.rootSylow J hJ (by omega : 0<n) hcard hf
  have hcS : Nat.card S=(2^n)^3 := by
    rw [Nat.card_congr ((S : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective).toEquiv]
    change Nat.card S'=_
    rw [Nat.card_congr (SylowOmega.specialSylowEquivProjective J S').toEquiv,
      Nat.card_congr ((S'.mapSurjective J.specialToProjective_surjective).equiv U).toEquiv]
    exact OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ _ hcard hf
  exact ⟨S,(eq_of_le_of_card_ge hS (by rw [hcA,hcS])).symm⟩

private theorem twoPoint_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (t : G) :
    (twoPoint B t).map e.toMonoidHom=twoPoint (B.map e.toMonoidHom) (e t) := by
  rw [twoPoint,twoPoint,Subgroup.map_inf _ _ _ e.injective]
  congr 1
  simp only [BenderSuzuki.PFchapter1section1.rightConjugate,Subgroup.conjBy,Subgroup.map_map]
  congr 1
  ext x
  simp

/-- The source Cartan inside R_j maps onto the full special-unitary torus. -/
theorem exists_special_unitary_cartan_marking {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F=(2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n))
    (j : Fin 2) (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : rankOne Q split j ≃* J.specialSubgroup)
    (hroot : Nat.card (simpleRoot Q split j)=(2^n)^3) :
    ∃ e : rankOne Q split j ≃* J.specialSubgroup,
      ((Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)).map e.toMonoidHom =
        BorelTorus.specialTorus J hJ := by
  obtain ⟨S,hS⟩:=source_special_sylow J hJ Q split hn hcard hconj j μ hroot
  let s:=UnitarySource.actorReflection Q split j
  let r:=involutoryRootReflection Q split j s
  let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
  have ht : IsInvolution t := ⟨fun he => involutoryRootReflection_ne_one Q split j s
    (congrArg Subtype.val he),Subtype.ext (involutoryRootReflection_sq Q split j s)⟩
  have htB : t∉normalizer (S : Set (rankOne Q split j)) := by
    intro htB
    rw [show (S : Set (rankOne Q split j))=
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS] at htB
    exact Q.tits.representative_not_mem_B (Q.simple_mem j) r.val r.class_eq
      ((rankOne_borel_iff_root_normalizer Q split j hK t).mpr htB)
  have he : twoPoint (normalizer (S : Set (rankOne Q split j))) t =
      (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) := by
    ext x
    change x∈normalizer (S : Set (rankOne Q split j)) ∧
      x∈BenderSuzuki.PFchapter1section1.rightConjugate (normalizer (S : Set (rankOne Q split j))) t ↔ _
    rw [LinearGeometry.mem_rightConjugate]
    simp only [show (S : Set (rankOne Q split j))=
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS,
      ←rankOne_borel_iff_root_normalizer Q split j hK]
    constructor
    · intro hx
      apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split j
      refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split j x.property,hx.1,?_⟩
      rw [borelConjugate_eq _ r.val r.class_eq]
      exact hx.2
    · intro hx
      exact ⟨hx.1,((torus_conjugate r.val).symm ▸ hx).1⟩
  let S' := S.mapSurjective (f:=μ.toMonoidHom) μ.surjective
  have hi : IsInvolution (μ t) :=
    ⟨fun hh => ht.1 (μ.injective (hh.trans μ.map_one.symm)),by rw [←map_pow,ht.2,map_one]⟩
  have ho : μ t∉normalizer (S' : Set J.specialSubgroup) := by
    intro hh
    change μ t∈normalizer ((S : Subgroup _).map μ.toMonoidHom : Set _) at hh
    rw [←map_equiv_normalizer_eq] at hh
    obtain ⟨x,hx,hxt⟩:=hh
    exact htB (μ.injective hxt ▸ hx)
  have hf:=FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨g,_,_,hg⟩:=PairNormalization.special_pair J hJ hn hcard hf S' (μ t) hi ho
  refine ⟨μ.trans (MulAut.conj g),?_⟩
  rw [←he]
  change (twoPoint (normalizer (S : Set (rankOne Q split j))) t).map
    ((MulAut.conj g).toMonoidHom.comp μ.toMonoidHom)=_
  rw [←Subgroup.map_map,twoPoint_map]
  have hN : (normalizer (S : Set (rankOne Q split j))).map μ.toMonoidHom =
      normalizer (S' : Set J.specialSubgroup) := by
    exact map_equiv_normalizer_eq (S : Subgroup (rankOne Q split j)) μ
  rw [hN]
  exact hg
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
