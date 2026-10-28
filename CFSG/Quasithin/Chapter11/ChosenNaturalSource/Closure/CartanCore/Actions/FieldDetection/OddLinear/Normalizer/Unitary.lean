module
public import Theory.SpecificGroups.SU3.BorelCoprimeFieldAction
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.GroupTheory.QuotientSylowNormalizerDisplacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.Coefficients
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components

/-!
# Unitary odd-subfield normalizer lifts

Align the literal I/O₂(I) projection with the Hermitian root Sylow group.
The field coefficient of each original Sylow actor has two-power order,
so it fixes the constructed odd-degree subfield. The triangular unitary
factor contributes only a root displacement. Hence every lift of each
odd-subfield torus element normalizes the original Sylow subgroup.

Source: Aschbacher--Smith 11.5.6(3), pp.780--781, the Borel movement route
for the surviving unitary row of the full A.3.6 catalogue.
-/

@[expose] public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelCoprimeFieldAction
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}

/-- Coordinates on the literal quotient, aligned with the original Sylow intersection. -/
structure Coordinates (T : Sylow 2 G) (I : Subgroup G) (F : BinaryField) (J : HermitianForm 3 F.Carrier)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) where
  model : (I ⧸ pCore 2 I) ≃* ProjectiveSpecialUnitaryMatrixGroup J
  sylow_image : ((T : Subgroup G).subgroupOf I).map
    (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = projectiveRoot J hJ

namespace Coordinates
variable {F : BinaryField} {J : HermitianForm 3 F.Carrier}
    {hJ : J.form = !![0,0,1;0,1,0;1,0,0]} (c : Coordinates T I F J hJ)

def quotient : I →* ProjectiveSpecialUnitaryMatrixGroup J :=
  c.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))

omit [Finite G] in
theorem quotient_surjective : Function.Surjective c.quotient :=
  c.model.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem quotient_sylow_image : ((T : Subgroup G).subgroupOf I).map c.quotient =
    projectiveRoot J hJ := c.sylow_image

def actor (x : normalizer (I : Set G)) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  MulAut.congr c.model (coreQuotientAction I x)

omit [Finite G] in
theorem actor_quotient (x : normalizer (I : Set G)) (i : I) :
    c.actor x (c.quotient i) = c.quotient (I.normalizerMonoidHom x i) := by
  change c.model (coreQuotientAction I x (c.model.symm
    (c.model (QuotientGroup.mk' (pCore 2 I) i)))) = _
  rw [c.model.symm_apply_apply,coreQuotientAction_apply_mk]
  rfl

omit [Finite G] in
theorem actor_preserves_root (x : normalizer (I : Set G))
    (hx : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G)) :
    (projectiveRoot J hJ).map (c.actor x).toMonoidHom = projectiveRoot J hJ := by
  rw [← c.quotient_sylow_image]
  have he : (c.actor x).toMonoidHom.comp c.quotient =
      c.quotient.comp (I.normalizerMonoidHom x).toMonoidHom := by
    apply MonoidHom.ext
    intro i
    exact c.actor_quotient x i
  rw [Subgroup.map_map,he,← Subgroup.map_map]
  congr 1
  ext i
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ((mem_normalizer_iff.mp hx j).mp ⟨hj,j.property⟩).1
  · intro hi
    refine ⟨(I.normalizerMonoidHom x).symm i,?_,(I.normalizerMonoidHom x).apply_symm_apply i⟩
    exact ((mem_normalizer_iff.mp ((normalizer _).inv_mem hx) i).mp
      ⟨hi,i.property⟩).1

/-- Every lift of an odd-subfield torus element normalizes the original T. -/
theorem normalizes_of_odd_torus
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (b : I) (u : (oddField F).Carrierˣ)
    (hb : c.quotient b = hermitianTorusPSU J hJ (Units.map (oddInclusion F).toMonoidHom u)) :
    (b : G) ∈ normalizer (T : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have hk : c.quotient.ker ≤ (T : Subgroup G).subgroupOf I := by
    intro i hi
    have hi' : i ∈ pCore 2 I := (QuotientGroup.eq_one_iff _).mp
      (c.model.map_eq_one_iff.mp hi)
    rw [← hP]
    exact pCore_isPGroup.le_sylow_of_normal P hi'
  let a : T → MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := fun t => c.actor ⟨t,hTI t.property⟩
  apply mem_normalizer_of_quotient_displacements (T : Subgroup G) I hTI
    c.quotient hk a (fun t i => c.actor_quotient ⟨t,hTI t.property⟩ i) b
  intro t
  have htS : (t : G) ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(T : Subgroup G).le_normalizer t.property,hTI t.property⟩
  have hr := c.actor_preserves_root ⟨t,hTI t.property⟩ htS
  obtain ⟨σ,hσ⟩ := EvenSemilinear.semilinear_coverage J hJ hn hc hconj (a t)
  obtain ⟨k,hkpow⟩ := T.isPGroup'.exists_pow_pow_eq_one t
  have hapow : a t ^ (2 ^ k) = 1 := by
    let f := (MulAut.congr c.model).toMonoidHom.comp
      ((coreQuotientAction I).comp (inclusion hTI))
    change f t ^ (2 ^ k) = 1
    rw [← map_pow,hkpow,map_one]
  have hσpow := coefficient_pow J hJ hn hc hconj hσ hapow
  rw [c.quotient_sylow_image,hb]
  exact torus_displacement_of_fixed J hJ hn hc hconj (a t) hσ hr _
    (oddInclusion_fixed_of_two_power F σ hσpow u)

/-- Every coefficient has a lift in the same original Sylow normalizer. -/
theorem odd_torus_lifts
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (u : (oddField F).Carrierˣ) : ∃ b : I,
      (b : G) ∈ normalizer (T : Set G) ∧
      c.quotient b = hermitianTorusPSU J hJ (Units.map (oddInclusion F).toMonoidHom u) := by
  obtain ⟨b,hb⟩ := c.quotient_surjective
    (hermitianTorusPSU J hJ (Units.map (oddInclusion F).toMonoidHom u))
  exact ⟨b,c.normalizes_of_odd_torus hn hc hconj hTI b u hb,hb⟩
end Coordinates

/-- Sylow conjugacy constructs coordinates on the actual unitary quotient. -/
theorem exists_coordinates (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (F : BinaryField) (J : HermitianForm 3 F.Carrier)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : (I ⧸ pCore 2 I) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nonempty (Coordinates T I F J hJ) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hconj
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S
    (EvenTwoRank.rootSylow J hJ hn hc hf)
  let e' := e.trans (MulAut.conj g)
  refine ⟨⟨e',?_⟩⟩
  have hh := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul,EvenTwoRank.rootSylow_coe] at hh
  change ((P : Subgroup I).map q).map (MulAut.conj g).toMonoidHom = _ at hh
  have heq : e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)) =
      (MulAut.conj g).toMonoidHom.comp q := rfl
  rw [heq,← Subgroup.map_map,← hP]
  exact hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear.Unitary
