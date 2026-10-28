module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.Action
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.LocalMembers
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThreeCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals.BinaryGeometry.ModelTransport
public import Theory.GroupTheory.ElementaryActorCentralizerSylow
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerQuotient
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerGeneration

/-!
# Binary outer-centralizer geometry

The faithful source action, the binary outer-group order, and the existence
of an outer actor identify the ambient group with Aut(SL₃(2)). We conjugate
the entire elementary actor into the marked Sylow while making its selected
outer involution have a Sylow centralizer. Only then do we apply the model
centralizer and generation calculations to that actual Sylow image.

An S₃ epimorphism with kernel of order two transports to the whole source
centralizer. The exact rank-two hypothesis prevents the actor from lying in
its kernel. Generation transports along the same ambient equivalence, so
there is no assumption that the initial conjugator normalizes the marked T.

The conditional assembly is retained, and
`binaryCentralizerGeometry_of_card_two` discharges both model premises using
the concrete outer-centralizer quotient and generation theorems. Thus the
binary branch needs no additional model hypothesis. The source SQTK,
Sylow-supplement and unipotent-placement assumptions are not needed for this
geometry once the actual simple generalized Fitting subgroup is identified.

This is the raw geometry for the binary branch of Aschbacher--Smith
E.1.14(1), printed p.214. It is consumed by
`hasCentralizerLocalWitness_of_binary_geometry` to verify the source E1
clauses of E.1.1--5, printed pp.209--210.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
variable [IsSimpleGroup (generalizedFitting G)]

/-- The two concrete model calculations imply every raw binary-geometry clause.
The unconditional theorem below supplies both calculations. -/
theorem binaryCentralizerGeometry_of_model_calculations
    (hquot : ∀ z : MulAut Matrix.PSL3Two.SL,
      z ^ 2 = 1 → z ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL →
      ∃ π : centralizer ({z} : Set (MulAut Matrix.PSL3Two.SL)) →* Equiv.Perm (Fin 3),
        Function.Surjective π ∧ Nat.card π.ker = 2)
    (hgenerate : ∀ (P : Sylow 2 (MulAut Matrix.PSL3Two.SL)) (z : MulAut Matrix.PSL3Two.SL),
      z ∈ P → z ^ 2 = 1 → z ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL →
      ∀ π : centralizer ({z} : Set (MulAut Matrix.PSL3Two.SL)) →* Equiv.Perm (Fin 3),
      Function.Surjective π → MulAut.innerSubgroup Matrix.PSL3Two.SL ≤
        centralizer ({z} : Set (MulAut Matrix.PSL3Two.SL)) ⊔ (P : Subgroup _))
    (e : generalizedFitting G ≃* PSL(3,F)) (hF : Nat.card F = 2)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (houter : ¬ A ≤ generalizedFitting G)
    (hrank : Group.rank A = 2) : BinaryCentralizerGeometry (generalizedFitting G) T A := by
  let := hA
  obtain ⟨z, hzA, hzL⟩ := Set.not_subset.mp houter
  have hAC : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨z, hzA⟩))
  obtain ⟨g, hBT, S, hS⟩ := T.exists_conj_actor_with_sylow_centralizer A
    (IsElementaryAbelian.isPGroup 2 A) z (hAT hzA) hAC
  let B := A.map (MulAut.conj g).toMonoidHom
  let w := (MulAut.conj g) z
  let C := centralizer ({w} : Set G)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hwB : w ∈ B := mem_map_of_mem _ hzA
  have hwL : w ∉ generalizedFitting G := by
    intro hw
    have h := (inferInstance : (generalizedFitting G).Normal).conj_mem w hw g⁻¹
    apply hzL
    simpa [w, MulAut.conj_apply, mul_assoc] using h
  have hBC : B ≤ C := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨w, hwB⟩))
  have hBrank : Group.rank B = 2 :=
    (Group.rank_congr (A.equivMapOfInjective _ (MulAut.conj g).injective)).symm.trans hrank
  let E := binaryAmbientEquiv e hF A houter
  have hwouter : E w ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
    intro hw
    apply hwL
    change w ∈ (MulAut.innerSubgroup Matrix.PSL3Two.SL).comap E.toMonoidHom at hw
    rwa [binaryAmbientEquiv_comap_inner] at hw
  have hw2 : (E w) ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian w hwB, map_one]
  obtain ⟨π, hπ, hker⟩ := hquot (E w) hw2 hwouter
  obtain ⟨ρ, hρ, hρker⟩ :=
    CentralizerSmallKernelTransport.exists_quotient_of_equiv E w π hπ hker
  refine ⟨g, w, hBT, hwB, hwL, ⟨S, hS⟩, ρ, hρ,
    IsPGroup.of_card (n := 1) (by simpa using hρker),
    CentralizerSmallKernelTransport.rank_two_not_le_kernel B C inferInstance hBrank hBC ρ hρker, ?_⟩
  have hEsurj : Function.Surjective E.toMonoidHom := E.surjective
  let P : Sylow 2 (MulAut Matrix.PSL3Two.SL) := T.mapSurjective hEsurj
  have hP : (P : Subgroup _) = (T : Subgroup G).map E.toMonoidHom :=
    Sylow.coe_mapSurjective hEsurj T
  have hwP : E w ∈ P := by
    change E w ∈ (P : Subgroup _)
    rw [hP]
    exact mem_map_of_mem _ (hBT hwB)
  have hgen := hgenerate P (E w) hwP hw2 hwouter π hπ
  have hmapC := CentralizerSmallKernelTransport.map_centralizer E w
  rw [← hmapC, hP, ← Subgroup.map_sup] at hgen
  intro x hx
  have hxinner : E x ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
    change x ∈ (MulAut.innerSubgroup Matrix.PSL3Two.SL).comap E.toMonoidHom
    rwa [binaryAmbientEquiv_comap_inner]
  obtain ⟨y, hy, he⟩ := hgen hxinner
  exact E.injective he ▸ hy

/-- Every outer elementary actor of exact rank two over the binary field has
the full centralizer geometry required by the E1 construction. Both the actual
S₃ epimorphism and generation with the marked Sylow are proved model facts. -/
theorem binaryCentralizerGeometry_of_card_two
    (e : generalizedFitting G ≃* PSL(3,F)) (hF : Nat.card F = 2)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (houter : ¬ A ≤ generalizedFitting G)
    (hrank : Group.rank A = 2) : BinaryCentralizerGeometry (generalizedFitting G) T A :=
  binaryCentralizerGeometry_of_model_calculations
    Matrix.PSL3Two.Automorphisms.OuterCentralizerQuotient.exists_outer_centralizer_symmetricThree_quotient
    Matrix.PSL3Two.Automorphisms.OuterCentralizerGeneration.inner_le_centralizer_sup_sylow
    e hF T A hA hAT houter hrank

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
