module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.Action
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.LocalMembers
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThreeCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals.BinaryGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals.NonbinaryGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.Quasisimple
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.LocalSections
public import Theory.GroupTheory.ElementaryActorCentralizerSylow

/-!
# From actual centralizer geometry to E-local witnesses

The inner centralizer is normal in the full centralizer, and its quotient
embeds in G/L, hence is a two-group when G = LT. If that inner centralizer
is nonabelian simple, the radical of the full centralizer intersects it
trivially. A nontrivial inner actor therefore survives the literal radical
quotient. The existing quasisimple two-extension theorem then checks all
E2 clauses, including both residuals and the local tau orbit. In the binary
case an actual S₃ epimorphism supplies E1 instead.

The Sylow arrangement retains the entire actor. At exact rank f + 1, the
binary geometry supplies the S₃ quotient, while the nonbinary geometry
selects a graph or field actor and proves the simple fixed-group structure
and generation with the original marked Sylow subgroup. Thus
`hasCentralizerLocalWitness_of_exact_rank` discharges every geometry premise.
Its E.1.5 application also derives E0 and the quotient rank bound. These
local results do not need the source's SQTK hypothesis; the universal sharp
rank bound and final family assembly remain separate.

Source: Aschbacher--Smith E.1.1--5 and E.1.14(1), printed pp.209--210, 214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem actor_le_centralizer (A : Subgroup G) [IsElementaryAbelian 2 A]
    {z : G} (hz : z ∈ A) : A ≤ centralizer ({z} : Set G) := by
  intro a ha
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨z, hz⟩))

/-- Every selected outer element admits a Sylow arrangement retaining its
whole elementary actor and its exclusion from the normal socle. -/
theorem exists_outer_actor_sylow_centralizer (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (z : G) (hzA : z ∈ A) (hzL : z ∉ L) :
    ∃ g w : G,
      let B := A.map (MulAut.conj g).toMonoidHom
      B ≤ (T : Subgroup G) ∧ w ∈ B ∧ w ∉ L ∧
      ∃ S : Sylow 2 (centralizer ({w} : Set G)),
        (S : Subgroup (centralizer ({w} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({w} : Set G)) := by
  let := hA
  obtain ⟨g, hB, S, hS⟩ := T.exists_conj_actor_with_sylow_centralizer A
    (IsElementaryAbelian.isPGroup 2 A) z (hAT hzA) (actor_le_centralizer A hzA)
  refine ⟨g, (MulAut.conj g) z, hB, mem_map_of_mem _ hzA, ?_, S, hS⟩
  intro hz
  have h := (inferInstance : L.Normal).conj_mem ((MulAut.conj g) z) hz g⁻¹
  apply hzL
  simpa [MulAut.conj_apply, mul_assoc] using h

omit [Finite G] in
private theorem inner_quotient_isTwoGroup (L K : Subgroup G) [L.Normal]
    (hq : IsPGroup 2 (G ⧸ L)) : IsPGroup 2 (K ⧸ L.subgroupOf K) := by
  let π := (QuotientGroup.mk' L).comp K.subtype
  have hker : π.ker = L.subgroupOf K := by
    ext x
    exact QuotientGroup.eq_one_iff _
  exact (hq.to_subgroup π.range).of_equiv
    ((QuotientGroup.quotientKerEquivRange π).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))

/-- A nontrivial inner actor survives the intrinsic radical of a centralizer
whose inner part is nonabelian simple. The quotient and E2 structure are
derived from G = LT, not supplied as additional premises. -/
theorem component_case_of_simple_inner_centralizer
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (A : Subgroup G) (z : G)
    (hAC : A ≤ centralizer ({z} : Set G)) (hAL : A ⊓ L ≠ ⊥)
    [IsSimpleGroup (L.subgroupOf (centralizer ({z} : Set G)))]
    [Group.IsPerfect (L.subgroupOf (centralizer ({z} : Set G)))] :
    ECaseComponent (T : Subgroup G) A (centralizer ({z} : Set G)) := by
  let C := centralizer ({z} : Set G)
  let D := L.subgroupOf C
  have hz : center D = ⊥ := by
    rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple D := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hr : solvableRadical D = ⊥ :=
    le_bot_iff.mp (IsQuasisimple.solvableRadical_le_center.trans hz.le)
  have hne : ¬ A.subgroupOf C ≤ solvableRadical C := by
    intro hA
    apply hAL
    apply le_bot_iff.mp
    intro a ha
    let d : D := ⟨⟨a, hAC ha.1⟩, ha.2⟩
    have hd : d ∈ solvableRadical D := by
      rw [← radical_subgroupOf_normal D]
      exact hA ha.1
    rw [hr, mem_bot] at hd
    exact congrArg (fun x : D => ((x : C) : G)) hd
  have hq := inner_quotient_isTwoGroup L C
    (isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT)
  exact ValuesOdd.PSUThreeGeneration.eCaseComponent_of_quasisimple_two_quotient
    (T : Subgroup G) A C D (hz ▸ IsPGroup.of_bot) hq hne

/-- The simple centralizer geometry constructs the requested witness with
the whole centralizer as local subgroup. No residual supplement is needed. -/
theorem hasCentralizerLocalWitness_of_simple_geometry
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (h : SimpleCentralizerGeometry L T A) :
    HasCentralizerLocalWitness L T A := by
  obtain ⟨g, z, hBT, hzB, hzL, ⟨S, hS⟩, hs, hp, hBL, hgen⟩ := h
  let := hA
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let := hs
  let := hp
  refine ⟨g, z, hBT, hzB, hzL, S, hS, centralizer ({z} : Set G),
    inf_le_right, le_rfl, Or.inr ?_, hgen⟩
  exact component_case_of_simple_inner_centralizer L T hLT B z
    (actor_le_centralizer B hzB) hBL

/-- The binary geometry supplies the actual odd E-case through its S₃
epimorphism, with nontriviality tested on the whole conjugate actor. -/
theorem hasCentralizerLocalWitness_of_binary_geometry
    (L : Subgroup G) (T : Sylow 2 G) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (h : BinaryCentralizerGeometry L T A) :
    HasCentralizerLocalWitness L T A := by
  obtain ⟨g, z, hBT, hzB, hzL, ⟨S, hS⟩, π, hπ, hker, hB, hgen⟩ := h
  let := hA
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  refine ⟨g, z, hBT, hzB, hzL, S, hS, centralizer ({z} : Set G),
    inf_le_right, le_rfl, Or.inl ?_, hgen⟩
  exact ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.eCaseOdd_of_symmetricThree_quotient
    B _ inferInstance (actor_le_centralizer B hzB) π hπ hker hB

open Matrix.PSL3.LinearThree
open scoped MatrixGroups

variable {F : Type*} [Field F] [Finite F]
variable [IsSimpleGroup (generalizedFitting G)]

/-- The actual centralizer local witness for an outer elementary actor of
exact rank f + 1 in the PSL₃(2ᶠ) branch of E.1.14(1). The binary and
nonbinary model calculations discharge every local-geometry premise. -/
theorem hasCentralizerLocalWitness_of_exact_rank
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ (T : Subgroup G))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (houter : ¬ A ≤ generalizedFitting G)
    (hrank : Group.rank A = f + 1) :
    HasCentralizerLocalWitness (generalizedFitting G) T A := by
  by_cases hf1 : f = 1
  · apply hasCentralizerLocalWitness_of_binary_geometry _ T A hA
    exact binaryCentralizerGeometry_of_card_two e (by simpa [hf1] using hF)
      T A hA hAT houter (by simpa [hf1] using hrank)
  · apply hasCentralizerLocalWitness_of_simple_geometry _ T hLT A hA
    exact NonbinaryGeometry.simpleCentralizerGeometry_of_exact_rank e T
      (by omega) hF hUT A hA hAT houter hrank

/-- Application to the literal E.1.5 local family: a conjugate of the whole
actor has a centralizing member at parameter f that generates the socle
together with the original T. E0, Sylow intersection and quotient rank are
all derived, so no local E-case or geometry premise remains. -/
theorem exists_centralizing_eMemberAt_of_exact_rank
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ (T : Subgroup G))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (houter : ¬ A ≤ generalizedFitting G)
    (hrank : Group.rank A = f + 1) :
    ∃ g z : G, ∃ K : Subgroup G,
      let B := A.map (MulAut.conj g).toMonoidHom
      z ∈ B ∧ z ∉ generalizedFitting G ∧
      K ≤ centralizer ({z} : Set G) ∧ IsEMemberAt f (T : Subgroup G) B K ∧
      generalizedFitting G ≤ K ⊔ (T : Subgroup G) := by
  obtain ⟨g, z, hBT, hzB, hzL, S, hS, K, hSK, hKC, hcase, hgen⟩ :=
    hasCentralizerLocalWitness_of_exact_rank e T hf hF hLT hUT A hA hAT houter hrank
  let := hA
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBrank : Group.rank B ≤ f + 1 :=
    (Group.rank_congr ((MulAut.conj g).subgroupMap A)).symm.le.trans hrank.le
  refine ⟨g, z, K, hzB, hzL, hKC, ?_, hgen⟩
  exact isEMemberAt_of_centralizer_intermediate hf (twoCore_eq_bot e T hLT)
    T B hB hBT hBrank z hzB (fun h => hzL (h ▸ (generalizedFitting G).one_mem))
    S hS K hSK hKC hcase

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
