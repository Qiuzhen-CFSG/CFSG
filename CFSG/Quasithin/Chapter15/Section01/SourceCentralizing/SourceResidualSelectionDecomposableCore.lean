module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSylow
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import Theory.GroupTheory.IndexTwoOmegaDiagonal
public import Theory.GroupTheory.PGroup.CharacteristicTwoNormalClosure

/-!
# The original decomposable fixed subgroup inside the moving core

The prime-three support geometry makes C_T(E) have index two for the
literal E=C_V(J1(T)). Every commutator of T with E is then a diagonal
central involution of T. In a Sylow overgroup P centralizing those
involutions, [O2(P),E] is central in P. The characteristic-two normal
closure theorem puts E inside O2(P).

This retains the original sixteen-element fixed subgroup and arbitrary
actual P inside C_G(Omega1 Z(T)); it assumes no normalization of E by P.
Source: Aschbacher--Smith 15.1.13--16, printed pp.1091--1092, using the
characteristic-two normal-closure argument.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem elementary_commutator_le_omegaCenter_of_centralizer_index_two
    (T E : Subgroup G) [IsElementaryAbelian 2 E]
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set G))
    (hi : (T ⊓ centralizer (E : Set G)).relIndex T = 2) :
    ⁅T,E⁆ ≤ omegaOneCenterAmbient T := by
  let S := T ⊓ centralizer (E : Set G)
  have hES : E ≤ S := le_inf hET E.le_centralizer
  have hEω : E ≤ omegaOneCenterAmbient S := by
    intro e he
    exact (mem_omegaOneCenterAmbient_iff S e).mpr
      ⟨hES he,elemPow_eq_one_of_isElementaryAbelian e he,fun x hx => (hx.2 e he).symm⟩
  apply commutator_le.mpr
  intro t ht e he
  by_cases htS : t ∈ S
  · have hc : Commute t e := (htS.2 e he).symm
    rw [hc.commutator_eq]
    exact one_mem _
  · have hconj : t*e*t⁻¹ ∈ E := (mem_normalizer_iff.mp (hTE ht) e).mp he
    have hc : Commute e (t*e*t⁻¹) := ((E.le_centralizer he) _ hconj).symm
    have hd := indexTwo_diagonal_mem_omegaCenter S T inf_le_left hi t ht htS e (hEω he) hc
    have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) e he)
    simpa only [commutatorElement_def,hinv,hc.eq] using hd

/-- The actual cubic decomposable fixed subgroup has only central seed
commutators with the original Sylow group. -/
theorem DecomposableMarker.ThompsonPair.fixed_commutator_le_seed_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized)
      (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3) :
    ⁅(T : Subgroup G),thompsonFixed T V⁆ ≤ centralInvolutions T := by
  let E := thompsonFixed T V
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hET : E ≤ (T : Subgroup G) := by
    intro e he
    exact ChapterB.thompsonJ_le _ _
      ((mem_omegaOneCenterAmbient_iff _ _).mp (h.thompsonFixed_le_omega T hM he)).1
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hfour := s.support_four_not_dvd_of_prime_three hG T hM hfull h.normalized
    c d hd π hp hs hthree s.first
  exact elementary_commutator_le_omegaCenter_of_centralizer_index_two
    (T : Subgroup G) E hET hTE
    (s.fixed_sylow_kernel_of_support_four_not_dvd hM.1.2 h.normalized c d hfour).2

/-- Every actual Sylow overgroup centralizing the original central seed
contains the same cubic decomposable fixed subgroup in its two-core. -/
theorem DecomposableMarker.ThompsonPair.fixed_le_core_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V P : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized)
      (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (hd : d.FittingFull)
    (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3)
    (hP : P ∈ Chapter1.HOver G (T : Set G))
    (hPC : P ≤ centralizer (centralInvolutions T : Set G)) :
    thompsonFixed T V ≤ P.pCoreIn 2 := by
  let E := thompsonFixed T V
  have hET : E ≤ (T : Subgroup G) := by
    intro e he
    exact ChapterB.thompsonJ_le _ _
      ((mem_omegaOneCenterAmbient_iff _ _).mp (h.thompsonFixed_le_omega T hM he)).1
  have hEP : E ≤ P := hET.trans hP.2
  let EP := E.subgroupOf P
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 EP := IsElementaryAbelian.subgroupOf hEP
  have hTZ := s.fixed_commutator_le_seed_of_prime_three hG T hM h hfull c d hd π hp hs hthree
  have hcomm : ⁅pCore 2 P,EP⁆ ≤ center P := by
    apply commutator_le.mpr
    intro q hq e he
    have hqT : (q : G) ∈ (T : Subgroup G) :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hP.2) hq
    have hz : (q*e*q⁻¹*e⁻¹ : P).val ∈ centralInvolutions T :=
      hTZ (commutator_mem_commutator hqT he)
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hPC x.property _ hz).symm
  have hchar : centralizer (pCore 2 P : Set P) ≤ pCore 2 P :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hP)
  have hW := normalClosure_isPGroup_of_characteristicTwo (center P) EP hchar
    inferInstance hcomm (commutator_eq_bot_iff_le_centralizer.mpr (center_le_centralizer _))
    inferInstance
  have hEQ : EP ≤ pCore 2 P :=
    (le_normalClosure (H := EP)).trans (le_sSup ⟨inferInstance,hW⟩)
  intro e he
  exact mem_map_of_mem P.subtype (hEQ (show (⟨e,hEP he⟩ : P) ∈ EP from he))

end CFSG.Quasithin.Chapter15.Section01
