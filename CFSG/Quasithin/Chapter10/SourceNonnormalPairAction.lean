module
public import CFSG.Quasithin.Chapter10.SourceCubicResidual
public import CFSG.Quasithin.Chapter3.Section02.ModuleConsequences
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The original pair of moved factors under the maximal local group

The nonnormal component has exactly two conjugates inside M, by the proved
source C-component theorem. The same two conjugates occur under the original
Sylow subgroup. Since M normalizes V and V=[V,L₀], relative commutator
generation gives V=[V,L]·[V,L]^t and M permutes these two moved factors.
This requires neither a marked module model nor failure of Baumann-normalizer
containment. It does not assert that the two factors are disjoint.

The cubic residual identity L₀=O^{3′}(M) also makes the orbit rigid:
L₀≤M^g exactly when g∈M. This is the actual residual comparison used in
the weak-closure argument, retaining the literal source subgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.1.1, 10.1.3, and the proof of 10.2.12, printed pp.741–742 and 754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

omit D [Finite G] in
private theorem relative_commutator_sup (V A B : Subgroup G)
    (hAV : A ≤ normalizer (V : Set G)) (hBV : B ≤ normalizer (V : Set G)) :
    ⁅V,A ⊔ B⁆ = ⁅V,A⁆ ⊔ ⁅V,B⁆ := by
  let W := ⁅V,A⁆ ⊔ ⁅V,B⁆
  have hWV : W ≤ V := sup_le (le_normalizer_iff_commutator_le_left.mp hAV)
    (le_normalizer_iff_commutator_le_left.mp hBV)
  have hAN : A ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl hWV).trans (by rw [commutator_comm]; exact le_sup_left))
  have hBN : B ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl hWV).trans (by rw [commutator_comm]; exact le_sup_right))
  apply le_antisymm ?_ (sup_le (commutator_mono le_rfl le_sup_left)
    (commutator_mono le_rfl le_sup_right))
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (A ⊔ B) A B V W
    (sup_le hAN hBN) le_sup_left le_sup_right
    (by rw [commutator_comm]; exact le_sup_left)
    (by rw [commutator_comm]; exact le_sup_right)

/-- Every M-conjugate of L is one of the original two T-conjugates. -/
theorem source_nonnormal_maximal_pair
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ∀ m ∈ D.maximalLocal,
      L.map (MulAut.conj m).toMonoidHom = L ∨
      L.map (MulAut.conj m).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  let tM : M := ⟨t,hTM ht⟩
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk (source_uniqueness D).normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi,_⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  have hmap (s : M) : (A.map (MulAut.conj s).toMonoidHom).map M.subtype =
      L.map (MulAut.conj (s : G)).toMonoidHom := by
    rw [map_map, show M.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : G)).toMonoidHom.comp M.subtype from rfl,
      ← map_map, map_subgroupOf_eq_of_le hLM]
  have hm : A.map (MulAut.conj tM).toMonoidHom ≠ A := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (map M.subtype) he
    rwa [hmap,map_subgroupOf_eq_of_le hLM] at hh
  intro m hmM
  rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm (⟨m,hmM⟩ : M) with he|he
  · left
    have hh := congrArg (map M.subtype) he
    rwa [hmap,map_subgroupOf_eq_of_le hLM] at hh
  · right
    have hh := congrArg (map M.subtype) he
    rwa [hmap,hmap] at hh

/-- The original full module is the product of its two moved factors, permuted by M. -/
theorem source_nonnormal_fullModule_pair
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      D.fullModule = ⁅D.fullModule,L⁆ ⊔
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ∧
      ∀ m ∈ D.maximalLocal,
        (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom = ⁅D.fullModule,L⁆ ∨
        (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom =
          (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hmaps (m : G) (hm : m ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
  have hLN : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hLtN : L.map (MulAut.conj t).toMonoidHom ≤ normalizer (D.fullModule : Set G) :=
    ((le_sup_right.trans hpair.ge).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  refine ⟨t,ht,htn,hpair,?_,?_⟩
  · rw [map_commutator,hmaps t (hTM ht),←relative_commutator_sup _ _ _ hLN hLtN,
      ←hpair,←D.fullModule_eq_commutator (source_uniqueness D)]
  · intro m hm
    rw [map_commutator,hmaps m hm,map_commutator,hmaps t (hTM ht)]
    rcases source_nonnormal_maximal_pair D hn ht htn m hm with he|he
    · exact Or.inl (congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) he)
    · exact Or.inr (congrArg (fun K : Subgroup G => ⁅D.fullModule,K⁆) he)

/-- Original10.1.3 makes containment of L₀ in a conjugate of M rigid. -/
theorem source_nonnormal_orbit_le_conjugate_maximal_iff
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) (g : G) :
    localOrbit T L ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom ↔
      g ∈ D.maximalLocal := by
  let R := localOrbit T L
  let M := D.maximalLocal
  have hr : (primeToResidual 3 M).map M.subtype = R :=
    source_nonnormal_cubic_residual D hn hd
  have hid : (primeToResidual 3 R).map R.subtype = R := by
    have he := map_embedded_primeToResidual_of_hom 3 (primeToResidual 3 M) M.subtype
    rw [embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 M) le_rfl,hr] at he
    exact he.symm
  constructor
  · intro hle
    have hm := embedded_primeToResidual_mono 3 hle
    rw [hid,←map_embedded_primeToResidual 3 M (MulAut.conj g),hr] at hm
    have he : R = R.map (MulAut.conj g).toMonoidHom := eq_of_le_of_card_ge hm
      (Nat.card_congr ((MulAut.conj g).subgroupMap R).toEquiv).ge
    exact mem_normalizer_iff_map_conj_eq.mpr he.symm
  · intro hg
    have he : M.map (MulAut.conj g).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg)
    rw [he]
    exact R.le_normalizer

end CFSG.Quasithin.Chapter10
