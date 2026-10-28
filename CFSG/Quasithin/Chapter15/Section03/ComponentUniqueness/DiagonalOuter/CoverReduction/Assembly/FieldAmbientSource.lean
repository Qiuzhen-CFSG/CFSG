module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FieldExclusionSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.PlaneIndex
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Original ambient inputs for the field-centralizer contradiction

The natural orthogonal action makes the original central-involution subgroup
have order two. Its nonidentity element has a two-local centralizer containing
the original Sylow subgroup, so condition (E) and 1.1.4 give characteristic two
there. Simplicity makes the ambient group two-perfect; quasithinness and the
proper K-group hypothesis give SQTK for the literal field centralizer.

The complete KnownSimple Theorems A/C and the marked component index theorem
then discharge every ambient input of the field terminal. Only the original
field-coset fusion and mixed odd-core/extraspecial Sylow-three rows remain.
The earlier empty-family and ordering hypotheses belong to the producers of
`SourceInputs`, `Setup` and `Reduction`; no extra ambient callback is required.

Source: Aschbacher–Smith, proof of 15.3.38, printed pp.1136–1137;
condition (E), and 1.1.4(2),(6), printed pp.500–501.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel FieldExclusion
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem ambient_twoPerfect
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) : IsPPerfect 2 G := by
  let : IsSimpleGroup G := hG.simple
  intro N hN hp
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hpG : IsPGroup 2 G := by
      subst N
      exact hp.of_equiv QuotientGroup.quotientBot
    have hc : center G = ⊤ :=
      (inferInstance : (center G).Normal).eq_bot_or_eq_top.resolve_left hpG.bot_lt_center.ne'
    exact (hG.nonabelian (center_eq_top_iff.mp hc)).elim
  · exact htop

private theorem central_involution_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G) :
    ∃ z : G, z ∈ d.Z ∧ z ≠ 1 ∧
      generalizedFitting (centralizer ({z} : Set G)) =
        pCore 2 (centralizer ({z} : Set G)) := by
  have hZ : Nat.card d.Z = 2 := d.action.card_centralInvolutions d.T d.sylow_le
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := d.Z) 2 (by rw [hZ])
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hTC : (d.T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  refine ⟨z, z.property, ?_, ?_⟩
  · intro he
    simp [he] at hzG
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le d.T
        (hG.evenCharacteristic d.T) (isTwoLocal_involution_centralizer hzG) hTC))

/-- All original ambient, model, fusion-inside and index inputs are discharged.
Only the literal field-coset and mixed odd-core/Sylow-three source rows remain. -/
theorem Reduction.field_exclusion_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (r : Reduction d I L) (h : Setup d I L)
    (hcoset : ∀ x : G, orderOf x = 2 → x * (r.sylow.lift.dihedral.halfTurn : G)⁻¹ ∈ L →
      IsConj x (r.sylow.lift.dihedral.halfTurn : G))
    (eO : pPrimeCore 2 (I ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G) ≃* ElementaryNine)
    (P : Sylow 3 (I ⊓ centralizer
      ({(r.sylow.lift.dihedral.firstReflection : G) *
        (r.sylow.lift.dihedral.halfTurn : G)} : Set G) : Subgroup G))
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (he : ∀ x : P, x ^ 3 = 1) : False := by
  obtain ⟨z, hzmem, hzne, hz⟩ := central_involution_data hG d
  have hf : orderOf (r.sylow.lift.dihedral.halfTurn : G) = 2 :=
    (Subgroup.orderOf_coe r.sylow.lift.dihedral.halfTurn).trans
      r.sylow.lift.dihedral.halfTurn_order
  exact r.field_exclusion_of_source h
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (ambient_twoPerfect hG) z hzmem hzne hz hcoset
    (r.coverData.component_index_center_centralizer s h r.normalizer_eq)
    eO (hG.involution_centralizer_sqtk hf) P hc he

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
