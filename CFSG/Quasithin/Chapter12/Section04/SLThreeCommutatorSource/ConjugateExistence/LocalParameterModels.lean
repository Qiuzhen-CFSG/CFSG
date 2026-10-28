module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterMoved
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive.Double
public import CFSG.Quasithin.Chapter6.SourceDefs
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterApplication

/-!
# The parameter consequence of the one-or-two A₅ alternative

The actual conjugation model includes K/O₂(K) and equivariant coordinates
on the original commutator subgroup. Both copies use the same marking.
The full normalizer bounds therefore apply to every outer H-actor. The
moved-submodule restriction then gives the bound on the whole V_H=V_K.
This proves the representation-theoretic consequence of 12.3.2, not the
classification that produces its alternatives. That classification remains
with qt-d-1241-l3-conjugate, including the original A₇ exclusion where needed.
Source: Aschbacher–Smith, 12.3.2 and 12.4.1, printed pp.807,812.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 ChapterE SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

omit [Finite G] in
private def modelSection (K W : Subgroup G) (hWK : W ≤ K)
    (hn : K ≤ normalizer (W : Set G))
    {A S : Type*} [Group A] [AddCommGroup S] [Module (ZMod 2) S]
    (ρ : Representation (ZMod 2) A S)
    (e : (K ⧸ pCore 2 K) ≃* A) (b : W ≃* Multiplicative S)
    (hb : ∀ (k : K) (w : W),
      ((b.symm (Multiplicative.ofAdd (ρ (e (QuotientGroup.mk' (pCore 2 K) k)) (b w).toAdd))) : G) =
        (k : G) * (w : G) * (k : G)⁻¹) :
    Representation.BinaryConjugationSection K W ⊥
      (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) := by
  refine ⟨hWK,bot_le,hn,b.toMonoidHom,b.surjective,?_,?_⟩
  · rw [b.toMonoidHom.ker_eq_bot b.injective,bot_subgroupOf]
  · intro k w
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    change b.symm (b _) = _
    rw [b.symm_apply_apply]
    exact Subtype.ext (hb k w).symm

omit [Finite G] in
/-- The original moved subgroup lies in the embedded two-residual. -/
theorem localMoved_le_residual (hTH : (T : Subgroup G) ≤ H) :
    localMoved T H ≤ localResidual H :=
  le_normalizer_iff_commutator_le_right.mp
    ((localModule_le hTH).trans (localResidual_normalized H))

/-- The escaping residual moves the seed, so the zero-copy alternative is absent. -/
theorem localMoved_ne_bot
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    localMoved T H ≠ ⊥ := by
  intro hb
  have hc : localModule T H ≤ centralizer (localResidual H : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hb
  exact localResidual_not_centralizes_seed hTM hZ hH
    ((le_centralizer_iff.mp hc).trans (centralizer_le (le_conjugateSpanBy _ _)))

/-- Both source A₅ module alternatives give the bound on the actual whole
local action, including its fixed summand and every outer H-actor. -/
theorem localModule_parameter_of_one_or_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (localModule T H)]
    (hm : Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
      ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆) :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  have hmodel : Chapter6.Source.IsOneOrTwoA5Modules (localResidual H) (localMoved T H) := by
    simpa only [localMoved,localModule_eq_residual_span hH.1.1.2] using hm
  have hn : localResidual H ≤ normalizer (localMoved T H : Set G) :=
    (map_subtype_le _).trans (localMoved_normalized T H)
  rcases hmodel with ⟨e,b,hb⟩ | ⟨e,b,hb⟩
  · let c := modelSection _ _ (localMoved_le_residual hH.1.1.2) hn _ e b hb
    exact localModule_parameter_of_single_deleted h hH _
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) c
  · let c := modelSection _ _ (localMoved_le_residual hH.1.1.2) hn _ e b hb
    let : IsElementaryAbelian 2 (localMoved T H) := IsElementaryAbelian.of_le (localMoved_le T H)
    exact (localModule_parameter_le_moved h hH).trans
      (moduleA_local_double_section_le_one _ _ _ _
        (e.surjective.comp (QuotientGroup.mk'_surjective _)) c (map_subtype_le _)
        (inf_le_left.trans (localResidual_normalized H)))

/-- The nonzero alternatives of printed 12.3.2. The zero-copy case is
excluded by localMoved_ne_bot under the source normalizer and escape guards. This remains a source input,
not a proved classification. In particular its residual quotient uses O₂(K). -/
def LocalClassification1232 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L : Subgroup X),
    Hypothesis1223 KnownSimple.IsKnownSimple T L →
    centralizer (sylowCenterSeed T : Set X) ≤ normalizer (L : Set X) →
    ∀ H : Subgroup X, H ∈ Chapter3.HStar (T : Subgroup X) (normalizer (L : Set X)) →
      Group.IsSolvable H ∨
        (Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) ∧
          FaithfulMaximalLocal T (localResidual H) ∧
          Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
            ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆)

/-- The numerical consequence of source 12.3.2 has no local action callbacks. -/
theorem localModule_parameter_of_classification
    (classification : LocalClassification1232.{u})
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (localModule T H)] :
    moduleA ((automizerRepresentation (localModule T H)).comp
      (inducedAutomizer (localModule T H) H).subtype) ≤ 1 := by
  rcases classification G T L h hZ H hH with hs | ⟨_,_,hm⟩
  · exact localModule_parameter_of_solvable h hH hs
  · exact localModule_parameter_of_one_or_two h hH hm
/-- The genuine classification suffices for the remaining nonsolvable input;
all representation and fixed-layer premises have been discharged here. -/
theorem nonsolvableLocalParameterSource_of_classification
    (classification : LocalClassification1232.{u}) : NonsolvableLocalParameterSource.{u} := by
  intro X _ _ T L V h D hmodel hne hZ H hH hns
  let := localModule_elementary h hH
  exact localModule_parameter_of_classification classification h hZ hH

/-- Source 12.3.2 through the literal 12.4.1 conjugator. Classification remains
with this task; SelectionSource.localSelectionSource supplies selection. -/
theorem noncommutingConjugate1241_of_classification
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (selection : LocalSelectionSource.{u})
    (classification : LocalClassification1232.{u}) : NoncommutingConjugate1241.{u} :=
  noncommutingConjugate1241_of_nonsolvable_parameters structural selection
    (nonsolvableLocalParameterSource_of_classification classification)

/-- The symmetric-plane consumer after the exact classification has been supplied.
The final 12.4.2 owner discharges the earlier structural inputs. -/
theorem source_commutator_plane_of_classification
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u}) (centralizers : HyperplaneCentralizers1248.{u})
    (selection : LocalSelectionSource.{u}) (classification : LocalClassification1232.{u})
    {V : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane_of_nonsolvable_parameters structural marked normalizerAction centralizers
    selection (nonsolvableLocalParameterSource_of_classification classification) h D hmodel hne
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
