module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.SourceInputs
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalGeometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.WeakClosure
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.CriticalPair
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Assembly

/-!
# Conditional assembly of the original 12.4.1 conjugate

Select an escaping H-star subgroup, use its literal Omega-center module
parameter bound to place W₀(T,V) in O₂(H), and apply the actual F.7 geometry
of LT and H. The resulting conjugator maps from ⟨LT,H⟩ to G and has the
exact nontrivial mutual-normalization commutator required by Contracts.
The final theorem applies this to the existing symmetric-plane consumer.

LocalSelectionSource and LocalParameterSource are still producer obligations.
Neither this conditional theorem nor its build discharges them; final
12.4.1 assembly must supply both. The permitted Structural1222 source input
remains explicit. No later fusion contradiction is used.
Source: Aschbacher–Smith, 12.4.1, printed p.812, using E.3.6/10 and F.7.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open Section02 SmallFusion ChapterE ConjugateExistence
universe u

/-- The original coset-geometry argument, conditional on its two remaining
earlier local inputs. It does not use the later fusion contradiction. -/
theorem noncommutingConjugate1241_of_local_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (selection : LocalSelectionSource.{u}) (parameters : LocalParameterSource.{u}) :
    NoncommutingConjugate1241.{u} := by
  intro X _ _ T L V h D hmodel hne hZ
  let _ := D.elementary
  intro hs
  obtain ⟨H, hH⟩ := selection X T L V h D hmodel hne hZ hs
  have P := parameters X T L V h D hmodel hne hZ H hH
  let _ := P.elementary
  have hTH : (T : Subgroup X) ≤ H := hH.1.1.2
  have hHM : ¬ H ≤ normalizer (L : Set X) := hH.1.2
  have hW := weakClosure_le_core_of_parameter_bound V (localModule T H) H T
    hTH (localModule_normalized T H) P.centralizer_le_core P.parameter hs
  let A := localGeometry h D structural hTH hHM
  let J := L ⊔ (T : Subgroup X) ⊔ H
  have hseed : A.seed.map J.subtype = V :=
    localGeometry_seed_map h D structural hTH hHM
  have hsyl : ((A.sylow false : Subgroup (localFamily T L H false)).map
      (localFamily T L H false).subtype).map J.subtype = (T : Subgroup X) :=
    localGeometry_sylow_map h D structural hTH hHM
  have hsecond : (localFamily T L H true).map J.subtype = H :=
    map_subgroupOf_eq_of_le le_sup_right
  have hw : indexedWeakClosure (A.seed.map J.subtype)
      (((A.sylow false : Subgroup (localFamily T L H false)).map
        (localFamily T L H false).subtype).map J.subtype) 0 ≤
      ((localFamily T L H true).map J.subtype).pCoreIn 2 := by
    rw [hseed, hsyl, hsecond]
    exact hW
  have hc := exists_ambient_conjugate_of_weakClosure_core A
    (localGeometry_ne_bot h D structural hTH hHM) J.subtype J.subtype_injective hw
  rwa [hseed] at hc

/-- Application to the original symmetric-plane consumer. The local source
inputs remain explicit until their producers discharge them. -/
theorem source_commutator_plane_of_local_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (centralizers : HyperplaneCentralizers1248.{u})
    (selection : LocalSelectionSource.{u}) (parameters : LocalParameterSource.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked normalizerAction centralizers
    (noncommutingConjugate1241_of_local_sources structural selection parameters)
    T L V h D hmodel hne

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
