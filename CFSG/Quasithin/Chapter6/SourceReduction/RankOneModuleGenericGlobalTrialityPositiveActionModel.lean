module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralParametersModel
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Generation
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Actions
import all Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Generation

/-!
# The full positive action from the compatible triality root frame

The central reflection takes short root zero to short root one; the arms
reflection then gives short root two, with the actual Frobenius rotation.
The corresponding two steps give the remaining long roots. Membership in
the equalizers of two local maps transports across the literal Borel at
each step. The six-factor positive normal form therefore proves agreement
on the whole positive subgroup without a full-carrier extension premise.

Surjectivity of the genuine torus characters realizes the two root scalars.
Consequently compatible scalar-semilinear signed-root formulas give exactly
a torus conjugation followed by the common coefficient action on U. The
source companion uses this identity in the original centralizer bound.

Source: GLS3 §§2.3--2.6 and Steinberg Theorems 30 and 36
(`refs/KGroup/GLS3/Chapter2St1.tex`); Aschbacher--Smith F.4.37--38
(`refs/quasithin.pdf`). The internal Generation import reuses its proved
folded Weyl identities and positive normal form within this root calculation.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open Triality.Standard.OuterOdd.Coverage.RootGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCentralAction
open TrialityLocalParameters

private theorem short_borel (P : Parameters) (hp : P.prime=2) (i : Fin 3) (t : ExtensionField P) :
    short P hp i t ∈ borel P :=
  unipotent_le_borel P (descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
    (short_mem P hp .central i trivial t))
private theorem long_borel (P : Parameters) (hp : P.prime=2) (i : Fin 3) (t : fixedField P) :
    long P hp i t ∈ borel P :=
  unipotent_le_borel P (descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
    (long_mem P hp .arms i trivial t))

private theorem compatible_positive_generation (n : ℕ) (hn : 0<n)
    (K : Node → Subgroup (Carrier (binaryParameters n hn)))
    (hB : ∀ x∈borel (binaryParameters n hn), x∈K .central ↔ x∈K .arms)
    (hroots : ∀ s i r, ConcreteBruhat.rootElement (binaryParameters n hn) rfl s i r∈K i) :
    unipotent (binaryParameters n hn) ≤ K .arms := by
  let P := binaryParameters n hn
  have hp : P.prime=2 := rfl
  have hw (i) : simpleRepresentative P hp i∈K i := by
    rw [simpleRepresentative_eq_root_word]
    exact mul_mem (mul_mem (hroots true i 1) (hroots false i 1)) (hroots true i 1)
  have hs0 (t) : short P hp 0 t∈K .arms := by
    rw [short_zero_eq]
    exact hroots true .arms t
  have hs1 (t) : short P hp 1 t∈K .arms := by
    apply (hB _ (short_borel P hp 1 t)).mp
    have he : simpleRepresentative P hp .central * short P hp 0 t *
        (simpleRepresentative P hp .central)⁻¹=short P hp 1 t := by
      apply FixedDescent.carrierToSplit_injective P hp
      simpa only [map_mul,map_inv,simpleRepresentative,short,
        FixedDescent.carrierToSplit_toCarrier,shortElementary_val] using conjugate_short_zero P hp t
    rw [←he]
    exact mul_mem (mul_mem (hw .central) ((hB _ (short_borel P hp 0 t)).mpr (hs0 t))) (inv_mem (hw .central))
  have hs (i : Fin 3) (t) : short P hp i t∈K .arms := by
    fin_cases i
    · exact hs0 t
    · exact hs1 t
    · have he : simpleRepresentative P hp .arms * short P hp 1 (fieldFrobenius P t) *
          (simpleRepresentative P hp .arms)⁻¹=short P hp 2 t := by
        apply FixedDescent.carrierToSplit_injective P hp
        simpa only [map_mul,map_inv,simpleRepresentative,short,
          FixedDescent.carrierToSplit_toCarrier,shortElementary_val,fieldFrobenius_three] using
          conjugate_short_one P hp (fieldFrobenius P t)
      change short P hp 2 t∈K .arms
      rw [←he]
      exact mul_mem (mul_mem (hw .arms) (hs1 _)) (inv_mem (hw .arms))
  have hl0 (t) : long P hp 0 t∈K .arms := by
    apply (hB _ (long_borel P hp 0 t)).mp
    rw [long_zero_eq]
    exact hroots true .central t
  have hstep (a : Node) (j k : Fin 3) (t : fixedField P)
      (hr : (foldedRootReflection a).val (rootIndex (longPosition j))=rootIndex (longPosition k))
      (hj : long P hp j t∈K a) : long P hp k t∈K a := by
    have he : simpleRepresentative P hp a * long P hp j t *
        (simpleRepresentative P hp a)⁻¹=long P hp k t := by
      apply FixedDescent.carrierToSplit_injective P hp
      simpa only [map_mul,map_inv,simpleRepresentative,long,
        FixedDescent.carrierToSplit_toCarrier,longElementary_val,longSplit] using
        simple_curve P hp a _ _ hr t.val
    rw [←he]
    exact mul_mem (mul_mem (hw a) hj) (inv_mem (hw a))
  have hl1 (t) : long P hp 1 t∈K .arms := hstep .arms 0 1 t arms_long_table (hl0 t)
  have hl (i : Fin 3) (t) : long P hp i t∈K .arms := by
    fin_cases i
    · exact hl0 t
    · exact hl1 t
    · exact (hB _ (long_borel P hp 2 t)).mp
        (hstep .central 1 2 t central_long_table ((hB _ (long_borel P hp 1 t)).mpr (hl1 t)))
  intro g hg
  obtain ⟨x,hx,he⟩ := hg
  obtain ⟨v,hv⟩ := positive_coordinates n hn x hx
  have hm : short P hp 0 (v.1 0)*long P hp 0 (v.2 0)*short P hp 1 (v.1 1)*
      short P hp 2 (v.1 2)*long P hp 1 (v.2 1)*long P hp 2 (v.2 2)∈K .arms :=
    mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hs 0 _) (hl 0 _)) (hs 1 _)) (hs 2 _)) (hl 1 _)) (hl 2 _)
  exact ((positive_factorization P hp x v hv).symm.trans he) ▸ hm

/-- Compatible parabolic maps agreeing with a native action on the four signed
simple roots agree on the entire positive subgroup. -/
theorem positive_action_of_signed_roots (n : ℕ) (hn : 0<n)
    (a : (i : Node) → MulAut (parabolic (binaryParameters n hn) i))
    (k : MulAut (Carrier (binaryParameters n hn)))
    (hB : ∀ x : borel (binaryParameters n hn),
      (a .central (inclusion (borel_le_parabolic _ .central) x)).val=
        (a .arms (inclusion (borel_le_parabolic _ .arms) x)).val)
    (hr : ∀ s i r, (a i (rootInParabolic (binaryParameters n hn) rfl s i r)).val=
      k (ConcreteBruhat.rootElement (binaryParameters n hn) rfl s i r)) :
    ∀ x : parabolic (binaryParameters n hn) .arms, x.val∈unipotent (binaryParameters n hn) →
      (a .arms x).val=k x.val := by
  let P := binaryParameters n hn
  let K (i) : Subgroup (Carrier P) := (MonoidHom.eqLocus
    ((parabolic P i).subtype.comp (a i).toMonoidHom)
    (k.toMonoidHom.comp (parabolic P i).subtype)).map (parabolic P i).subtype
  have hK (i) (x : Carrier P) (hx : x∈parabolic P i) :
      x∈K i ↔ (a i ⟨x,hx⟩).val=k x := by
    change ((parabolic P i).subtype ⟨x,hx⟩)∈K i ↔ _
    rw [mem_map_iff_mem (parabolic P i).subtype_injective]
    rfl
  have hgen : unipotent P ≤ K .arms := compatible_positive_generation n hn K
    (fun x hx => by
      rw [hK .central x (borel_le_parabolic P .central hx),hK .arms x (borel_le_parabolic P .arms hx)]
      exact (congrArg (fun z => z=k x) (hB ⟨x,hx⟩)).to_iff)
    (fun s i r => (hK i _ (rootInParabolic P rfl s i r).property).mpr (hr s i r))
  intro x hx
  exact (hK .arms x.val x.property).mp (hgen hx)

/-- Compatible signed-root formulas determine the whole positive action as
conjugation by an actual torus element followed by the common coefficient map. -/
theorem torus_coefficient_positive_action (n : ℕ) (hn : 0<n)
    (a : (i : Node) → MulAut (parabolic (binaryParameters n hn) i))
    (hB : ∀ x : borel (binaryParameters n hn),
      (a .central (inclusion (borel_le_parabolic _ .central) x)).val=
        (a .arms (inclusion (borel_le_parabolic _ .arms) x)).val)
    (c : (i : Node) → (RootField (binaryParameters n hn) i)ˣ)
    (σ : CoefficientAut (binaryParameters n hn))
    (hr : ∀ s i r, a i (rootInParabolic (binaryParameters n hn) rfl s i r)=
      rootInParabolic (binaryParameters n hn) rfl s i
        (signedScalar s (c i).val*coefficientRootField (binaryParameters n hn) σ i r)) :
    ∃ g : torus (binaryParameters n hn),
      let gP : parabolic (binaryParameters n hn) .arms := inclusion
        ((torus_le_borel _).trans (borel_le_parabolic _ .arms)) g
      ∀ x : parabolic (binaryParameters n hn) .arms,
        x.val∈unipotent (binaryParameters n hn) →
          a .arms x=gP*coefficientParabolic (binaryParameters n hn) σ .arms x*gP⁻¹ := by
  let P := binaryParameters n hn
  have hp : P.prime=2 := rfl
  obtain ⟨g,hg,hgs⟩ := exists_torus_scalars P hp c
  let k := MulAut.conj g*coefficientAction P σ
  have hrs (s i r) : (a i (rootInParabolic P hp s i r)).val=
      k (ConcreteBruhat.rootElement P hp s i r) := by
    rw [hr]
    change ConcreteBruhat.rootElement P hp s i _=g*coefficientAction P σ
      (ConcreteBruhat.rootElement P hp s i r)*g⁻¹
    rw [coefficientAction_rootElement,hgs]
  have hpos := positive_action_of_signed_roots n hn a k hB hrs
  refine ⟨⟨g,hg⟩,?_⟩
  dsimp only
  intro x hx
  exact Subtype.ext (hpos x hx)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCentralAction
