module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.FusionFields
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.SourceIrreducible

/-!
# Source recognition with the actual irreducible branch discharged

The actual earlier action excludes the irreducible minimal-normal branch.
The proved G.6.4 supplies the two surviving constituent models. Their literal
coordinates, actor recognition, source Sylow coset and power form give the
recognition fields consumed by the 15.3.50 fusion assembly. No classification
or recognition callback remains in this source-facing theorem.
Source: Aschbacher–Smith 15.3.57–58, printed pp.1148–1149.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {v : ActorQuotient Z} {s : ℕ}

/-- Recognize the source natural and dual pair without a classification premise. -/
theorem naturalPair_of_source
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    (a : EarlierActionInputs d) : Nonempty (NaturalPair d a) :=
  naturalPair_of_local_exclusion d a (fun _ hK hi => a.not_irreducible hK hi)

/-- All literal fusion recognition fields, with both classification branches proved. -/
theorem fusionRecognition_of_source
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    (a : EarlierActionInputs d) (b : EarlierPowerInputs d a)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hUT : closureU Z ZS ≤ (d.T : Subgroup G))
    (hcomm : ⁅closureU Z ZS, V⁆ ≤ V)
    (hindex : (closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))).relIndex
      (d.T : Subgroup G) = 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hout : t ∉ closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))) :
    s = 1 ∧ Nonempty (FusionRecognition (d.T : Subgroup G) Z ZS V t) := by
  obtain ⟨p⟩ := naturalPair_of_source d a
  exact ⟨p.s_eq_one, ⟨fusionRecognition p b hUQ hUT hcomm hindex t ht hout⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
