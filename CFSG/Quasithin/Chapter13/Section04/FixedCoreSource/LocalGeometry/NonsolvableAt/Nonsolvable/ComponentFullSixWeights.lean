module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductWeight

/-!
# Original centralizer amalgams at both escaping weights: structure at the original group

The tetrahedral orbit calculation excludes the product commutator bound
at weight two. Apply this to the constructed ordinary A₆ centralizer pair:
its join is therefore N_G(J(T)), is maximal two-local, has the actual
L₃(2) quotient, and has a unique outside parabolic.

For two escaping vectors of weights two and four, the marked Sylow action
identifies their original invariant planes, so both joins use the same
literal B=L₂T. Their outside parabolics are distinct because their fixed
lines on V∩Ω₁Z(T) are distinct. They cannot both lie in N_G(J(T)); hence
the weight-four join takes the product alternative. Its commutator bound
and the actual Sylow supplement give B≤N_G(O²(P₄)).

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ComponentFullSixWeights` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Outside parabolics at distinct escaping weights have different fixed lines. -/
theorem different_weight_parabolics_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z w : V) (hz : m.weight z = 2) (hw : m.weight w = 4)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P Q : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hQ : Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G))
    (hQw : Q ≤ centralizer ({w.val} : Set G)) : P ≠ Q := by
  classical
  have hz1 : z ≠ 1 := by intro he; rw [he,m.weight_one] at hz; omega
  have hw1 : w ≠ 1 := by intro he; rw [he,m.weight_one] at hw; omega
  intro he
  have hp := m.central_four_fixed_of_escape_at h structural z hz1 hzT P hPz hP.1.2
  have hq := m.central_four_fixed_of_escape_at h structural w hw1 hwT Q hQw hQ.1.2
  have hlines : zpowers z.val = zpowers w.val := by rw [←hp,←hq,he]
  have hm : z.val ∈ zpowers w.val := hlines ▸ mem_zpowers z.val
  let := D.elementary
  have ho : orderOf w.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian w.val w.property)
    (fun he => hw1 (Subtype.ext he))
  rw [mem_zpowers_iff_mem_range_orderOf,ho] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact hz1 (Subtype.ext (by simpa using he.symm))
  · have hzw : z = w := Subtype.ext (by simpa using he.symm)
    rw [hzw,hw] at hz
    omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
