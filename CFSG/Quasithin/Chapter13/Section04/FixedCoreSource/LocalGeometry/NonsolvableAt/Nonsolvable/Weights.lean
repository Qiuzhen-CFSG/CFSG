module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Weights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.Representation.BinaryPermutation.SixConstantWeight

/-!
# Weight and centralizer transport in the original fixed core: structure at the original group

The all-one coordinate word is the actual generator of C_V(L). Equal-weight
vectors are conjugate by elements of the original L, through the literal
L/centralCore L marking. Consequently containment of their full ambient
centralizers in N_G(L) is constant on each weight class.

After source 13.4.12 supplies a unique escaping vector in V∩Ω₁Z(T), its
product with the fixed generator is the other Sylow-central weight choice.
Uniqueness and the fixed-generator centralizer theorem therefore force every
escaping nonidentity vector of V to have the same weight. The proof of
13.4.12 remains with qt-d-1341-nonsolvable-source; this is its conditional
weight-transport consumer, not a proof of that uniqueness assertion.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/Weights` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
namespace CoreMarking
variable {D : ChosenModule T L V} (m : CoreMarking D)

variable [Finite G]

/-- Source 13.4.12 uniqueness propagates to every vector of the original core.
The second Sylow-central choice is the actual product with the fixed generator. -/
theorem escape_has_unique_weight_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (v : V) (hv1 : v ≠ 1)
    (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
    m.weight v = m.weight z := by
  have nonfixed (u : V) (hu : u ≠ 1)
      (hout : ¬ centralizer ({u.val} : Set G) ≤ normalizer (L : Set G)) :
      u.val ∉ centralizer (L : Set G) := by
    intro hf
    exact hout (fixed_generator_centralizer_at h structural D m ⟨u.property,hf⟩
      (fun he => hu (Subtype.ext he))).le
  have hzwt := m.nonfixed_weight z (nonfixed z hz1 hzout)
  have hvwt := m.nonfixed_weight v (nonfixed v hv1 hvout)
  have hdT : m.constant.val ∈ centralizer (T : Set G) := by
    have hh : (T : Subgroup G) ≤ centralizer (V ⊓ centralizer (L : Set G) : Set G) :=
      D.sylow_normalizes_component.trans (normalizer_component_le_fixed_centralizer_at h structural D m)
    apply mem_centralizer_iff.mpr
    intro t ht
    exact (mem_centralizer_iff.mp (hh ht) m.constant.val
      ⟨m.constant.property,m.constant_fixed⟩).symm
  have hwT : (z * m.constant).val ∈ centralizer (T : Set G) :=
    (centralizer (T : Set G)).mul_mem ((mem_omega_iff (D := D) z).mp hzT) hdT
  have hww := m.weight_mul_constant z
  have hw1 : z * m.constant ≠ 1 := by
    intro he
    rw [he, m.weight_one] at hww
    omega
  have hwz : z * m.constant ≠ z := by
    intro he
    rw [he] at hww
    omega
  have hwc : centralizer ({(z * m.constant).val} : Set G) ≤ normalizer (L : Set G) := by
    by_contra hh
    exact hwz (hunique _ hw1 ((mem_omega_iff (D := D) _).mpr hwT) hh)
  by_contra hne
  have he : m.weight v = m.weight (z * m.constant) := by omega
  exact hvout ((m.centralizer_le_iff_of_weight_eq v _ he).mpr hwc)

end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
