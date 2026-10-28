module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The original centralizer module for the solvable branch

For the original central involution z, put H=C_G(z) and
V_H=⟨Ω₁(Z(T))^H⟩. The original Sylow subgroup lies in H, and the
involution makes H two-local. Characteristic-two inheritance and the
central-seed form of B.2.14 therefore make this literal V_H two-reduced
in H, with the actual quotient H/C_H(V_H).

The five-dimensional marking puts C_V(L) in Ω₁(Z(T)), hence in V_H.
Its known full centralizer is M=N_G(L), so C_G(V_H)≤M. Reducedness
also gives O₂(H)≤C_G(V_H), establishing O₂(H)≤M. These supply the
module and centralizer inputs for the application of 13.4.8 to H=C_G(z).
The local-product proof and its C₃-chamber application remain with this
solvable-branch owner; the earlier Chapter12 inputs retain final discharge
with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, B.2.14 and the opening of 13.4.9, printed
pp.78 and906; the local-product argument is 13.4.8, pp.904–905.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual omega-center orbit in the full centralizer C_G(z). -/
def centralizerOmegaOrbit (T : Sylow 2 G) (z : G) : Subgroup G :=
  conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (centralizer ({z} : Set G))

omit [Finite G] in
/-- The original chamber Sylow subgroup lies in the centralizer of z. -/
theorem original_sylow_le_centralizer {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht)

omit [Finite G] in
/-- The ambient conjugate span is contained in its original acting group. -/
theorem centralizerOmegaOrbit_le {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    centralizerOmegaOrbit T z ≤ centralizer ({z} : Set G) := by
  apply conjugateSpanBy_le _ (centralizer ({z} : Set G)).le_normalizer
  intro w hw
  exact original_sylow_le_centralizer hz ((mem_omegaOneCenterAmbient_iff _ _).mp hw).1

/-- The nontrivial involution supplies a two-local overgroup of the original T. -/
theorem centralizer_mem_HOver {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) ∈ Chapter1.HOver G (T : Set G) := by
  refine ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer ?_),
    original_sylow_le_centralizer hz⟩
  exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1

/-- The literal source V_H is reduced in the full original involution centralizer. -/
theorem centralizerOmegaOrbit_reduced (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    IsPReduced 2 ((centralizerOmegaOrbit T z).subgroupOf (centralizer ({z} : Set G))) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (T : Subgroup G)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  apply reduced_conjugateSpan_of_sylow_central T _ _
    (original_sylow_le_centralizer hz)
  · exact fun _ hw => ((mem_omegaOneCenterAmbient_iff _ _).mp hw).1
  · exact fun _ hw => ((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2
  · exact Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T)
      (centralizer_mem_HOver hz hz1))

/-- The same ambient conjugate span lies in the actual two-core of C_G(z). -/
theorem centralizerOmegaOrbit_le_core (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    centralizerOmegaOrbit T z ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  have hh := map_mono (f := (centralizer ({z} : Set G)).subtype)
    (centralizerOmegaOrbit_reduced h₀ hz hz1).le_pCore
  rw [map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz)] at hh
  exact hh

/-- The original fixed line belongs to the seed, and hence to V_H. -/
theorem fixed_le_centralizerOmegaOrbit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) :
    V ⊓ centralizer (L : Set G) ≤ centralizerOmegaOrbit T z := by
  apply le_trans _ (le_conjugateSpanBy _ _)
  intro d hd
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  let := D.elementary
  refine ⟨D.le_sylow hd.1, elemPow_eq_one_of_isElementaryAbelian d hd.1, ?_⟩
  intro t ht
  exact (normalizer_component_le_fixed_centralizer h structural D m
    (D.sylow_normalizes_component ht) d hd).symm

/-- Its full ambient centralizer lies in the original component normalizer.
This is the specialized centralizer bound used in 13.4.8. -/
theorem centralizerOmegaOrbit_centralizer_le_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) :
    centralizer (centralizerOmegaOrbit T z : Set G) ≤ normalizer (L : Set G) := by
  rw [← fixed_centralizer_eq_normalizer h structural D m]
  exact centralizer_le (fixed_le_centralizerOmegaOrbit h structural D m z)

/-- The actual two-core of the escaping centralizer is already contained in M. -/
theorem centralizer_core_le_normalizer
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤ normalizer (L : Set G) := by
  apply le_trans _ (centralizerOmegaOrbit_centralizer_le_normalizer h structural D m z)
  apply le_centralizer_iff.mp
  intro w hw y hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact congrArg Subtype.val ((centralizerOmegaOrbit_reduced h₀ hz hz1).le_centralizer_pCore
    (show (⟨w, centralizerOmegaOrbit_le hz hw⟩ : centralizer ({z} : Set G)) ∈
      (centralizerOmegaOrbit T z).subgroupOf (centralizer ({z} : Set G)) from hw) a ha)

/-- The literal centralizer and its literal omega orbit satisfy the module
hypotheses of 13.4.8 before any solvable structure theorem is applied. -/
theorem source_centralizer_module (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (hz : z ∈ V ⊓ omegaOneCenterAmbient (T : Subgroup G))
    (hout : z ∉ centralizer (L : Set G)) :
    centralizer ({z} : Set G) ∈ Chapter1.HOver G (T : Set G) ∧
    IsPReduced 2 ((centralizerOmegaOrbit T z).subgroupOf (centralizer ({z} : Set G))) ∧
    V ⊓ centralizer (L : Set G) ≤ centralizerOmegaOrbit T z ∧
    z ∈ centralizerOmegaOrbit T z ∧
    centralizerOmegaOrbit T z ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  have hz1 : z ≠ 1 := fun he => hout (he ▸ one_mem _)
  exact ⟨centralizer_mem_HOver hz.2 hz1,
    centralizerOmegaOrbit_reduced h₀ hz.2 hz1,
    fixed_le_centralizerOmegaOrbit h structural D m z,
    le_conjugateSpanBy _ _ hz.2, centralizerOmegaOrbit_le_core h₀ hz.2 hz1⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
