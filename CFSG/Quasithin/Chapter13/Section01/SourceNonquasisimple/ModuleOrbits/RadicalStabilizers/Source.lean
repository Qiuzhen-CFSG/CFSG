module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.Models
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Preparation

/-!
# Original radical irreducibility from the moved-module stabilizers

The S₃ stabilizer has a double cover of order twelve in the original odd
Frattini action, prime to p>3. The A₄, S₄ and four-group stabilizers lift a
four-group to Q₈. The Sylow-image alternative inherits the original
component Sylow action. Thus the actual stabilizer alternatives prove
13.1.12(1), including its local quaternion conclusion outside the S₃ case.
No arbitrary nonabelian subgroup of GL₂(p) is used as an irreducibility
criterion.

The source chooses C_T(u) Sylow in C_{N_G(L)}(u). We retain that choice for
the literal Q₈ in the action of C_T(u)∩L. Irreducibility alone transports to
every nonidentity moved vector: conjugate both the point centralizer and an
invariant subgroup of the same Frattini quotient by the selected element of
N_G(L). The S₅ application uses its proved centralizer_orbit calculation.

The final TI applications discharge the radical-action premise of the
existing 13.1.13 consumer. Orbit-model construction and the centralizer
containment in 13.1.12(3) remain independent source inputs; none of the
stabilizer alternatives assumes a radical-action conclusion.

Source: Aschbacher--Smith, 13.1.12(1) and 13.1.13, printed pp.872--875.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G]

/-- Transport on the literal odd Frattini quotient through an element of N_G(L). -/
theorem radical_irreducible_of_conjugate (L : Subgroup G) (p : ℕ) (u : G)
    (g : normalizer (L : Set G))
    (hi : RadicalCentralizerIrreducible L p ((g : G) * u * (g : G)⁻¹)) :
    RadicalCentralizerIrreducible L p u := by
  let M := normalizer (L : Set G)
  let ρ := xiFrattiniAction M (XiP p L) (XiP_invariant p le_rfl)
  intro A hA
  have hb : ∀ s : (M ⊓ centralizer ({(g : G) * u * (g : G)⁻¹} : Set G) : Subgroup G),
      ∀ a ∈ A.map (ρ g).toMonoidHom, xiFrattiniAction
        (M ⊓ centralizer ({(g : G) * u * (g : G)⁻¹} : Set G)) (XiP p L)
        (XiP_invariant p inf_le_left) s a ∈ A.map (ρ g).toMonoidHom := by
    intro s a ha
    obtain ⟨b,hb,rfl⟩ := ha
    let sM : M := ⟨s,s.property.1⟩
    let tM : M := g⁻¹ * sM * g
    have ht : (tM : G) ∈ centralizer ({u} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hc := congrArg (MulAut.conj (g : G)⁻¹)
        (mem_centralizer_singleton_iff.mp s.property.2)
      simpa only [map_mul,MulAut.conj_apply,inv_inv,mul_assoc,
        inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel_right,inv_mul_cancel_right,
        inv_mul_cancel,mul_inv_cancel,mul_one,one_mul,
        tM,sM,Subgroup.coe_mul,Subgroup.coe_inv] using hc
    let t : (M ⊓ centralizer ({u} : Set G) : Subgroup G) := ⟨tM,tM.property,ht⟩
    have hat : ρ tM b ∈ A := by
      have hh := hA t b hb
      rw [xiFrattiniAction_restrict inf_le_left (XiP_invariant p le_rfl)] at hh
      exact hh
    refine ⟨ρ tM b,hat,?_⟩
    rw [xiFrattiniAction_restrict inf_le_left (XiP_invariant p le_rfl)]
    change (ρ g) ((ρ (g⁻¹ * sM * g)) b) = (ρ sM) ((ρ g) b)
    simp only [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply]
    exact (ρ g).apply_symm_apply _
  rcases hi (A.map (ρ g).toMonoidHom) hb with he | he
  · exact Or.inl ((Subgroup.map_injective (f := (ρ g).toMonoidHom) (ρ g).injective)
      (he.trans (Subgroup.map_bot _).symm))
  · apply Or.inr
    apply Subgroup.map_injective (f := (ρ g).toMonoidHom) (ρ g).injective
    exact he.trans (Subgroup.map_top_of_surjective (ρ g).toMonoidHom
      (ρ g).surjective).symm

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits



open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
open SourceCentralizerStructure.Elimination
variable {G : Type*} [Group G] [Finite G]

/-- The actual component images in the source branches with a local Q₈ lift. -/
@[expose] def QuaternionStabilizerAlternative (T : Sylow 2 G) (L : Subgroup G)
    (u : normalizerMoved L) : Prop :=
  Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L)) ≃* alternatingGroup (Fin 4)) ∨
  Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L)) ≃* Equiv.Perm (Fin 4)) ∨
  (Nat.card (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L)) = 4 ∧
    ∀ a : (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)), a ^ 2 = 1) ∨
  IsSylowIn 2
    (((((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) (componentImage L)

/-- The source point-stabilizer alternatives, as models of the actual moved action. -/
@[expose] def ComponentStabilizerAlternative (T : Sylow 2 G) (L : Subgroup G)
    (u : normalizerMoved L) : Prop :=
  Nonempty ((((centralizer ({(u : G)} : Set G)).subgroupOf L).map
    (componentAction L)) ≃* Equiv.Perm (Fin 3)) ∨
  QuaternionStabilizerAlternative T L u

/-- The nonsymmetric-three alternatives give both irreducibility and a faithful
Q₈ in the original action of C_T(u)∩L, with the local Sylow choice retained. -/
theorem radical_actions_of_quaternion_stabilizer
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (h : Context T L p) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hm : QuaternionStabilizerAlternative T L u) :
    RadicalCentralizerIrreducible L p u ∧
      ∃ f : QuaternionGroup 2 →* (xiFrattiniAction
        (((T : Subgroup G) ⊓ L) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
        (inf_le_left.trans (inf_le_right.trans (XiP_invariant p L.le_normalizer)))).range,
        Function.Injective f := by
  rcases hm with ha | hs | ⟨hc,he⟩ | hy
  · exact (radical_actions_of_component_alternating_four h.hypothesis h.many h.maximal
      h.nonquasisimple h.odd h.divides u hlocal ha).2
  · exact (radical_actions_of_component_symmetric_four h.hypothesis h.many h.maximal
      h.nonquasisimple h.odd h.divides u hlocal hs).2
  · exact (radical_actions_of_component_four_group h.hypothesis h.many h.maximal
      h.nonquasisimple h.odd h.divides u hlocal hc he).2
  · exact radical_actions_of_local_sylow_image h.hypothesis h.maximal h.nonquasisimple
      h.odd h.divides u hy

/-- The radical-action implication of 13.1.12(1) for every supplied source model. -/
theorem radical_irreducible_of_component_stabilizer
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (h : Context T L p) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hm : ComponentStabilizerAlternative T L u) : RadicalCentralizerIrreducible L p u := by
  rcases hm with hs | hq
  · exact (radicalCentralizerIrreducible_of_component_symmetric_three
      h.hypothesis h.many h.maximal h.nonquasisimple h.odd h.divides u hs).2
  · exact (radical_actions_of_quaternion_stabilizer h u hlocal hq).1

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits

namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Subgroup Theory.GroupTheory
open Chapter1 Chapter1.Section02 Chapter12.Section02
open SourceCentralizerStructure.Elimination
variable {G : Type*} [Group G] [Finite G]

/-- The source representative choice suffices for irreducibility at every moved vector. -/
theorem radical_irreducible_of_selected
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} (h : Context T L p)
    (hi : ∀ v : G, Selected T L v → RadicalCentralizerIrreducible L p v)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    RadicalCentralizerIrreducible L p u := by
  obtain ⟨g,hg,hs⟩ := h.exists_selected hu hne
  exact radical_irreducible_of_conjugate L p u ⟨g,hg⟩ (hi _ hs)

/-- All nonidentity moved vectors satisfy the radical-action conclusion once
the source stabilizer models are supplied on selected noncentral representatives. -/
theorem radical_irreducible_of_stabilizer_models
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (h : Context T L p)
    (hm : ∀ v : normalizerMoved L, Selected T L (v : G) →
      ¬ (T : Subgroup G) ≤ centralizer ({(v : G)} : Set G) →
      ComponentStabilizerAlternative T L v)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    RadicalCentralizerIrreducible L p u := by
  apply radical_irreducible_of_selected h _ hu hne
  intro v hs
  by_cases ht : (T : Subgroup G) ≤ centralizer ({v} : Set G)
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.hypothesis.simpleQTKE
      h.maximal.1.1 h.nonquasisimple h.odd h.divides ht
  · exact radical_irreducible_of_component_stabilizer h ⟨v,hs.mem⟩ hs.local_sylow
      (hm ⟨v,hs.mem⟩ hs ht)

/-- Discharge the radical-action input of the literal TI consumer; only the
independent source centralizer-containment input remains alongside the models. -/
theorem ti_of_stabilizer_models
    {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (h : Context T L p)
    (hm : ∀ v : normalizerMoved L, Selected T L (v : G) →
      ¬ (T : Subgroup G) ≤ centralizer ({(v : G)} : Set G) →
      ComponentStabilizerAlternative T L v)
    (hc : ∀ v : G, Selected T L v →
      centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply normalizerMoved_ti_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides
  · exact fun _ hu hne _ => radical_irreducible_of_stabilizer_models h hm hu hne
  · exact fun _ hu hne => h.centralizer_le_of_selected hc hu hne

namespace SymmetricFiveMarking

/-- The actual S₅ orbit theorem proves radical irreducibility for every moved
vector, without a coprimality or point-stabilizer hypothesis. -/
theorem radical_irreducible
    {T : Sylow 2 G} {L : Subgroup G} (d : SymmetricFiveMarking T L)
    {p : ℕ} [Fact p.Prime] (h : Context T L p)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    RadicalCentralizerIrreducible L p u := by
  apply radical_irreducible_of_selected h _ hu hne
  intro v hs
  exact (d.centralizer_index_and_radical_irreducible h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides ⟨v,hs.mem⟩
    (fun he => hs.ne_one (congrArg Subtype.val he)) hs.local_sylow).2

/-- The marked S₅ branch feeds 13.1.13 after the independent 13.1.12(3)
centralizer-containment argument is supplied on its selected representatives. -/
theorem ti_of_selected_centralizer_containment
    {T : Sylow 2 G} {L : Subgroup G} (d : SymmetricFiveMarking T L)
    {p : ℕ} [Fact p.Prime] (h : Context T L p)
    (hc : ∀ v : G, Selected T L v →
      centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :
    ChapterI.Section06To08.IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  apply normalizerMoved_ti_of_centralizer_analysis h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides
  · exact fun _ hu hne _ => d.radical_irreducible h hu hne
  · exact fun _ hu hne => h.centralizer_le_of_selected hc hu hne

end SymmetricFiveMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
