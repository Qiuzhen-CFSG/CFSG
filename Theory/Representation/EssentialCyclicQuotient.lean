module
public import Theory.Representation.EssentialResidualQuotient
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.PSL3Two.ParabolicCyclic.Basic

/-!
# A fixed cyclic generator retains a chosen normal actor in a simple quotient

An invariant subspace maximal subject to retaining a normal two-perfect
actor's moved space gives an essential simple moved image. That quotient
has no actor-fixed vectors. Averaging over the actor's Sylow cosets puts
the original Sylow-fixed cyclic generator in this simple image. Cyclicity
then makes the entire quotient simple, while the chosen actor still moves it.

The averaging takes place inside the chosen normal actor; no hypothesis
that this actor supplements the ambient Sylow is needed.
Source application: Aschbacher–Smith 14.7.42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open BinaryLinearThree.ParabolicCyclic
namespace Representation.EssentialCyclicQuotient
open EssentialResidualQuotient
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A Sylow-fixed cyclic module has an irreducible quotient retaining any
specified normal two-perfect actor which acts nontrivially. -/
theorem exists_irreducible_quotient
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (hK : IsPPerfect 2 K) (hmove : ¬ K ≤ ρ.ker)
    (S : Sylow 2 G) (v : V)
    (hfix : ∀ g ∈ (S : Subgroup G), ρ g v = v)
    (hcyc : orbitSpan ρ ⊤ v = ⊤) :
    ∃ N : Subrepresentation ρ, IsCoatom N ∧
      IsIrreducible N.quotientRepresentation ∧ ¬ K ≤ N.quotientRepresentation.ker := by
  let D := moved ρ K
  obtain ⟨N,hDN,hmax,_,hess⟩ := exists_essential_quotient ρ D
    (moved_ne_bot_of_not_le_ker ρ K hmove)
  let E := N.quotientImage D
  have hdisp (k : K) (w : V ⧸ N.toSubmodule) :
      N.quotientRepresentation k w - w ∈ E := by
    obtain ⟨x,rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact ⟨ρ k x - x,Submodule.subset_span ⟨k,k.property,x,Submodule.mem_top,rfl⟩,
      map_sub _ _ _⟩
  have hnoncentral : ¬ E.toSubmodule ≤ fixedSpace N.quotientRepresentation K := by
    intro hE
    have hf (w : V ⧸ N.toSubmodule) : w ∈ fixedSpace N.quotientRepresentation K := by
      apply fixed_of_pPerfect_central_kernel N.quotientRepresentation K hK E.toSubmodule.mkQ
      · simpa only [Submodule.ker_mkQ] using hE
      · intro k
        exact (Submodule.Quotient.eq _).mpr (hdisp k w)
    apply hDN
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,x,_,rfl⟩
    exact (Submodule.Quotient.eq N.toSubmodule).mp (hf (N.toSubmodule.mkQ x) ⟨k,hk⟩)
  have hzero : fixedSpace N.quotientRepresentation K = ⊥ := by
    let C : Subrepresentation N.quotientRepresentation := {
      toSubmodule := fixedSpace N.quotientRepresentation K
      apply_mem_toSubmodule g x hx :=
        (fixedSpace_stable_of_normalizes N.quotientRepresentation
          (show (⊤ : Subgroup G) ≤ normalizer (K : Set G) from le_normalizer_of_normal)
          (mem_top g) x).2 hx }
    by_contra hn
    exact hnoncentral (hess C (fun he => hn (congrArg Subrepresentation.toSubmodule he)))
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  let w := N.toSubmodule.mkQ v
  have hw : w ∈ E := by
    obtain ⟨z,hz,hwz⟩ := fixed_lift_of_displacement
      (N.quotientRepresentation.comp K.subtype) P E.toSubmodule w
      (by
        intro p
        change N.toSubmodule.mkQ (ρ p.val.val v) = N.toSubmodule.mkQ v
        exact congrArg N.toSubmodule.mkQ (hfix p.val (hP.le p.property)))
      (fun k => hdisp k w)
    have hz0 : z = 0 := by
      have hzc : z ∈ fixedSpace N.quotientRepresentation K := hz
      rwa [hzero,Submodule.mem_bot] at hzc
    change w ∈ E.toSubmodule
    simpa only [hz0,sub_zero] using hwz
  have hall : ∀ x : V, N.toSubmodule.mkQ x ∈ E := by
    intro x
    have hx : x ∈ orbitSpan ρ ⊤ v := hcyc.symm ▸ Submodule.mem_top
    have hle : orbitSpan ρ ⊤ v ≤ E.toSubmodule.comap N.toSubmodule.mkQ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,_,rfl⟩
      exact E.apply_mem_toSubmodule g hw
    exact hle hx
  have hE : E = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨x,rfl⟩ := N.toSubmodule.mkQ_surjective x
    exact hall x
  have hsup : N.toSubmodule ⊔ D.toSubmodule = ⊤ :=
    (N.quotientImage_eq_top_iff D).mp hE
  have hN : IsCoatom N := by
    refine ⟨fun hn => hDN (hn ▸ le_top),fun Q hQ => ?_⟩
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [←hsup]
    exact sup_le hQ.le (hmax Q hQ)
  refine ⟨N,hN,SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN,?_⟩
  intro hk
  apply hnoncentral
  intro x _ k
  exact LinearMap.congr_fun (hk k.property) x

end Representation.EssentialCyclicQuotient
