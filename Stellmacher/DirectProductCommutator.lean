module
public import Stellmacher.DirectProductMap
public import Theory.GroupAction.CommutatorDecomposition
public import Theory.GroupAction.NormalizingActor

/-!
# Action commutators in a product module

Suppose commuting actor factors generate E, and the module is the internal
product of the E-fixed subgroup and the factors' commutator modules. For
B≤E, its commutator module is the internal product of its intersections
with those factor modules. This supplies Stellmacher (8.1)(c), journal p.37.

Each factor is normalized by E because it is normalized by itself and
centralized by every other factor. Thus B preserves every factor module.
The generic fixed/invariant generation lemma gives the required supremum;
pairwise disjointness and commutation descend to the intersections. The
argument uses precisely the repository's internal-product-family predicate,
without strengthening it to a different independence condition.
-/

namespace Stellmacher
open scoped IsMulCommutative
universe u

public theorem IsInternalDirectProductFamily.commutatorAction
    {G V : Type u} [Group G] [Group V] [IsMulCommutative V]
    [MulDistribMulAction G V] {ι : Type*}
    {E : Subgroup G} {D : ι → Subgroup G}
    (hE : IsInternalDirectProductFamily E D)
    (hV : IsInternalDirectProductFamily (⊤ : Subgroup V)
      (fun o : Option ι => o.elim (FixedPoints.subgroup E V)
        (fun i => commutatorAction (D i) V)))
    (B : Subgroup G) (hBE : B ≤ E) :
    IsInternalDirectProductFamily (commutatorAction B V)
      (fun i => commutatorAction B V ⊓ commutatorAction (D i) V) := by
  have hnorm (i : ι) : B ≤ Subgroup.normalizer (D i : Set G) := by
    apply hBE.trans
    rw [hE.1]
    apply iSup_le
    intro j
    by_cases hji : j = i
    · subst j
      exact (D i).le_normalizer
    · apply le_trans _ (Subgroup.centralizer_le_normalizer (D i : Set G))
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        hE.2.2 i j (Ne.symm hji) y hy x hx
  have hinv (i : ι) : IsInvariant B V (_root_.commutatorAction (D i) V) :=
    commutatorAction_isInvariant_of_normalizing_actor B (D i) (hnorm i)
  have hgen : FixedPoints.subgroup E V ⊔
      ⨆ i, _root_.commutatorAction (D i) V = ⊤ := by
    simpa only [iSup_option, Option.elim_none, Option.elim_some] using hV.1.symm
  have hfix (b : B) (v : V) (hv : v ∈ FixedPoints.subgroup E V) : b • v = v := by
    exact hv ⟨b, hBE b.property⟩
  refine ⟨commutatorAction_eq_iSup_inf_of_fixed_sup _ _ hgen hfix hinv, ?_, ?_⟩
  · intro i j hij
    exact (hV.2.1 (some i) (some j) (fun he => hij (Option.some.inj he))).mono
      inf_le_right inf_le_right
  · intro i j hij x hx y hy
    exact hV.2.2 (some i) (some j) (fun he => hij (Option.some.inj he))
      x hx.2 y hy.2

end Stellmacher
