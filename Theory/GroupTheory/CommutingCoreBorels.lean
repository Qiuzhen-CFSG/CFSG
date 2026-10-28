module
public import Theory.GroupTheory.SylowCommutingJoin
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness
/-!
# Self-centralizing cores and normal Sylow subgroups in commuting joins

A finite commuting family of characteristic-p subgroups generates another
characteristic-p subgroup. In a commuting pair, write a centralizing element
as a product: each coordinate centralizes its own core and hence lies in it.
Finite induction gives the family statement, including central intersections.

If each factor has a normal Sylow p-subgroup, those Sylow subgroups lie in
the core of the join. The commuting-product Sylow theorem makes this core
Sylow too. These are the orbit-Borel structure calculations in
Aschbacher--Smith 15.1.20, printed p.1094.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

private theorem core_le_core_of_normalizes {A D : Subgroup G}
    (hAD : A ≤ D) (hn : D ≤ normalizer (A : Set G)) :
    A.pCoreIn p ≤ D.pCoreIn p :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn p A) ((pCoreIn_le p A).trans hAD)
    (hn.trans (normalizer_le_normalizer_characteristic_image A (pCore p A)))

private theorem core_centralizer_sup (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G))
    (hA : A ⊓ centralizer (A.pCoreIn p : Set G) ≤ A.pCoreIn p)
    (hB : B ⊓ centralizer (B.pCoreIn p : Set G) ≤ B.pCoreIn p) :
    (A ⊔ B) ⊓ centralizer ((A ⊔ B).pCoreIn p : Set G) ≤ (A ⊔ B).pCoreIn p := by
  have hBA := le_centralizer_iff.mp hc
  have hAn : A ⊔ B ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer (hBA.trans (centralizer_le_normalizer _))
  have hBn : A ⊔ B ≤ normalizer (B : Set G) :=
    sup_le (hc.trans (centralizer_le_normalizer _)) B.le_normalizer
  have hAQ := core_le_core_of_normalizes (p := p) le_sup_left hAn
  have hBQ := core_le_core_of_normalizes (p := p) le_sup_right hBn
  rintro x ⟨hx,hxc⟩
  have hxprod : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B
      (hBA.trans (centralizer_le_normalizer _))]
    exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hxprod
  have haC : a ∈ centralizer (A.pCoreIn p : Set G) :=
    (centralizer (A.pCoreIn p : Set G)).mul_mem_cancel_right
      ((centralizer_le (pCoreIn_le p A)) (hBA hb)) |>.mp
        ((centralizer_le hAQ) hxc)
  have hbC : b ∈ centralizer (B.pCoreIn p : Set G) :=
    (centralizer (B.pCoreIn p : Set G)).mul_mem_cancel_left
      ((centralizer_le (pCoreIn_le p B)) (hc ha)) |>.mp
        ((centralizer_le hBQ) hxc)
  exact (A ⊔ B).pCoreIn p |>.mul_mem (hAQ (hA ⟨ha,haC⟩)) (hBQ (hB ⟨hb,hbC⟩))

/-- Characteristic p passes to a finite commuting join, allowing central intersections. -/
theorem core_centralizer_iSup_of_commuting {ι : Type*} [Finite ι]
    (C : ι → Subgroup G)
    (hc : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hC : ∀ i, C i ⊓ centralizer ((C i).pCoreIn p : Set G) ≤ (C i).pCoreIn p) :
    (⨆ i, C i) ⊓ centralizer ((⨆ i, C i).pCoreIn p : Set G) ≤ (⨆ i, C i).pCoreIn p := by
  classical
  let := Fintype.ofFinite ι
  have hfin (s : Finset ι) :
      (⨆ i ∈ s, C i) ⊓ centralizer ((⨆ i ∈ s, C i).pCoreIn p : Set G) ≤
        (⨆ i ∈ s, C i).pCoreIn p := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.iSup_insert]
      apply core_centralizer_sup (C i) (⨆ j ∈ s, C j) ?_ (hC i) ih
      apply le_centralizer_iff.mpr
      exact iSup_le fun j => iSup_le fun hj =>
        le_centralizer_iff.mp (hc (fun he => hi (he ▸ hj)))
  simpa using hfin Finset.univ

variable [Finite G] [Fact p.Prime]

/-- A commuting join of groups with normal Sylow p-subgroups again has a
normal Sylow p-subgroup, expressed by its literal core. -/
theorem exists_sylow_eq_core_of_commuting {ι : Type*} [Finite ι]
    (C : ι → Subgroup G)
    (hc : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hC : ∀ i, ∃ P : Sylow p (C i), (P : Subgroup (C i)) = pCore p (C i)) :
    ∃ P : Sylow p (⨆ i, C i : Subgroup G),
      (P : Subgroup (⨆ i, C i : Subgroup G)) = pCore p (⨆ i, C i : Subgroup G) := by
  classical
  choose P hP using hC
  let D := ⨆ i, C i
  have hn (i) : D ≤ normalizer (C i : Set G) := by
    apply iSup_le
    intro j
    by_cases he : j = i
    · subst j; exact (C i).le_normalizer
    · exact (hc he).trans (centralizer_le_normalizer _)
  have hPQ (i) : (P i : Subgroup (C i)).map (C i).subtype ≤ D.pCoreIn p := by
    rw [hP i]
    exact core_le_core_of_normalizes (le_iSup C i) (hn i)
  obtain ⟨Q,hQ⟩ := exists_sylow_iSup_le_of_commuting C
    (fun _ _ hij _ _ hx hy => (hc hij hx _ hy).symm) P (D.pCoreIn p) hPQ
  refine ⟨Q,le_antisymm ?_ (pCore_isPGroup.le_sylow_of_normal Q)⟩
  exact (map_le_map_iff_of_injective D.subtype_injective).mp hQ
section Transport
variable {H : Type*} [Group H]
omit [Finite G] [Fact p.Prime] in
/-- An injective embedding preserves the literal relative Sylow normalizer. -/
theorem map_relative_sylowNormalizer (S K : Subgroup G) (f : G →* H)
    (hf : Function.Injective f) :
    (K ⊓ normalizer ((S ⊓ K : Subgroup G) : Set G)).map f =
      K.map f ⊓ normalizer ((S.map f ⊓ K.map f : Subgroup H) : Set H) := by
  rw [←map_inf S K f hf]
  have hn : (normalizer ((S ⊓ K).map f : Set H)).comap f =
      normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf]
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left)
      ((map_mono inf_le_right).trans (le_normalizer_map f))
  · rintro x ⟨⟨k,hk,rfl⟩,hnk⟩
    exact ⟨k,⟨hk,hn ▸ hnk⟩,rfl⟩
end Transport
end Subgroup
