module

public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Sylow restriction and cores of Sylow overgroups

A Sylow subgroup remains Sylow in every intermediate subgroup containing it.
Its intersection with a relatively normal subgroup is Sylow in that subgroup.
Both statements below retain the ambient embeddings.

If J contains a Sylow subgroup of I, O_p(J) is the p-core of its normalizer
inside I: that normalizer's core lies in the same Sylow subgroup and is
normalized by J, hence lies in O_p(J). This elementary argument supplies the
radical-core conclusion used in Aschbacher–Smith 15.3.11(5), p.1124.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] {p : ℕ}

/-- Restrict a supplied ambient Sylow witness to an intermediate subgroup. -/
theorem exists_map_subtype_eq_of_le {I H : Subgroup G} (P : Sylow p I)
    (hHI : H ≤ I) (hPH : (P : Subgroup I).map I.subtype ≤ H) :
    ∃ Q : Sylow p H, (Q : Subgroup H).map H.subtype =
      (P : Subgroup I).map I.subtype := by
  have hr : (P : Subgroup I) ≤ (inclusion hHI).range := by
    intro x hx
    exact ⟨⟨x, hPH (mem_map.mpr ⟨x, hx, rfl⟩)⟩, rfl⟩
  let Q := P.comapOfInjective (inclusion hHI) (inclusion_injective hHI) hr
  refine ⟨Q, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨inclusion hHI y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hPH (mem_map.mpr ⟨y, hy, rfl⟩)⟩, hy, rfl⟩

/-- Sylow intersection with a normal subgroup, with normality relative to I. -/
theorem exists_map_subtype_eq_inf_of_normalizes [Finite G] [Fact p.Prime]
    {I N : Subgroup G} (P : Sylow p I) (hNI : N ≤ I)
    (hn : I ≤ normalizer (N : Set G)) :
    ∃ Q : Sylow p N, (Q : Subgroup N).map N.subtype =
      ((P : Subgroup I).map I.subtype) ⊓ N := by
  let : (N.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal (N.subgroupOf I)
  let e := subgroupOfEquivOfLe hNI
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    rw [hQ] at hz
    have hv : ((z : N.subgroupOf I) : G) = y := congrArg Subtype.val hzy
    have hzP : ((z : N.subgroupOf I) : G) ∈ (P : Subgroup I).map I.subtype :=
      mem_map.mpr ⟨z.val, hz, rfl⟩
    rw [hv] at hzP
    exact ⟨hzP, y.property⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyn⟩
    refine ⟨⟨y, hyn⟩, ?_, rfl⟩
    refine ⟨⟨y, hyn⟩, ?_, rfl⟩
    rwa [hQ]

end Sylow

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

/-- A Sylow overgroup's core equals the core of its relative normalizer. -/
theorem pCoreIn_normalizer_eq_of_sylow_le {I J : Subgroup G} (P : Sylow p I)
    (hJI : J ≤ I) (hPJ : (P : Subgroup I).map I.subtype ≤ J) :
    (I ⊓ normalizer (J.pCoreIn p : Set G)).pCoreIn p = J.pCoreIn p := by
  let R := J.pCoreIn p
  let N := I ⊓ normalizer (R : Set G)
  have hJR : J ≤ normalizer (R : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore p J))
  have hJN : J ≤ N := le_inf hJI hJR
  have hNR : N ≤ normalizer (R : Set G) := inf_le_right
  have hRN : R ≤ N := (pCoreIn_le p J).trans hJN
  have hNQ : N ≤ normalizer (N.pCoreIn p : Set G) := N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (pCore p N))
  obtain ⟨Q, hQ⟩ := P.exists_map_subtype_eq_of_le
    (show N ≤ I from inf_le_left) (hPJ.trans hJN)
  have hcoreJ : N.pCoreIn p ≤ J :=
    (pCoreIn_le_sylow N Q).trans (hQ.le.trans hPJ)
  exact le_antisymm
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn p N) hcoreJ (hJN.trans hNQ))
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn p J) hRN hNR)

end Subgroup
end
