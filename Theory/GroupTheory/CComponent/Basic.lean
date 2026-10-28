module
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.Order.Minimal

/-!
# Minimal nontrivial perfect subnormal subgroups

A C-component is minimal among nontrivial perfect subnormal subgroups. These
notions make sense in every group; finiteness is required only for the existence
and solvability results below. In a finite group, being perfect is equivalent to
being equal to the terminal term of the derived series.

Restriction to an overgroup and lifting through a subnormal inclusion follow
from transitivity of subnormality. For existence, minimize among the terms of the
derived series and then among nontrivial perfect subnormal subgroups. This also
shows that every proper subnormal subgroup of a C-component is solvable.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition A.3.1 and Proposition A.3.3(1)–(2), pp. 41–42.
-/

@[expose] public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A subgroup minimal among nontrivial perfect subnormal subgroups. -/
structure IsCComponent (L : Subgroup G) : Prop where
  /-- A C-component is nontrivial. -/
  ne_bot : L ≠ ⊥
  /-- A C-component equals its commutator subgroup. -/
  perfect : Group.IsPerfect L
  /-- A C-component is subnormal in its ambient group. -/
  subnormal : L.IsSubnormal
  /-- No smaller subgroup has all three defining properties. -/
  minimal : ∀ K : Subgroup G, K ≤ L → K ≠ ⊥ → Group.IsPerfect K →
    K.IsSubnormal → L ≤ K

namespace IsCComponent
variable {L H : Subgroup G}

/-- Comparable C-components coincide. -/
theorem eq_of_le (hL : L.IsCComponent) (hH : H.IsCComponent) (h : L ≤ H) : L = H :=
  le_antisymm h (hH.minimal L h hL.ne_bot hL.perfect hL.subnormal)

/-- A C-component is not solvable. -/
theorem not_isSolvable (hL : L.IsCComponent) : ¬ Group.IsSolvable L := by
  let := hL.perfect
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL.ne_bot
  exact Group.IsPerfect.not_isSolvable L

private theorem perfect_subgroupOf (h : L ≤ H) (hp : Group.IsPerfect L) :
    Group.IsPerfect (L.subgroupOf H) := by
  rw [Subgroup.isPerfect_iff, ← Subgroup.map_subtype_inj, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le h]
  exact Subgroup.isPerfect_iff.mp hp

/-- A.3.3(2): a C-component remains one in any subgroup containing it. -/
theorem subgroupOf (hL : L.IsCComponent) (h : L ≤ H) :
    (L.subgroupOf H).IsCComponent := by
  refine ⟨?_, perfect_subgroupOf h hL.perfect, hL.subnormal.subgroupOf, ?_⟩
  · intro hb
    apply hL.ne_bot
    have := congrArg (Subgroup.map H.subtype) hb
    simpa [Subgroup.map_subgroupOf_eq_of_le h] using this
  · intro K hK hKbot hKperfect hKsub
    let := hKperfect
    have hmap_le : K.map H.subtype ≤ L := by
      simpa [Subgroup.map_subgroupOf_eq_of_le h] using (Subgroup.map_mono (f := H.subtype) hK)
    have hmap_bot : K.map H.subtype ≠ ⊥ := by
      exact fun hb => hKbot ((Subgroup.map_eq_bot_iff_of_injective K H.subtype_injective).mp hb)
    have hsub : (K.map H.subtype).IsSubnormal := by
      have hc := hKsub.comap (Subgroup.inclusion h)
      have he : (K.comap (Subgroup.inclusion h)).map L.subtype = K.map H.subtype := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨Subgroup.inclusion h y, hy, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hK hy⟩, hy, rfl⟩
      rw [← he]
      exact hc.trans' hL.subnormal
    have hmin := hL.minimal (K.map H.subtype) hmap_le hmap_bot
      (Group.IsPerfect.map H.subtype) hsub
    intro x hx
    obtain ⟨y, hy, he⟩ := hmin hx
    have : y = x := Subtype.ext he
    simpa [this] using hy

/-- A.3.3(2): a C-component of a subnormal subgroup is a C-component of the ambient group. -/
theorem map_subtype (hL : L.IsSubnormal) {K : Subgroup L}
    (hK : K.IsCComponent) : (K.map L.subtype).IsCComponent := by
  let := hK.perfect
  refine ⟨?_, Group.IsPerfect.map L.subtype, hK.subnormal.trans' hL, ?_⟩
  · exact fun hb => hK.ne_bot ((Subgroup.map_eq_bot_iff_of_injective K L.subtype_injective).mp hb)
  · intro J hJ hJbot hJperfect hJsub
    have hJL : J ≤ L := hJ.trans (by simpa using Subgroup.map_le_range L.subtype K)
    have hjK : J.subgroupOf L ≤ K := by
      intro x hx
      obtain ⟨y, hy, he⟩ := hJ hx
      have : y = x := Subtype.ext he
      simpa [this] using hy
    have hjbot : J.subgroupOf L ≠ ⊥ := by
      intro hb
      apply hJbot
      have := congrArg (Subgroup.map L.subtype) hb
      simpa [Subgroup.map_subgroupOf_eq_of_le hJL] using this
    have hmin := hK.minimal (J.subgroupOf L) hjK hjbot
      (perfect_subgroupOf hJL hJperfect) hJsub.subgroupOf
    simpa [Subgroup.map_subgroupOf_eq_of_le hJL] using (Subgroup.map_mono (f := L.subtype) hmin)

/-- A.3.3(2): restriction to a subnormal overgroup preserves and reflects C-components. -/
theorem subgroupOf_iff (hH : H.IsSubnormal) (h : L ≤ H) :
    (L.subgroupOf H).IsCComponent ↔ L.IsCComponent := by
  constructor
  · intro hL
    simpa [Subgroup.map_subgroupOf_eq_of_le h] using hL.map_subtype hH
  · exact fun hL => hL.subgroupOf h

private theorem perfect_of_map {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) {K : Subgroup G} (hp : Group.IsPerfect (K.map f)) :
    Group.IsPerfect K := by
  rw [Subgroup.isPerfect_iff, ← (Subgroup.map_injective hf).eq_iff,
    Subgroup.map_commutator]
  exact Subgroup.isPerfect_iff.mp hp

/-- Group isomorphisms carry C-components to C-components. -/
theorem map_equiv (hL : L.IsCComponent) {G' : Type*} [Group G'] (e : G ≃* G') :
    (L.map e.toMonoidHom).IsCComponent := by
  let := hL.perfect
  refine ⟨fun hb => hL.ne_bot ((L.map_eq_bot_iff_of_injective e.injective).mp hb),
    Group.IsPerfect.map _, hL.subnormal.map e.surjective, ?_⟩
  intro J hJ hJbot hJperfect hJsub
  have hmap : (J.comap e.toMonoidHom).map e.toMonoidHom = J :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective J
  have hJL : J.comap e.toMonoidHom ≤ L := by
    simpa only [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] using
      Subgroup.comap_mono (f := e.toMonoidHom) hJ
  have hmin := hL.minimal (J.comap e.toMonoidHom) hJL
    (fun hb => hJbot (by rw [← hmap, hb, Subgroup.map_bot]))
    (perfect_of_map e.toMonoidHom e.injective (hmap.symm ▸ hJperfect))
    (hJsub.comap _)
  simpa only [hmap] using Subgroup.map_mono (f := e.toMonoidHom) hmin

/-- Restrict a C-component of an overgroup to an intermediate subgroup. -/
theorem subgroupOf_of_le {B K : Subgroup G} (hB : (B.subgroupOf H).IsCComponent)
    (hBK : B ≤ K) (hKH : K ≤ H) : (B.subgroupOf K).IsCComponent := by
  have hres := hB.subgroupOf (show B.subgroupOf H ≤ K.subgroupOf H from
    Subgroup.comap_mono hBK)
  have hm := hres.map_equiv (Subgroup.subgroupOfEquivOfLe hKH)
  have he : ((B.subgroupOf H).subgroupOf (K.subgroupOf H)).map
      (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom = B.subgroupOf K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, hKH x.property⟩, x.property⟩, hx, rfl⟩
  rwa [he] at hm

/-- A.3.3(1): a C-component has no C-component other than itself. -/
theorem eq_top_of_isCComponent {K : Subgroup L} (hL : L.IsCComponent)
    (hK : K.IsCComponent) : K = ⊤ := by
  have hm := hK.map_subtype hL.subnormal
  have he : K.map L.subtype = L :=
    hm.eq_of_le hL (by simpa using Subgroup.map_le_range L.subtype K)
  apply (Subgroup.map_injective L.subtype_injective)
  simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

end IsCComponent

/-- A finite nontrivial perfect subnormal subgroup contains a C-component. -/
theorem exists_isCComponent_le [Finite G] {H : Subgroup G}
    (hH : H ≠ ⊥) (hp : Group.IsPerfect H) (hs : H.IsSubnormal) :
    ∃ L : Subgroup G, L ≤ H ∧ L.IsCComponent := by
  obtain ⟨L, hLH, hL, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K : Subgroup G => K ≠ ⊥ ∧ Group.IsPerfect K ∧ K.IsSubnormal)
    H ⟨hH, hp, hs⟩
  exact ⟨L, hLH, hL.1, hL.2.1, hL.2.2,
    fun K hK hn hp hs => hmin ⟨hn, hp, hs⟩ hK⟩

/-- Every finite nonsolvable group has a C-component. -/
theorem exists_isCComponent_of_not_isSolvable [Finite G] (hG : ¬ Group.IsSolvable G) :
    ∃ L : Subgroup G, L.IsCComponent := by
  obtain ⟨D, ⟨n, rfl⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun K : Subgroup G => ∃ n : ℕ, derivedSeries G n = K)
    ⟨⊤, 0, derivedSeries_zero G⟩
  have hperfect : Group.IsPerfect (derivedSeries G n) := by
    rw [Subgroup.isPerfect_iff]
    apply le_antisymm (derivedSeries G n).commutator_le_self
    exact hmin ⟨n + 1, derivedSeries_succ G n⟩ (derivedSeries G n).commutator_le_self
  have hne : derivedSeries G n ≠ ⊥ := fun hn => hG ⟨n, hn⟩
  obtain ⟨L, _, hL⟩ := exists_isCComponent_le hne hperfect
    (derivedSeries_normal G n).isSubnormal
  exact ⟨L, hL⟩

/-- The first assertion in the proof of A.3.3(1): proper subnormal subgroups of a C-component are solvable. -/
theorem IsCComponent.isSolvable_of_subnormal_lt_top [Finite G]
    {L : Subgroup G} (hL : L.IsCComponent) {N : Subgroup L}
    (hN : N.IsSubnormal) (hproper : N ≠ ⊤) : Group.IsSolvable N := by
  by_contra hn
  obtain ⟨K, hK⟩ := exists_isCComponent_of_not_isSolvable hn
  have hKL : (K.map N.subtype).IsCComponent := hK.map_subtype hN
  have he := hL.eq_top_of_isCComponent hKL
  exact hproper (top_unique (he ▸ (by simpa using Subgroup.map_le_range N.subtype K)))

end Subgroup
