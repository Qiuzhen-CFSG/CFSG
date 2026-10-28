module
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement

/-!
# C-components and solvable quotients

An invariant solvable subgroup normalizes a C-component, and the C-component
is the solvable residual of their join. Quotienting by a solvable normal
subgroup therefore gives a bijection on C-components. Its inverse takes the
solvable residual of a quotient C-component's preimage.

The supplement result follows from the stronger perfect-subnormal theorem.
For quotient preservation, pull a perfect subnormal subgroup back, take its
residual, and use minimality. The residual identity gives injectivity, while
existence of a minimal perfect subnormal subgroup gives surjectivity.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition A.3.3(3)–(4), pp. 42–43 (1 March 2004 manuscript).
-/

@[expose] public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

namespace IsCComponent
variable {L M : Subgroup G}

/-- A.3.3(3): an invariant solvable subgroup normalizes a C-component. -/
theorem commutator_le_of_solvable (hL : L.IsCComponent)
    (N : Subgroup G) [Group.IsSolvable N] (hLN : L ≤ normalizer N) : ⁅L, N⁆ ≤ L := by
  let := hL.perfect
  exact hL.subnormal.commutator_le_of_solvable N hLN

/-- A.3.3(3): the residual of a C-component with an invariant solvable supplement. -/
theorem solvableResidual_sup_eq (hL : L.IsCComponent)
    (N : Subgroup G) [Group.IsSolvable N] (hLN : L ≤ normalizer N) :
    (solvableResidual ↥(L ⊔ N)).map (L ⊔ N).subtype = L := by
  let := hL.perfect
  exact hL.subnormal.solvableResidual_sup_eq N hLN

omit [Finite G] in
/-- A C-component has nontrivial image modulo a solvable normal subgroup. -/
theorem map_quotient_ne_bot (hL : L.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] :
    L.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hb
  have hLN : L ≤ N := by simpa only [map_eq_bot_iff, QuotientGroup.ker_mk'] using hb
  exact hL.not_isSolvable
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hLN))

/-- A.3.3(4): quotienting by a solvable normal subgroup preserves C-components. -/
theorem map_quotient (hL : L.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] :
    (L.map (QuotientGroup.mk' N)).IsCComponent := by
  let q := QuotientGroup.mk' N
  let := hL.perfect
  refine ⟨hL.map_quotient_ne_bot N, Group.IsPerfect.map q, hL.subnormal.quotient, ?_⟩
  intro K hKL hKbot hKperfect hKsub
  let := hKperfect
  let H := K.comap q
  let R := (solvableResidual H).map H.subtype
  have hRq : R.map q = K := by
    simpa only [R, H, solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using map_solvableResidual_comap q (QuotientGroup.mk'_surjective N) K
  have hRbot : R ≠ ⊥ := by
    intro hb
    exact hKbot (by rw [← hRq, hb, map_bot])
  have hRperfect : Group.IsPerfect R := Group.IsPerfect.map H.subtype
  have hRsub : R.IsSubnormal :=
    (inferInstance : (solvableResidual H).Normal).isSubnormal.trans' (hKsub.comap q)
  have hHN : H ≤ L ⊔ N := by
    simpa only [H, q, comap_map_eq, QuotientGroup.ker_mk'] using comap_mono (f := q) hKL
  have hRL : R ≤ L := by
    have hmono := map_solvableResidual_mono hHN
    rwa [hL.solvableResidual_sup_eq N (by rw [normalizer_eq_top]; exact le_top)] at hmono
  have hLR := hL.minimal R hRL hRbot hRperfect hRsub
  simpa only [hRq] using map_mono (f := q) hLR

/-- A.3.3(4): two C-components with the same image modulo a solvable normal subgroup coincide. -/
theorem eq_of_map_quotient_eq (hL : L.IsCComponent) (hM : M.IsCComponent)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (he : L.map (QuotientGroup.mk' N) = M.map (QuotientGroup.mk' N)) : L = M := by
  have hsup : L ⊔ N = M ⊔ N := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using
      congrArg (comap (QuotientGroup.mk' N)) he
  have hLN : L ≤ normalizer N := by rw [normalizer_eq_top]; exact le_top
  have hMN : M ≤ normalizer N := by rw [normalizer_eq_top]; exact le_top
  rw [← hL.solvableResidual_sup_eq N hLN, ← hM.solvableResidual_sup_eq N hMN, hsup]

/-- A.3.3(4): every quotient C-component lifts to a C-component. -/
theorem exists_map_quotient_eq (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    {K : Subgroup (G ⧸ N)} (hK : K.IsCComponent) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map (QuotientGroup.mk' N) = K := by
  let q := QuotientGroup.mk' N
  let H := K.comap q
  let R := (solvableResidual H).map H.subtype
  let := hK.perfect
  have hRq : R.map q = K := by
    simpa only [R, H, solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using map_solvableResidual_comap q (QuotientGroup.mk'_surjective N) K
  have hRbot : R ≠ ⊥ := by
    intro hb
    exact hK.ne_bot (by rw [← hRq, hb, map_bot])
  have hRperfect : Group.IsPerfect R := Group.IsPerfect.map H.subtype
  have hRsub : R.IsSubnormal :=
    (inferInstance : (solvableResidual H).Normal).isSubnormal.trans' (hK.subnormal.comap q)
  obtain ⟨L, hLR, hL⟩ := exists_isCComponent_le hRbot hRperfect hRsub
  refine ⟨L, hL, (hL.map_quotient N).eq_of_le hK ?_⟩
  simpa only [hRq] using map_mono (f := q) hLR

/-- The unique lift of a quotient C-component is the residual of its preimage. -/
theorem solvableResidual_preimage_eq (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    {K : Subgroup (G ⧸ N)} (hK : K.IsCComponent) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map (QuotientGroup.mk' N) = K ∧
      (solvableResidual (K.comap (QuotientGroup.mk' N))).map
        (K.comap (QuotientGroup.mk' N)).subtype = L := by
  obtain ⟨L, hL, he⟩ := hK.exists_map_quotient_eq N
  refine ⟨L, hL, he, ?_⟩
  rw [← he, comap_map_eq, QuotientGroup.ker_mk']
  exact hL.solvableResidual_sup_eq N (by rw [normalizer_eq_top]; exact le_top)

/-- The residual of a quotient C-component's preimage is its canonical C-component lift. -/
theorem solvableResidual_preimage (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    {K : Subgroup (G ⧸ N)} (hK : K.IsCComponent) :
    ((solvableResidual (K.comap (QuotientGroup.mk' N))).map
      (K.comap (QuotientGroup.mk' N)).subtype).IsCComponent := by
  obtain ⟨L, hL, _, he⟩ := hK.solvableResidual_preimage_eq N
  exact he.symm ▸ hL

end IsCComponent

/-- A.3.3(4): quotienting by a solvable normal subgroup gives a bijection on C-components. -/
theorem bijOn_isCComponent_map_quotient (N : Subgroup G) [N.Normal] [Group.IsSolvable N] :
    Set.BijOn (map (QuotientGroup.mk' N)) {L : Subgroup G | L.IsCComponent}
      {K : Subgroup (G ⧸ N) | K.IsCComponent} := by
  refine ⟨fun L hL => hL.map_quotient N, ?_, ?_⟩
  · intro L hL M hM he
    exact hL.eq_of_map_quotient_eq hM N he
  · intro K hK
    exact hK.exists_map_quotient_eq N

end Subgroup
