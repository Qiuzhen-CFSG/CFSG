module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Quasisimple component calculus

Components here are subnormal quasisimple subgroups, with no ambient normality
or trivial-center assumption. A proper normal subgroup of a quasisimple group
is central. Induction on subnormal chains, using perfectness and the
three-subgroup lemma, therefore shows that a component is contained in or
centralizes every subnormal subgroup. This proves that distinct components
commute and prevents proper containment between components.

We transport components under isomorphisms, restriction to overgroups, and
surjective homomorphisms. Nontrivial homomorphic images remain quasisimple:
the preimage of their center is exactly the original center. Commuting perfect
subgroups cannot have the same nontrivial image.

Finally `componentOrbit L A` is the join of the actual conjugates of `L` by
`A`. It is perfect and normal inside `L ⊔ A`. If `A` does not normalize `L`,
then `[componentOrbit L A, A] = componentOrbit L A`. Normality here is relative
to the generated overgroup. These arguments also work without finiteness.

Source: Gorenstein–Lyons–Solomon, *The Classification of the Finite Simple
Groups*, vol. 2, Theorem 3.5(i),(iii), Lemmas 3.9–3.10, and the opening
reduction of Theorem 26.24. The subnormal-chain argument extends
`Commutator.SimpleSubnormal` to quasisimple groups.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Quasisimplicity is invariant under group isomorphism. -/
theorem IsQuasisimple.of_mulEquiv (e : G ≃* H) [hG : IsQuasisimple G] :
    IsQuasisimple H := by
  have hcenter : (center G).map e.toMonoidHom = center H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
        e.apply_symm_apply x⟩
  exact { toIsPerfect := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
          simple := (MulEquiv.isSimpleGroup_congr (QuotientGroup.congr _ _ e hcenter)).mp hG.simple }

/-- Every proper normal subgroup of a quasisimple group is central. -/
theorem IsQuasisimple.normal_le_center_or_eq_top [IsQuasisimple G]
    (N : Subgroup G) [N.Normal] : N ≤ center G ∨ N = ⊤ := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let q := QuotientGroup.mk' (center G)
  have hn : (N.map q).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with hb | ht
  · left
    intro x hx
    have hxq : q x ∈ N.map q := mem_map_of_mem q hx
    rw [hb, mem_bot] at hxq
    exact (QuotientGroup.eq_one_iff x).mp hxq
  · right
    have he := congrArg (Subgroup.comap q) ht
    have hs : N ⊔ center G = ⊤ := by simpa [q, sup_comm] using he
    apply top_unique
    simpa using (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      hs (inferInstance : IsMulCommutative (center G)))

/-- Every proper subnormal subgroup of a quasisimple group is central. -/
theorem IsQuasisimple.subnormal_le_center_or_eq_top [IsQuasisimple G]
    (N : Subgroup G) (hN : N.IsSubnormal) : N ≤ center G ∨ N = ⊤ := by
  rcases hN.lt_normal with ht | ⟨K, hn, hNK, hK⟩
  · exact Or.inr ht
  · let := hn
    rcases IsQuasisimple.normal_le_center_or_eq_top K with hc | ht
    · exact Or.inl (hNK.trans hc)
    · exact (hK.ne ht).elim

/-- Isomorphisms carry components to components. -/
theorem IsComponent.map_equiv {L : Subgroup G} (hL : IsComponent G L)
    (e : G ≃* H) : IsComponent H (L.map e.toMonoidHom) := by
  let := hL.2
  exact ⟨hL.1.map e.surjective, IsQuasisimple.of_mulEquiv (e.subgroupMap L)⟩

/-- A component remains a component in every overgroup containing it. -/
theorem IsComponent.subgroupOf {L K : Subgroup G} (hL : IsComponent G L)
    (hLK : L ≤ K) : IsComponent K (L.subgroupOf K) := by
  let := hL.2
  exact ⟨hL.1.subgroupOf,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLK).symm⟩

/-- A component is contained in or centralizes each normal subgroup. -/
theorem IsComponent.normal_dichotomy {L : Subgroup G} (hL : IsComponent G L)
    (N : Subgroup G) [N.Normal] : L ≤ N ∨ ⁅L, N⁆ = ⊥ := by
  let := hL.2
  rcases IsQuasisimple.normal_le_center_or_eq_top (N.subgroupOf L) with hc | ht
  · right
    rw [commutator_comm]
    apply commutator_eq_bot_of_inf_subnormal N L L hL.1 le_rfl
    have he : ⁅N.subgroupOf L, (⊤ : Subgroup L)⁆ = ⊥ :=
      commutator_top_right_eq_bot_iff_le_center.mpr hc
    have hm := congrArg (Subgroup.map L.subtype) he
    simpa [map_commutator, ← MonoidHom.range_eq_map] using hm
  · exact Or.inl (subgroupOf_eq_top.mp ht)

/-- A component is contained in or centralizes each subnormal subgroup. -/
theorem IsComponent.subnormal_dichotomy {L : Subgroup G} (hL : IsComponent G L)
    (N : Subgroup G) (hN : N.IsSubnormal) : L ≤ N ∨ ⁅L, N⁆ = ⊥ := by
  induction hN with
  | top => exact Or.inl le_top
  | step N K hNK hK hn ih =>
    rcases ih with hLK | hc
    · let := hn
      rcases (hL.subgroupOf hLK).normal_dichotomy (N.subgroupOf K) with hl | hc
      · left
        simpa [map_subgroupOf_eq_of_le hLK, map_subgroupOf_eq_of_le hNK] using
          map_mono (f := K.subtype) hl
      · right
        have he := congrArg (Subgroup.map K.subtype) hc
        simpa [map_commutator, map_subgroupOf_eq_of_le hLK,
          map_subgroupOf_eq_of_le hNK] using he
    · exact Or.inr (le_bot_iff.mp ((commutator_mono le_rfl hNK).trans hc.le))

/-- Containment between components implies equality. -/
theorem IsComponent.eq_of_le {L K : Subgroup G} (hL : IsComponent G L)
    (hK : IsComponent G K) (hLK : L ≤ K) : L = K := by
  let := hK.2
  let := (hL.subgroupOf hLK).2
  rcases IsQuasisimple.subnormal_le_center_or_eq_top (L.subgroupOf K)
      hL.1.subgroupOf with hc | ht
  · have he : ⁅L.subgroupOf K, L.subgroupOf K⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_mono hc le_top).trans
        (commutator_center_left (⊤ : Subgroup K)).le)
    rw [commutator_eq_self] at he
    let : IsSimpleGroup ((L.subgroupOf K) ⧸ center (L.subgroupOf K)) :=
      IsQuasisimple.simple
    have : Nontrivial (L.subgroupOf K) :=
      (QuotientGroup.mk'_surjective (center (L.subgroupOf K))).nontrivial
    exact ((nontrivial_iff_ne_bot _).mp inferInstance he).elim
  · exact le_antisymm hLK (subgroupOf_eq_top.mp ht)

/-- Distinct components commute. -/
theorem IsComponent.commutator_eq_bot_of_ne {L K : Subgroup G}
    (hL : IsComponent G L) (hK : IsComponent G K) (hne : L ≠ K) : ⁅L, K⁆ = ⊥ := by
  rcases hL.subnormal_dichotomy K hK.1 with hle | hc
  · exact (hne (hL.eq_of_le hK hle)).elim
  · exact hc

/-- Every nontrivial homomorphic image of a quasisimple group is quasisimple. -/
theorem IsQuasisimple.of_surjective [IsQuasisimple G] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f) : IsQuasisimple H := by
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective hf
  have hcenter : (center H).comap f = center G := by
    apply le_antisymm
    · rcases IsQuasisimple.normal_le_center_or_eq_top ((center H).comap f) with hc | ht
      · exact hc
      · have hc : center H = ⊤ := by
          apply (Subgroup.comap_injective hf)
          simpa using ht
        exact (Group.IsPerfect.not_isMulCommutative H (center_eq_top_iff.mp hc)).elim
    · intro x hx
      change f x ∈ center H
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := hf y
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)
  let q := (QuotientGroup.mk' (center H)).comp f
  have hker : q.ker = center G := by
    change ((QuotientGroup.mk' (center H)).comp f).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hcenter
  let e : G ⧸ center G ≃* H ⧸ center H :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q
        ((QuotientGroup.mk'_surjective _).comp hf))
  exact { simple := (MulEquiv.isSimpleGroup_congr e).mp IsQuasisimple.simple }

/-- Under a surjection a component has trivial image or component image. -/
theorem IsComponent.map_surjective {L : Subgroup G} (hL : IsComponent G L)
    (f : G →* H) (hf : Function.Surjective f) :
    L.map f = ⊥ ∨ IsComponent H (L.map f) := by
  by_cases hb : L.map f = ⊥
  · exact Or.inl hb
  · right
    let := hL.2
    have : Nontrivial (L.map f) := (nontrivial_iff_ne_bot _).mpr hb
    exact ⟨hL.1.map hf,
      IsQuasisimple.of_surjective (f.subgroupMap L) (f.subgroupMap_surjective L)⟩

/-- Distinct components cannot have the same nontrivial homomorphic image. -/
theorem IsComponent.eq_of_map_eq {L K : Subgroup G}
    (hL : IsComponent G L) (hK : IsComponent G K) (f : G →* H)
    (he : L.map f = K.map f) (hne : L.map f ≠ ⊥) : L = K := by
  by_contra hLK
  let := hL.2
  let : Group.IsPerfect (L.map f) := Group.IsPerfect.map f
  have hc := congrArg (Subgroup.map f) (hL.commutator_eq_bot_of_ne hK hLK)
  rw [map_commutator, ← he, commutator_eq_self, Subgroup.map_bot] at hc
  exact hne hc

/-- A component's commutator is trivial or generates its entire conjugate orbit. -/
theorem IsComponent.commutator_dichotomy {L : Subgroup G}
    (hL : IsComponent G L) (A : Subgroup G) :
    ⁅L, A⁆ = ⊥ ∨ ⁅L, A⁆ = ⨆ a : A, L.map (MulAut.conj (a : G)).toMonoidHom := by
  let := hL.2
  let S := L ⊔ A
  have hLS : L ≤ S := le_sup_left
  have hCS : ⁅L, A⁆ ≤ S := commutator_le_sup L A
  rcases (hL.subgroupOf hLS).normal_dichotomy (⁅L, A⁆.subgroupOf S) with hl | hc
  · right
    have hLC : L ≤ ⁅L, A⁆ := by
      simpa [map_subgroupOf_eq_of_le hLS, map_subgroupOf_eq_of_le hCS] using
        map_mono (f := S.subtype) hl
    exact le_antisymm (commutator_le_iSup_conjugates L A)
      (iSup_conjugates_le_of_le_normalizer L A ⁅L, A⁆ hLC
        (normalizer_commutator_ge_right L A))
  · left
    have hc' : ⁅L, ⁅L, A⁆⁆ = ⊥ := by
      have he := congrArg (Subgroup.map S.subtype) hc
      simpa [map_commutator, map_subgroupOf_eq_of_le hLS,
        map_subgroupOf_eq_of_le hCS] using he
    rw [commutator_comm L ⁅L, A⁆, commutator_comm L A] at hc'
    rw [commutator_comm]
    exact commutator_eq_bot_of_iterated_eq_bot A L hc'

/-- The subgroup generated by the actual `A`-conjugates of `L`. -/
def componentOrbit (L A : Subgroup G) : Subgroup G :=
  ⨆ a : A, L.map (MulAut.conj (a : G)).toMonoidHom

/-- Conjugates of a component generate a perfect subgroup. -/
theorem IsComponent.orbit_isPerfect {L : Subgroup G}
    (hL : IsComponent G L) (A : Subgroup G) : Group.IsPerfect (componentOrbit L A) := by
  let := hL.2
  exact isPerfect_iSup_conjugates L A

/-- The conjugate orbit is normal in the join, without ambient normality. -/
theorem componentOrbit_normal_subgroupOf_sup (L A : Subgroup G) :
    ((componentOrbit L A).subgroupOf (L ⊔ A)).Normal :=
  normal_iSup_conjugates_subgroupOf_sup L A

/-- If `A` moves the component, its orbit is generated by commutators with `A`. -/
theorem IsComponent.commutator_orbit_eq_self {L : Subgroup G}
    (hL : IsComponent G L) (A : Subgroup G) (hA : ¬ A ≤ normalizer L) :
    ⁅componentOrbit L A, A⁆ = componentOrbit L A := by
  rcases hL.commutator_dichotomy A with hb | he
  · exact (hA (le_normalizer_iff_commutator_le_left.mpr (by rw [hb]; exact bot_le))).elim
  · apply le_antisymm
    · exact le_normalizer_iff_commutator_le_left.mp (le_normalizer_iSup_conjugates L A)
    · exact he.symm.le.trans (commutator_mono (le_iSup_conjugates L A) le_rfl)

/-- Each actual conjugate of a component is a component. -/
theorem IsComponent.map_conj {L : Subgroup G} (hL : IsComponent G L) (g : G) :
    IsComponent G (L.map (MulAut.conj g).toMonoidHom) :=
  hL.map_equiv (MulAut.conj g)

/-- Isomorphisms identify the sets of components in both directions. -/
theorem isComponent_map_equiv_iff (L : Subgroup G) (e : G ≃* H) :
    IsComponent H (L.map e.toMonoidHom) ↔ IsComponent G L := by
  constructor
  · intro h
    simpa [Subgroup.map_map] using h.map_equiv e.symm
  · exact fun h => h.map_equiv e

/-- The original component lies in its actual conjugate orbit. -/
theorem le_componentOrbit (L A : Subgroup G) : L ≤ componentOrbit L A :=
  le_iSup_conjugates L A

/-- The orbit lies in the subgroup generated by the component and the acting subgroup. -/
theorem componentOrbit_le_sup (L A : Subgroup G) : componentOrbit L A ≤ L ⊔ A :=
  iSup_conjugates_le_sup L A

/-- The acting subgroup normalizes the actual conjugate orbit. -/
theorem le_normalizer_componentOrbit (L A : Subgroup G) :
    A ≤ normalizer (componentOrbit L A) := le_normalizer_iSup_conjugates L A

/-- Orbit generation replaces the component without changing the generated overgroup. -/
theorem componentOrbit_sup (L A : Subgroup G) : componentOrbit L A ⊔ A = L ⊔ A :=
  le_antisymm (sup_le (componentOrbit_le_sup L A) le_sup_right)
    (sup_le_sup_right (le_componentOrbit L A) A)

/-- The component calculus used in the generated-overgroup reduction of GLS 26.24. -/
theorem IsComponent.orbit_properties {L : Subgroup G} (hL : IsComponent G L)
    (A : Subgroup G) (hA : ¬ A ≤ normalizer L) :
    Group.IsPerfect (componentOrbit L A) ∧
      ((componentOrbit L A).subgroupOf (L ⊔ A)).Normal ∧
      ⁅componentOrbit L A, A⁆ = componentOrbit L A :=
  ⟨hL.orbit_isPerfect A, componentOrbit_normal_subgroupOf_sup L A,
    hL.commutator_orbit_eq_self A hA⟩

end Theory.GroupTheory

end
