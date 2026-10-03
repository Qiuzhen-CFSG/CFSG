module
public import Theory.GroupTheory.ElementaryEightIndexTwoGeometry
public import Mathlib.GroupTheory.Sylow

/-!
# Ambient normalizers from index-two elementary-eight geometry

The distinguished order-32 normalizer embeds into every normalizer in the
ambient conjugacy class of the distinguished eight. A Sylow two-subgroup of
such an ambient normalizer embeds into a local elementary-eight normalizer.
The explicit non-embedding hypothesis excludes order 64, giving the bound 32.
Sylow conjugacy then excludes an elementary-sixteen local normalizer, since
it would embed into the distinguished normalizer. Thus every member of the
conjugacy class is self-centralizing in its Sylow overgroups and has local
normalizer order 32.

Source: MacWilliams, Trans. AMS 150 (1970), assertions (xxiii)–(xxiv),
printed p.384, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

private theorem embed_in_sylow
    {H K : Type*} [Group H] [Group K] [Finite K]
    (hH : IsPGroup 2 H) (f : H →* K) (hf : Function.Injective f)
    (P : Sylow 2 K) : ∃ j : H →* P, Function.Injective j := by
  have hp : IsPGroup 2 f.range := hH.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  let j := (Q.equiv P).toMonoidHom.comp
    ((inclusion hQ).comp f.rangeRestrict)
  refine ⟨j, (Q.equiv P).injective.comp ((inclusion_injective hQ).comp ?_)⟩
  intro x y hxy
  exact hf (congrArg Subtype.val hxy)

private noncomputable def normalizer_equiv
    {H K : Type*} [Group H] [Group K] (E : Subgroup H) (e : H ≃* K) :
    normalizer (E : Set H) ≃* normalizer (E.map e.toMonoidHom : Set K) :=
  (e.subgroupMap (normalizer (E : Set H))).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq E e))

private noncomputable def local_normalizer_equiv
    {G : Type*} [Group G] (U T : Subgroup G) (hUT : U ≤ T) :
    normalizer (U.subgroupOf T : Set T) ≃*
      ((T ⊓ normalizer (U : Set G) : Subgroup G)) := by
  exact (MulEquiv.subgroupCongr (subgroupOf_normalizer_eq hUT).symm).trans
    (((normalizer (U : Set G)).subgroupOf T).equivMapOfInjective T.subtype
      T.subtype_injective |>.trans (MulEquiv.subgroupCongr (by
        rw [subgroupOf_map_subtype, inf_comm])))

private theorem normalizer_sylow_bound
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (f : normalizer (centralizer ({t} : Set S) : Set S) →*
      normalizer (U : Set G)) (hf : Function.Injective f)
    (P : Sylow 2 (normalizer (U : Set G))) : Nat.card P ≤ 32 := by
  let N := normalizer (U : Set G)
  let I := (P : Subgroup N).map N.subtype
  have hIP : IsPGroup 2 I := P.isPGroup'.map _
  obtain ⟨T, hIT⟩ := hIP.exists_le_sylow
  let UN := U.subgroupOf N
  let : IsElementaryAbelian 2 UN := IsElementaryAbelian.subgroupOf U.le_normalizer
  have hUP : UN ≤ P := (IsElementaryAbelian.isPGroup 2 UN).le_sylow_of_normal P
  have hUT : U ≤ T := by
    intro u hu
    exact hIT ⟨⟨u, U.le_normalizer hu⟩, hUP hu, rfl⟩
  let F := U.subgroupOf (T : Subgroup G)
  let e := T.equiv S
  let D := F.map e.toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hUT
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  have hD : Nat.card D = 8 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv).trans hU
  let j : P →* normalizer (F : Set T) :=
    { toFun := fun p => ⟨⟨p.val.val, hIT (mem_map_of_mem N.subtype p.property)⟩, by
        rw [← subgroupOf_normalizer_eq hUT]
        exact p.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro p q hpq
    exact Subtype.ext (Subtype.ext (congrArg (fun x => x.val.val) hpq))
  let k := (normalizer_equiv F e).toMonoidHom.comp j
  have hk : Function.Injective k := (normalizer_equiv F e).injective.comp hj
  have hcard : Nat.card P ≤ Nat.card (normalizer (D : Set S)) :=
    Nat.card_le_card_of_injective k hk
  rcases h.normalizer_cases D inferInstance hD with hh | hh | hh
  · omega
  · obtain ⟨i, hi⟩ := embed_in_sylow (S.isPGroup'.to_subgroup _) f hf P
    exact False.elim (hh.2 (k.comp i) (hk.comp hi))
  · omega

private theorem normalizer_local_profile
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (f : normalizer (centralizer ({t} : Set S) : Set S) →*
      normalizer (U : Set G)) (hf : Function.Injective f)
    (T : Sylow 2 G) (hUT : U ≤ T) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) = U ∧
      Nat.card ((T : Subgroup G) ⊓ normalizer (U : Set G) : Subgroup G) = 32 := by
  let N := normalizer (U : Set G)
  let F := U.subgroupOf (T : Subgroup G)
  let e := T.equiv S
  let D := F.map e.toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hUT
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  have hD : Nat.card D = 8 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv).trans hU
  let a := (normalizer_equiv F e).symm.trans
    (local_normalizer_equiv U (T : Subgroup G) hUT)
  let k := (inclusion (show (T : Subgroup G) ⊓ N ≤ N from inf_le_right)).comp a.toMonoidHom
  have hk : Function.Injective k := (inclusion_injective (show (T : Subgroup G) ⊓ N ≤ N from inf_le_right)).comp a.injective
  let P : Sylow 2 N := Classical.choice inferInstance
  obtain ⟨j, hj⟩ := embed_in_sylow (S.isPGroup'.to_subgroup _) k hk P
  have hbound := normalizer_sylow_bound S h U hU f hf P
  have hcard : Nat.card (normalizer (D : Set S)) ≤ 32 :=
    (Nat.card_le_card_of_injective j hj).trans hbound
  have hfirst : centralizer (D : Set S) = D ∧
      Nat.card (normalizer (D : Set S)) = 32 := by
    rcases h.normalizer_cases D inferInstance hD with hh | hh | hh
    · exact hh
    · omega
    · obtain ⟨i, hi⟩ := embed_in_sylow (S.isPGroup'.to_subgroup _) f hf P
      have hbij := hi.bijective_of_nat_card_le (h.normalizer_card ▸ hbound)
      let b := (MulEquiv.ofBijective i hbij).symm.toMonoidHom.comp j
      have hb : Function.Injective b := (MulEquiv.ofBijective i hbij).symm.injective.comp hj
      let : IsElementaryAbelian 2 (normalizer (D : Set S)) := hh.1
      let : IsElementaryAbelian 2 (⊤ : Subgroup (normalizer (D : Set S))) := by
        have hh := IsElementaryAbelian.subgroupOf (p := 2)
          (H := normalizer (D : Set S)) (K := normalizer (D : Set S)) le_rfl
        rwa [subgroupOf_eq_top.mpr le_rfl] at hh
      let A := (⊤ : Subgroup (normalizer (D : Set S))).map b
      have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
      have hcA : Nat.card A = 16 := by
        rw [card_map_of_injective hb, Nat.card_congr (topEquiv (G := normalizer (D : Set S))).toEquiv]
        exact hh.2
      exact False.elim (h.normalizer_no_sixteen A hA hcA)
  refine ⟨?_, (Nat.card_congr a.toEquiv).symm.trans hfirst.2⟩
  apply le_antisymm ?_ (le_inf hUT U.le_centralizer)
  rintro x ⟨hxT, hxC⟩
  let xT : T := ⟨x, hxT⟩
  have hm : e xT ∈ centralizer (D : Set S) := by
    rintro _ ⟨u, hu, rfl⟩
    have hc : u * xT = xT * u := Subtype.ext (hxC u hu)
    change e u * e xT = e xT * e u
    simpa only [map_mul] using congrArg e hc
  rw [hfirst.1] at hm
  obtain ⟨u, hu, he⟩ := hm
  have he' : u = xT := e.injective he
  change (xT : G) ∈ U
  rw [← he']
  exact hu

namespace ElementaryEightIndexTwoGeometry

/-- The distinguished normalizer embeds into the normalizer of every ambient
conjugate of the distinguished elementary eight. -/
private theorem conjugate_normalizer_embedding
    {G : Type*} [Group G] (S : Sylow 2 G) (t : S) (g : G) :
    ∃ f : normalizer (centralizer ({t} : Set S) : Set S) →*
      normalizer (((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom : Set G), Function.Injective f := by
  let E := centralizer ({t} : Set S)
  let U := E.map (S : Subgroup G).subtype
  let k : normalizer (E : Set S) →* normalizer (U : Set G) :=
    { toFun := fun n => ⟨n.val.val, E.le_normalizer_map (S : Subgroup G).subtype
        (mem_map_of_mem (S : Subgroup G).subtype n.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun n : normalizer (U : Set G) => (n : G)) he))
  exact ⟨(normalizer_equiv U (MulAut.conj g)).toMonoidHom.comp k,
    (normalizer_equiv U (MulAut.conj g)).injective.comp hk⟩

/-- The normalizer of each ambient conjugate of the distinguished elementary
eight has Sylow two-order at most 32. -/
public theorem conjugate_normalizer_sylow_bound
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (g : G)
    (P : Sylow 2 (normalizer
      (((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom : Set G))) : Nat.card P ≤ 32 := by
  let E := centralizer ({t} : Set S)
  let U := (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := h.centralizer_elementary
  let : IsElementaryAbelian 2 (E.map (S : Subgroup G).subtype) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hU : Nat.card U = 8 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective]
    exact h.centralizer_card
  obtain ⟨f, hf⟩ := conjugate_normalizer_embedding S t g
  exact normalizer_sylow_bound S h U hU f hf P

/-- In every ambient Sylow overgroup, a conjugate of the distinguished eight
is self-centralizing and has normalizer of order 32. -/
public theorem conjugate_local_profile
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (g : G) (T : Sylow 2 G)
    (hUT : ((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
      (MulAut.conj g).toMonoidHom ≤ T) :
    (T : Subgroup G) ⊓ centralizer
      (((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom : Set G) =
      ((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom ∧
    Nat.card ((T : Subgroup G) ⊓ normalizer
      (((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) = 32 := by
  let E := centralizer ({t} : Set S)
  let U := (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := h.centralizer_elementary
  let : IsElementaryAbelian 2 (E.map (S : Subgroup G).subtype) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hU : Nat.card U = 8 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective]
    exact h.centralizer_card
  obtain ⟨f, hf⟩ := conjugate_normalizer_embedding S t g
  exact normalizer_local_profile S h U hU f hf T hUT

/-- A conjugate of the distinguished eight is self-centralizing in every
ambient two-subgroup containing it. -/
public theorem conjugate_self_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {R : Subgroup S} {t : S} (h : ElementaryEightIndexTwoGeometry R t)
    (g : G) (P : Subgroup G) (hp : IsPGroup 2 P)
    (hUP : ((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
      (MulAut.conj g).toMonoidHom ≤ P) :
    P ⊓ centralizer
      (((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom : Set G) =
      ((centralizer ({t} : Set S)).map (S : Subgroup G).subtype).map
        (MulAut.conj g).toMonoidHom := by
  obtain ⟨T, hPT⟩ := hp.exists_le_sylow
  have he := (h.conjugate_local_profile S g T (hUP.trans hPT)).1
  apply le_antisymm ((inf_le_inf_right _ hPT).trans he.le)
  exact le_inf hUP (he.symm.le.trans inf_le_right)

end ElementaryEightIndexTwoGeometry
