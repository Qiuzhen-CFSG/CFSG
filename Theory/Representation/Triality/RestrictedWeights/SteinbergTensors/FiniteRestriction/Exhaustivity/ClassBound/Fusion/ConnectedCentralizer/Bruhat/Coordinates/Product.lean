module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Basic

/-!
# Coordinates from successive root-subgroup factorizations

Induct on the ordered root list. A leading root group normalizing the subgroup
of later roots makes their product a subgroup, hence the whole generated group.
Trivial intersection makes that two-factor product unique. The actual
one-parameter isomorphisms then give existence and injectivity of all scalar
coordinates. No Chevalley pinning or root-system realization is used here.

This is the group-theoretic assembly step for GLS3, Theorem 1.12.7(a), and
Steinberg 6.2(b): `refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

open scoped Pointwise

universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] {K : Variety k} [AlgebraicGroup K]
  {T : ClosedSubgroup K}

private noncomputable def rootParameterEquiv (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (a : D.Root) : k ≃ (D.rootSubgroup a).toSubgroup :=
  (Multiplicative.ofAdd.trans (additiveGroupPointEquiv k).symm).trans
    ((p a).toMulEquiv.toEquiv.trans (D.rootSubgroup a).pointEquiv)

private lemma ordered_mem (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (rs : List D.Root) (c : Fin rs.length → k) :
    toralOrderedRootProduct D p rs c ∈ RootSubgroupGenerated D {a | a ∈ rs} := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact rootSubgroup_le_RootSubgroupGenerated D (List.get_mem rs i)
    (rootParameterEquiv D p (rs.get i) (c i)).property

private lemma ordered_cons (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (a : D.Root) (rs : List D.Root) (c : Fin (a :: rs).length → k) :
    toralOrderedRootProduct D p (a :: rs) c =
      (rootParameterEquiv D p a (c 0)).val *
        toralOrderedRootProduct D p rs (fun i => c i.succ) := by
  rw [toralOrderedRootProduct, List.ofFn_succ, List.prod_cons]
  rfl

private lemma generated_cons (D : RootGroupData K T) (a : D.Root) (rs : List D.Root) :
    RootSubgroupGenerated D {b | b ∈ a :: rs} =
      (D.rootSubgroup a).toSubgroup ⊔ RootSubgroupGenerated D {b | b ∈ rs} := by
  rw [show {b | b ∈ a :: rs} = {a} ∪ {b | b ∈ rs} by ext; simp,
    RootSubgroupGenerated_union, RootSubgroupGenerated_singleton]

private theorem ordered_coordinates_of_suffixes (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (rs : List D.Root)
    (hnormal : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ≤
        Subgroup.normalizer (RootSubgroupGenerated D {b | b ∈ bs} : Set (Variety.Point K)))
    (hdisjoint : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ⊓ RootSubgroupGenerated D {b | b ∈ bs} = ⊥) :
    Function.Injective (toralOrderedRootProduct D p rs) ∧
      ∀ x ∈ RootSubgroupGenerated D {a | a ∈ rs},
        ∃ c, toralOrderedRootProduct D p rs c = x := by
  induction rs with
  | nil =>
    constructor
    · intro c d _
      funext i
      exact Fin.elim0 i
    · intro x hx
      have hx1 : x = 1 := by
        simpa [RootSubgroupGenerated] using hx
      exact ⟨Fin.elim0, by simpa [toralOrderedRootProduct] using hx1.symm⟩
  | cons a rs ih =>
    have suffix (b : D.Root) (bs : List D.Root) (h : (b :: bs).IsSuffix rs) :
        (b :: bs).IsSuffix (a :: rs) := h.trans (List.suffix_cons a rs)
    obtain ⟨hinj, hcover⟩ := ih
      (fun b bs h => hnormal b bs (suffix b bs h))
      (fun b bs h => hdisjoint b bs (suffix b bs h))
    have hn := hnormal a rs (List.suffix_refl _)
    have hd := hdisjoint a rs (List.suffix_refl _)
    constructor
    · intro c d h
      rw [ordered_cons, ordered_cons] at h
      let xc := rootParameterEquiv D p a (c 0)
      let xd := rootParameterEquiv D p a (d 0)
      let yc := toralOrderedRootProduct D p rs (fun i => c i.succ)
      let yd := toralOrderedRootProduct D p rs (fun i => d i.succ)
      have hyc := ordered_mem D p rs (fun i => c i.succ)
      have hyd := ordered_mem D p rs (fun i => d i.succ)
      have he : (xd : Variety.Point K)⁻¹ * xc = yd * yc⁻¹ := by
        change (xc : Variety.Point K) * yc = xd * yd at h
        calc
          (xd : Variety.Point K)⁻¹ * xc =
              (xd : Variety.Point K)⁻¹ * (xc * yc) * yc⁻¹ := by group
          _ = yd * yc⁻¹ := by rw [h]; group
      have hone : (xd : Variety.Point K)⁻¹ * xc = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← hd]
        refine ⟨(D.rootSubgroup a).toSubgroup.mul_mem
          ((D.rootSubgroup a).toSubgroup.inv_mem xd.property) xc.property, ?_⟩
        rw [he]
        exact Subgroup.mul_mem _ hyd (Subgroup.inv_mem _ hyc)
      have hx : xc = xd := Subtype.ext (inv_mul_eq_one.mp hone).symm
      have hhead : c 0 = d 0 := (rootParameterEquiv D p a).injective hx
      have htail : (fun i : Fin rs.length => c i.succ) =
          (fun i => d i.succ) := by
        apply hinj
        exact mul_left_cancel (by simpa only [hhead] using h)
      funext i
      exact Fin.cases hhead (fun j => congrFun htail j) i
    · intro x hx
      rw [generated_cons] at hx
      have hprod := Subgroup.coe_mul_of_left_le_normalizer_right
        (D.rootSubgroup a).toSubgroup (RootSubgroupGenerated D {b | b ∈ rs}) hn
      change x ∈ (↑((D.rootSubgroup a).toSubgroup ⊔
        RootSubgroupGenerated D {b | b ∈ rs}) : Set (Variety.Point K)) at hx
      rw [hprod] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨t, ht⟩ := (rootParameterEquiv D p a).surjective ⟨y, hy⟩
      obtain ⟨c, hc⟩ := hcover z hz
      refine ⟨Fin.cons t c, ?_⟩
      rw [ordered_cons]
      simpa [hc] using congrArg (fun q : (D.rootSubgroup a).toSubgroup =>
        (q : Variety.Point K) * z) ht

/-- Retain the prescribed root order in both uniqueness and coverage. This
version supplies callers whose literal coordinate order is already fixed. -/
public theorem toralOrderedRootProduct_unique_and_covers_of_suffixes (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (rs : List D.Root)
    (hnormal : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ≤
        Subgroup.normalizer (RootSubgroupGenerated D {b | b ∈ bs} : Set (Variety.Point K)))
    (hdisjoint : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ⊓ RootSubgroupGenerated D {b | b ∈ bs} = ⊥) :
    Function.Injective (toralOrderedRootProduct D p rs) ∧
      ∀ x ∈ RootSubgroupGenerated D {a | a ∈ rs},
        ∃ c, toralOrderedRootProduct D p rs c = x :=
  ordered_coordinates_of_suffixes D p rs hnormal hdisjoint

/-- A list of root groups has unique coordinates if each root normalizes and
meets trivially the group generated by its successors. The parametrizations
are arbitrary algebraic isomorphisms with the additive group. -/
public theorem nonempty_toralRootCoordinates_of_suffixes (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (P : Set D.Root) (rs : List D.Root) (hnd : rs.Nodup)
    (hmem : ∀ a, a ∈ rs ↔ a ∈ P)
    (hnormal : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ≤
        Subgroup.normalizer (RootSubgroupGenerated D {b | b ∈ bs} : Set (Variety.Point K)))
    (hdisjoint : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ⊓ RootSubgroupGenerated D {b | b ∈ bs} = ⊥) :
    Nonempty (ToralRootCoordinates D p P) := by
  obtain ⟨hinj, hcover⟩ := ordered_coordinates_of_suffixes D p rs hnormal hdisjoint
  have hset : {a | a ∈ rs} = P := Set.ext hmem
  exact ⟨{ roots := rs
           nodup := hnd
           mem_roots := hmem
           injective := hinj
           covers := by simpa only [hset] using hcover }⟩

end Theory.AlgebraicGroup
