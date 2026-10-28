module
public import Theory.GroupTheory.PCoreCentralizerOvergroup
public import Theory.GroupTheory.CharacteristicTwoInheritance

/-!
# Local characteristic p from prime-order centralizers

If every centralizer of an element of order p has characteristic p, so does
all of N_G(R) for every nontrivial p-subgroup R. Choose z of order p in Z(R).
The subgroup C_{N_G(R)}(z) is the normalizer of R inside C_G(z), hence inherits
characteristic p. It contains the centralizer of O_p(N_G(R)), because R is
normal in its own normalizer and contains z. The proved core-centralizer
overgroup criterion finishes the argument.

This supplies the local-normalizer condition in Aschbacher--Smith 2.5.3(4),
printed p.553, for the PSL3(3) and M11 components of 2.5.2(3). No ambient
Sylow containment or even-characteristic inference is used.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

public theorem normalizer_core_selfCentralizing_of_prime_centralizers
    (hc : ∀ z : G, orderOf z = p →
      centralizer (pCore p (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) ≤
        pCore p (centralizer ({z} : Set G)))
    (R : Subgroup G) (hp : IsPGroup p R) (hne : R ≠ ⊥) :
    centralizer (pCore p (normalizer (R : Set G)) : Set (normalizer (R : Set G))) ≤
      pCore p (normalizer (R : Set G)) := by
  let : Nontrivial R := (nontrivial_iff_ne_bot _).mpr hne
  let := hp.center_nontrivial
  have hZp := hp.to_subgroup (center R)
  obtain ⟨n, hn, hcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center R) p
    (hcard ▸ dvd_pow_self p (by omega : n ≠ 0))
  let C := centralizer ({(z.val : G)} : Set G)
  let N := normalizer (R : Set G)
  let zN : N := ⟨z.val, R.le_normalizer z.val.property⟩
  have hRC : R ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp z.property ⟨x, hx⟩))
  have hC : centralizer (pCore p C : Set C) ≤ pCore p C :=
    hc z.val (by simpa only [orderOf_coe] using hz)
  have hNC : centralizer (pCore p (N.subgroupOf C) : Set (N.subgroupOf C)) ≤
      pCore p (N.subgroupOf C) := by
    rw [subgroupOf_normalizer_eq hRC]
    exact normalizer_core_selfCentralizing hC (R.subgroupOf C) hp.comap_subtype
  let e : centralizer ({zN} : Set N) ≃* N.subgroupOf C := {
    toFun x := ⟨⟨x, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
      x.val.property⟩
    invFun x := ⟨⟨x, x.property⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  apply centralizer_pCore_le_of_overgroup p (centralizer ({zN} : Set N))
    ((Theory.Quasithin.centralizer_pCore_le_iff p e).mpr hNC)
  have hRcore : R.subgroupOf N ≤ pCore p N :=
    le_sSup ⟨inferInstance, hp.comap_subtype⟩
  exact centralizer_le (Set.singleton_subset_iff.mpr (hRcore z.val.property))

omit [Finite G] [Fact p.Prime] in
/-- Transport the characteristic-p normalizer conclusion through an actual
isomorphism, keeping the specified subgroup and its literal normalizer. -/
public theorem normalizer_core_selfCentralizing_of_equiv
    {J : Type*} [Group J] (e : G ≃* J)
    (R : Subgroup G)
    (hc : centralizer (pCore p (normalizer (R.map e.toMonoidHom : Set J)) :
      Set (normalizer (R.map e.toMonoidHom : Set J))) ≤
      pCore p (normalizer (R.map e.toMonoidHom : Set J))) :
    centralizer (pCore p (normalizer (R : Set G)) : Set (normalizer (R : Set G))) ≤
      pCore p (normalizer (R : Set G)) := by
  exact (Theory.Quasithin.centralizer_pCore_le_iff p
    ((e.subgroupMap (normalizer (R : Set G))).trans
      (MulEquiv.subgroupCongr (map_normalizer_eq_of_bijective R e.bijective)))).mpr hc
end Subgroup
