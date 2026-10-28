module

public import Theory.GroupTheory.PGroup.NormalSubgroupUpperCentralBound
public import Theory.ElementaryAbelian.Basic

/-!
# Characteristic subgroups distinguished by their centralizers

The order of any fixed lower-central term of C_G(A) is unchanged by an
isomorphism carrying A to its image. If these orders distinguish a complete
family of normal elementary subgroups of a given order, every member is
characteristic. In a finite p-group the coverage need only be checked inside
the upper-central term determined by that order.

The third lower-central term is indexed by two: the term indexed by zero is
the whole centralizer. This convention is needed in the normal-eight
calculation for the J₄ Sylow group.

Source: functoriality of commutators and the upper-central bound in
`NormalSubgroupUpperCentralBound`; no finite model computation is assumed here.
-/

public section

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The order of the nth lower-central term of the intrinsic centralizer of A. -/
@[expose] noncomputable def centralizerLowerCentralCard (A : Subgroup G) (n : ℕ) : ℕ :=
  Nat.card ((⊤ : Subgroup (centralizer (A : Set G))).lowerCentralSeries n)

private theorem centralizer_map_mulEquiv (e : G ≃* H) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Centralizer lower-central orders are invariant under actual group isomorphisms. -/
theorem centralizerLowerCentralCard_map (e : G ≃* H) (A : Subgroup G) (n : ℕ) :
    centralizerLowerCentralCard (A.map e.toMonoidHom) n =
      centralizerLowerCentralCard A n := by
  let c : centralizer (A : Set G) ≃* centralizer (A.map e.toMonoidHom : Set H) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map_mulEquiv e A))
  have hmap : ((⊤ : Subgroup (centralizer (A : Set G))).lowerCentralSeries n).map
      c.toMonoidHom = (⊤ : Subgroup (centralizer (A.map e.toMonoidHom : Set H))).lowerCentralSeries n := by
    rw [map_lowerCentralSeries, map_top_of_surjective _ c.surjective]
  unfold centralizerLowerCentralCard
  rw [← hmap, card_map_of_injective c.injective]

/-- Pull characteristicity back through an actual group isomorphism. -/
theorem characteristic_of_map_mulEquiv (e : G ≃* H) (A : Subgroup G)
    (hA : (A.map e.toMonoidHom).Characteristic) : A.Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  let b : MulAut H := e.symm.trans (a.trans e)
  have hy := characteristic_iff_le_comap.mp hA b (mem_map_of_mem e.toMonoidHom hx)
  change e (a (e.symm (e x))) ∈ A.map e.toMonoidHom at hy
  rw [e.symm_apply_apply] at hy
  rcases hy with ⟨y, hy, he⟩
  have he' : y = a x := e.injective he
  change a x ∈ A
  exact he' ▸ hy


/-- A complete family with distinct centralizer invariants fixes every normal
 elementary subgroup of the specified order under every automorphism. Coverage
 inside Z_n suffices for subgroups of order p^n. -/
theorem characteristic_of_centralizer_profile [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) {n k : ℕ}
    {ι : Type*} (family : ι → Subgroup G)
    (hcover : ∀ A : Subgroup G, A.Normal → IsElementaryAbelian p A →
      Nat.card A = p ^ n → A ≤ upperCentralSeries G n → ∃ i, A = family i)
    (hdistinct : Function.Injective (fun i => centralizerLowerCentralCard (family i) k))
    (A : Subgroup G) [A.Normal] [IsElementaryAbelian p A]
    (hcard : Nat.card A = p ^ n) : A.Characteristic := by
  obtain ⟨i, hi⟩ := hcover A inferInstance inferInstance hcard
    (le_upperCentralSeries_of_card_eq_prime_pow hp A hcard)
  apply characteristic_iff_map_eq.mpr
  intro e
  have : (A.map e.toMonoidHom).Normal := MulEquiv.normal_map_iff.mpr inferInstance
  have : IsElementaryAbelian p (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hmapcard : Nat.card (A.map e.toMonoidHom) = p ^ n := by
    rw [card_map_of_injective e.injective, hcard]
  obtain ⟨j, hj⟩ := hcover (A.map e.toMonoidHom) inferInstance inferInstance hmapcard
    (le_upperCentralSeries_of_card_eq_prime_pow hp _ hmapcard)
  have hji : j = i := by
    apply hdistinct
    change centralizerLowerCentralCard (family j) k = centralizerLowerCentralCard (family i) k
    rw [← hj, ← hi, centralizerLowerCentralCard_map]
  rw [hj, hji, hi]

end Subgroup
