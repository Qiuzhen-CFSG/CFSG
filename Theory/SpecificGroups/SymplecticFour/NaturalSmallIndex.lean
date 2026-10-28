module
public import Theory.SpecificGroups.SymplecticFour.CentralNaturalDerivedAmbient
public import Theory.GroupTheory.ClassTwoSmallIndex
/-!
# Index-four subgroups of central natural Sp₄(4) extensions

Every nonzero commutator row is the whole derived group, and its order is
at most four. If an index-four subgroup lost some derived elements, the
quotient by its derived subgroup would have center index at most64 and at
least256. This identifies the derived subgroup of the actual intersection
in MS93 (3.10), pp.880--881, without splitting the central kernel.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.ClassTwo
open Theory.SpecificGroups.SymplecticFour
variable {P A F : Type*} [Group P] [Finite P] [Group A]
  [Field F] [CharP F 2] [Finite F]

/-- An index-four subgroup retains the full derived group of a central
extension of the natural Sp₄(4) module. -/
theorem derived_eq_of_symplectic_section_index_le_four
    (hc : _root_.commutator P ≤ center P) (hF : Nat.card F = 4)
    (α : A →* MulAut P) (π : A →* Sp F) (hπ : Function.Surjective π)
    (f : P →* Multiplicative (Vector F)) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P)
    (hequiv : ∀ a v, (f (α a v)).toAdd = π a • (f v).toAdd)
    (hfix : ∀ a : A, ∀ c ∈ _root_.commutator P, α a c = c)
    (S : Subgroup P) (hi : S.index ≤ 4) :
    ⁅S,S⁆ = _root_.commutator P := by
  have hN : f.ker.index = 256 := by
    rw [index_ker,f.range_eq_top_of_surjective hf,card_top,
      Nat.card_congr Multiplicative.toAdd]
    norm_num [Theory.SpecificGroups.SymplecticFour.Vector,Nat.card_fun,Nat.card_sum,Nat.card_fin,hF]
  apply derived_eq_of_index_le_four_of_full_rows hc
    ((card_commutator_le_of_symplectic_section hc α π hπ f hf hker hequiv hfix).trans_eq hF)
    f.ker (by omega) _ S hi
  intro x hx
  exact commutator_eq_row_of_symplectic_section α π hπ f hker hequiv hfix x hx

variable {G : Type*} [Group G]

/-- The ambient formulation retains the literal intersection with Y and the
original conjugation and quotient maps. -/
theorem derived_intersection_eq_of_natural_central_section
    (L V Y : Subgroup G) [Finite V]
    (hVL : V ≤ L) (hLV : L ≤ normalizer (V : Set G)) (hF : Nat.card F = 4)
    (π : L →* Sp F) (hπ : Function.Surjective π)
    (f : V →* Multiplicative (Vector F)) (hf : Function.Surjective f)
    (hker : f.ker ≤ center V)
    (hequiv : ∀ (a : L) (v : V),
      (f ⟨(a : G) * v * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hLV a.property) v).mp v.property⟩).toAdd =
          π a • (f v).toAdd)
    (hfix : ⁅V,V⁆ ≤ centralizer (L : Set G))
    (hi : (Y.subgroupOf V).index ≤ 4) :
    ⁅V ⊓ Y,V ⊓ Y⁆ = ⁅V,V⁆ := by
  let α : L →* MulAut V := V.normalizerMonoidHom.comp (inclusion hLV)
  have hmap : (_root_.commutator V).map V.subtype = ⁅V,V⁆ := by
    rw [map_commutator_eq,range_subtype]
  have hcent : _root_.commutator V ≤ center V := by
    intro c hc
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    exact hfix (hmap ▸ mem_map_of_mem V.subtype hc) v (hVL v.property)
  have hfixed : ∀ a : L, ∀ c ∈ _root_.commutator V, α a c = c := by
    intro a c hc
    apply Subtype.ext
    change (a : G) * (c : G) * (a : G)⁻¹ = c
    have he := hfix (hmap ▸ mem_map_of_mem V.subtype hc) a a.property
    change (a : G) * (c : G) = (c : G) * a at he
    rw [he,mul_inv_cancel_right]
  have he := derived_eq_of_symplectic_section_index_le_four hcent hF α π hπ
    f hf hker hequiv hfixed (Y.subgroupOf V) hi
  have hm := congrArg (Subgroup.map V.subtype) he
  simpa only [map_commutator,subgroupOf_map_subtype,inf_comm,hmap] using hm
end Subgroup.ClassTwo
