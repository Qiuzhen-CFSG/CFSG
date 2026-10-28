module
public import Glauberman.PushingUpQuadraticOffender
public import Theory.GroupTheory.SylowTwistedGeneratingPair

/-!
# Thompson subgroups in a fixed-normal-free pair

Maximum abelian subgroups transport along injective homomorphisms. For an
isomorphism between two ambient subgroups, this preserves both maximum
abelian orders and the literal Thompson subgroup. If the isomorphism fixes
no nontrivial normal subgroup, neither Thompson subgroup can lie in the
other member: such containment and equality of orders would identify the
two Thompson subgroups and violate the fixed-normal condition.

Consequently both members have maximum abelian subgroups outside their
intersection. This supplies the existence step of Niles4.3 and is preserved
in the recursive pair construction of4.4.

Source: Niles, *Pushing-up in finite groups* (1979), printed pp.44–45.
-/

public section
open Subgroup
namespace Glauberman
variable {G H : Type*} [Group G] [Group H]

theorem maximum_abelian_map_of_injective (f : G →* H) (hf : Function.Injective f)
    {S A : Subgroup G} (hA : A ∈ thompsonAbelianSubgroups S) :
    A.map f ∈ thompsonAbelianSubgroups (S.map f) := by
  let _ := hA.2.1
  refine ⟨map_mono hA.1,map_isMulCommutative A f,?_⟩
  intro B hB hBc
  have hpre : B.comap f ≤ S := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hB hx
    exact hf he ▸ hy
  have hprec : IsMulCommutative (B.comap f) := by
    let _ := hBc
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    apply hf
    simpa only [map_mul] using setLike_mul_comm (show f x ∈ B from hx) (show f y ∈ B from hy)
  have hb : (B.comap f).map f = B := map_comap_eq_self (hB.trans (map_le_range _ _))
  calc
    Nat.card B = Nat.card (B.comap f) := by
      calc
        Nat.card B = Nat.card ((B.comap f).map f) := congrArg (fun U : Subgroup H => Nat.card U) hb.symm
        _ = Nat.card (B.comap f) := card_map_of_injective hf
    _ ≤ Nat.card A := hA.2.2 _ hpre hprec
    _ = Nat.card (A.map f) := (card_map_of_injective hf).symm

theorem maximum_abelian_map_iff_of_injective (f : G →* H) (hf : Function.Injective f)
    {S A : Subgroup G} :
    A.map f ∈ thompsonAbelianSubgroups (S.map f) ↔ A ∈ thompsonAbelianSubgroups S := by
  refine ⟨?_,maximum_abelian_map_of_injective f hf⟩
  intro hA
  have hAc : IsMulCommutative A := by
    let _ := hA.2.1
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    apply hf
    simpa only [map_mul] using setLike_mul_comm (mem_map_of_mem f hx) (mem_map_of_mem f hy)
  have hAS : A ≤ S := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hA.1 (mem_map_of_mem f hx)
    exact hf he ▸ hy
  refine ⟨hAS,hAc,?_⟩
  intro B hB hBc
  let _ := hBc
  have h := hA.2.2 (B.map f) (map_mono hB) (map_isMulCommutative B f)
  simpa only [card_map_of_injective hf] using h

/-- Transport a maximum abelian subgroup through the actual subgroup isomorphism. -/
theorem maximum_abelian_map_pair {S T A : Subgroup G} (φ : S ≃* T)
    (hA : A ∈ thompsonAbelianSubgroups S) :
    ((A.subgroupOf S).map φ.toMonoidHom).map T.subtype ∈ thompsonAbelianSubgroups T := by
  have hlocal : A.subgroupOf S ∈ thompsonAbelianSubgroups (⊤ : Subgroup S) := by
    apply (maximum_abelian_map_iff_of_injective S.subtype S.subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le hA.1,←MonoidHom.range_eq_map,range_subtype] using hA
  have hphi := maximum_abelian_map_of_injective φ.toMonoidHom φ.injective hlocal
  rw [map_top_of_surjective _ φ.surjective] at hphi
  have h := maximum_abelian_map_of_injective T.subtype T.subtype_injective hphi
  simpa only [←MonoidHom.range_eq_map,range_subtype] using h

variable [Finite G]

/-- The ambient Thompson subgroup follows the same literal subgroup maps. -/
theorem thompson_map_pair (S T : Subgroup G) (φ : S ≃* T) :
    (((thompsonSubgroup S).subgroupOf S).map φ.toMonoidHom).map T.subtype =
      thompsonSubgroup T := by
  have he : (thompsonSubgroup S).subgroupOf S = thompsonSubgroup (⊤ : Subgroup S) := by
    apply map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le (thompsonSubgroup_le S),thompsonSubgroup_top_map_subtype]
  rw [he,thompsonSubgroup_top_map_mulEquiv φ,thompsonSubgroup_top_map_subtype]

/-- A fixed-normal-free isomorphism cannot identify two nontrivial Thompson
subgroups in the ambient group. -/
theorem thompson_ne_of_no_fixed_normal (S T : Subgroup G) (φ : S ≃* T)
    (hS : S ≠ ⊥)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥) :
    thompsonSubgroup S ≠ thompsonSubgroup T := by
  intro heq
  let A := (thompsonSubgroup S).subgroupOf S
  let _ : A.Characteristic := allAbelianThompson_subgroupOf_characteristic S
  have h := hno A inferInstance (by
    rw [map_subgroupOf_eq_of_le (thompsonSubgroup_le S)]
    exact (thompson_map_pair S T φ).trans heq.symm)
  have hmap := congrArg (Subgroup.map S.subtype) h
  rw [map_subgroupOf_eq_of_le (thompsonSubgroup_le S),Subgroup.map_bot] at hmap
  exact allAbelianThompson_ne_bot S hS hmap

omit [Finite G] in
/-- Literal transport preserves the order of every subgroup of the source. -/
theorem card_map_pair (S T A : Subgroup G) (φ : S ≃* T) (hAS : A ≤ S) :
    Nat.card (((A.subgroupOf S).map φ.toMonoidHom).map T.subtype) = Nat.card A := by
  rw [card_map_of_injective T.subtype_injective,card_map_of_injective φ.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv

private theorem maximum_abelian_mem_other {S T A : Subgroup G} (φ : S ≃* T)
    (hA : A ∈ thompsonAbelianSubgroups S) (hAT : A ≤ T) :
    A ∈ thompsonAbelianSubgroups T := by
  obtain ⟨B,hB⟩ := thompsonAbelianSubgroups_nonempty T
  have hpre := maximum_abelian_map_pair φ.symm hB
  have hc := hA.2.2 _ hpre.1 hpre.2.1
  rw [card_map_pair T S B φ.symm hB.1] at hc
  exact ⟨hAT,hA.2.1,fun C hC hCc => (hB.2.2 C hC hCc).trans hc⟩

/-- The Thompson subgroup of either member cannot be contained in the other
member of a nontrivial fixed-normal-free pair. This is the outside-existence
step at the start of Niles4.3. -/
theorem thompson_not_le_other_of_no_fixed_normal (S T : Subgroup G) (φ : S ≃* T)
    (hS : S ≠ ⊥)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥) :
    ¬ thompsonSubgroup S ≤ T ∧ ¬ thompsonSubgroup T ≤ S := by
  have hne := thompson_ne_of_no_fixed_normal S T φ hS hno
  have hc : Nat.card (thompsonSubgroup T) = Nat.card (thompsonSubgroup S) := by
    rw [←thompson_map_pair S T φ]
    exact card_map_pair S T (thompsonSubgroup S) φ (thompsonSubgroup_le S)
  constructor
  · intro hST
    have hle : thompsonSubgroup S ≤ thompsonSubgroup T := by
      apply sSup_le
      intro A hA
      exact le_sSup (maximum_abelian_mem_other φ hA ((le_sSup hA).trans hST))
    exact hne (eq_of_le_of_card_ge hle hc.le)
  · intro hTS
    have hle : thompsonSubgroup T ≤ thompsonSubgroup S := by
      apply sSup_le
      intro A hA
      exact le_sSup (maximum_abelian_mem_other φ.symm hA ((le_sSup hA).trans hTS))
    exact hne (eq_of_le_of_card_ge hle hc.ge).symm

/-- The actual maximum-abelian witnesses for both sides of Niles4.3. -/
theorem exists_maximum_abelian_outside_pair (S T : Subgroup G) (φ : S ≃* T)
    (hS : S ≠ ⊥)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥) :
    (∃ A, A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ S ⊓ T) ∧
    (∃ B, B ∈ thompsonAbelianSubgroups T ∧ ¬ B ≤ S ⊓ T) := by
  have h := thompson_not_le_other_of_no_fixed_normal S T φ hS hno
  constructor
  · by_contra hn
    apply h.1
    apply sSup_le
    intro A hA
    have hAQ : A ≤ S ⊓ T := by
      by_contra hout
      exact hn ⟨A,hA,hout⟩
    exact hAQ.trans inf_le_right
  · by_contra hn
    apply h.2
    apply sSup_le
    intro B hB
    have hBQ : B ≤ S ⊓ T := by
      by_contra hout
      exact hn ⟨B,hB,hout⟩
    exact hBQ.trans inf_le_left
end Glauberman
