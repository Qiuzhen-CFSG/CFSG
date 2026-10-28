module

public import Theory.SpecificGroups.Alternating.StrongClosureObstruction
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization
public import Theory.Alternating.OddCentralCovers

/-!
# The alternating rows in the Bender component inspection

Apply the proved six- and seven-letter fusion obstructions to the original
selected U and distinguished z, restricting only along the actual Sylow
embedding in H. The symmetric extension and its marked Sylow placement
are constructed from the component equivalence and the source action.
There is no assumption that U lies in the symmetric subgroup.

The two nonsplit triple covers are excluded separately: their actual centers
have order three, while O(H)=1 passes to each subnormal component. Thus all
four alternatives in source 1.1.5(3)(c),(d) are excluded once that theorem
supplies their specified isomorphisms and actions. Its earlier-source
producer still owns selecting those rows; the other four rows and the
Bender inner-action equality remain separate obligations.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520 and
Lemma 1.1.5(3)(c),(d), pp.501--502 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

omit [Finite G] in
private theorem local_strong_closure (w : LocalControlWitness T M)
    (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G)) :
    IsStronglyClosedSet (w.U.subgroupOf H : Set H) (S : Subgroup H) ⊤ := by
  constructor
  · intro x hx
    obtain ⟨y, hy, he⟩ := hUS hx
    exact (Subtype.ext he : y = x) ▸ hy
  · intro x hx g _ hg
    exact w.strongly_closed.2 x hx g (mem_top _) (hST (mem_map_of_mem H.subtype hg))

/-- The actual distinguished z cannot induce a transposition on an A6 component.
The embedding and its Sylow placement are constructed from the marked action. -/
theorem LocalControlWitness.false_of_alternating_six_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H)
    (e : L ≃* alternatingGroup (Fin 6)) (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (haction : ∀ a : alternatingGroup (Fin 6),
      (e.symm (MulAut.conjNormal t a) : G) = w.z * (e.symm a : G) * w.z⁻¹) : False := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let : IsMulCommutative (w.U.subgroupOf H) :=
    w.U.comap_injective_isMulCommutative H.subtype_injective
  have hzH : w.z ∈ H := (map_subtype_le _ : (S : Subgroup H).map H.subtype ≤ H)
    (hUS w.z_mem)
  let z : H := ⟨w.z, hzH⟩
  let e' := (subgroupOfEquivOfLe hL.1).trans e
  apply AlternatingStrongClosure.false_of_alternating_six_transposition S
    (w.U.subgroupOf H) (L.subgroupOf H) (local_strong_closure w H S hUS hST)
    hL.2.1 e' z w.z_mem (Subtype.ext (w.z_order ▸ pow_orderOf_eq_one w.z))
    (fun s hs => ?_) t ht (fun a => ?_)
  · exact Subtype.ext (w.z_central s (hST (mem_map_of_mem H.subtype hs))).eq
  · exact Subtype.ext (haction a)

/-- The actual distinguished z cannot induce three transpositions on an A7 component. -/
theorem LocalControlWitness.false_of_alternating_seven_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H)
    (e : L ≃* alternatingGroup (Fin 7)) (t : Equiv.Perm (Fin 7))
    (ht : t.cycleType = {2, 2, 2})
    (haction : ∀ a : alternatingGroup (Fin 7),
      (e.symm (MulAut.conjNormal t a) : G) = w.z * (e.symm a : G) * w.z⁻¹) : False := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let : IsMulCommutative (w.U.subgroupOf H) :=
    w.U.comap_injective_isMulCommutative H.subtype_injective
  have hzH : w.z ∈ H := (map_subtype_le _ : (S : Subgroup H).map H.subtype ≤ H)
    (hUS w.z_mem)
  let z : H := ⟨w.z, hzH⟩
  let e' := (subgroupOfEquivOfLe hL.1).trans e
  apply AlternatingStrongClosure.false_of_alternating_seven_triple S
    (w.U.subgroupOf H) (L.subgroupOf H) (local_strong_closure w H S hUS hST)
    hL.2.1 e' z w.z_mem (Subtype.ext (w.z_order ▸ pow_orderOf_eq_one w.z))
    (fun s hs => ?_) t ht (fun a => ?_)
  · exact Subtype.ext (w.z_central s (hST (mem_map_of_mem H.subtype hs))).eq
  · exact Subtype.ext (haction a)

private theorem not_subnormal_cubic_center {D : Type*} [Group D] [Finite D]
    (K : Subgroup D) (hK : K.IsSubnormal) (hcore : pPrimeCore 2 D = ⊥)
    (hc : Nat.card (center K) = 3) : False := by
  have hKcore := hK.pPrimeCore_eq_bot hcore K
  have hcb : center K = ⊥ := (pPrimeCore_eq_bot_iff.mp hKcore) _ inferInstance
    (by rw [hc]; decide)
  rw [hcb, card_bot] at hc
  omega

/-- The source O(H)=1 excludes the actual nonsplit triple cover of A6. -/
theorem false_of_triple_six_component (H L : Subgroup G) (hL : IsComponentIn L H)
    (hcore : pPrimeCore 2 H = ⊥) (e : L ≃* Atlas.Codes.HexEvenAutomorphisms) : False := by
  apply not_subnormal_cubic_center (L.subgroupOf H) hL.2.1 hcore
  exact (Nat.card_congr (Subgroup.centerCongr ((subgroupOfEquivOfLe hL.1).trans e)).toEquiv).trans
    Representation.Hexacode.even_center_card

/-- The source O(H)=1 excludes the actual nonsplit triple cover of A7. -/
theorem false_of_triple_seven_component (H L : Subgroup G) (hL : IsComponentIn L H)
    (hcore : pPrimeCore 2 H = ⊥)
    (e : L ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) : False := by
  apply not_subnormal_cubic_center (L.subgroupOf H) hL.2.1 hcore
  exact (Nat.card_congr (Subgroup.centerCongr ((subgroupOfEquivOfLe hL.1).trans e)).toEquiv).trans
    GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card

end CFSG.Quasithin.Chapter2.BenderFusion
