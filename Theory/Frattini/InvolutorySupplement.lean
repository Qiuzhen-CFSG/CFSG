module
public import Theory.Frattini.BinarySquares
public import Theory.Frattini.PGroupMap
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Frattini subgroups with an involutory supplement

Let T = QE be a finite two-group, with E normalizing Q and every element
of E an involution or the identity. Then the ambient Frattini subgroup is
Phi(T) = Phi(Q)[Q,E] = Phi(Q)[Q,T]. The square formula
(qe)^2 = q^2 [q^{-1},e] e^2 proves the upper bound; both factors lie in
Phi(T) by Frattini functoriality and the commutator bound.

Only the subgroups need to be finite. The ambient group may be a free
amalgam, and no centrality or splitting of the supplement is assumed.
This standard two-group calculation supplies the retained Frattini factor
in the distance-two comparisons of MS93 (3.7), printed pp.873--876.
-/

public section
namespace Subgroup
open scoped commutatorElement

/-- An involutory supplement contributes exactly its commutators with the normal factor. -/
theorem frattini_map_eq_of_involutory_supplement {G : Type*} [Group G]
    (T Q E : Subgroup G) [Finite T] [Finite Q]
    (hpT : IsPGroup 2 T) (hpQ : IsPGroup 2 Q)
    (hjoin : Q ⊔ E = T) (hn : E ≤ normalizer (Q : Set G))
    (hE : ∀ e ∈ E, e^2=1) :
    (frattini T).map T.subtype = (frattini Q).map Q.subtype ⊔ ⁅Q,E⁆ := by
  let : Fact (IsPGroup 2 T) := ⟨hpT⟩
  let : Fact (IsPGroup 2 Q) := ⟨hpQ⟩
  have hQT : Q ≤ T := le_sup_left.trans_eq hjoin
  have hET : E ≤ T := le_sup_right.trans_eq hjoin
  apply le_antisymm
  · rw [map_le_iff_le_comap,hpT.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    have hx : x.val ∈ Q ⊔ E := hjoin.symm ▸ x.property
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hx
    obtain ⟨q,hq,e,he,heq⟩ := hx
    change x.val^2 ∈ (frattini Q).map Q.subtype ⊔ ⁅Q,E⁆
    rw [←heq]
    have hid : (q*e)^2=q^2*⁅q⁻¹,e⁆*e^2 := by
      simp only [pow_two,commutatorElement_def,inv_inv]
      group
    rw [hid,hE e he,mul_one]
    exact mul_mem_sup
      (mem_map_of_mem Q.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨q,hq⟩ : Q)))
      (commutator_mem_commutator (Q.inv_mem hq) he)
  · apply sup_le
    · have hm := map_mono (f := T.subtype)
        (frattini_map_le_of_isPGroup (p := 2) (inclusion hQT))
      rw [Subgroup.map_map,show T.subtype.comp (inclusion hQT)=Q.subtype from rfl] at hm
      exact hm
    · apply commutator_le.mpr
      intro q hq e he
      exact mem_map_of_mem T.subtype (commutator_le_frattini_of_isPGroup (p := 2)
        (commutator_mem_commutator (mem_top (⟨q,hQT hq⟩ : T)) (mem_top (⟨e,hET he⟩ : T))))

/-- The same formula expressed with the whole containing group as actor. -/
theorem frattini_map_eq_commutator_sup_of_involutory_supplement {G : Type*} [Group G]
    (T Q E : Subgroup G) [Finite T] [Finite Q]
    (hpT : IsPGroup 2 T) (hpQ : IsPGroup 2 Q)
    (hjoin : Q ⊔ E = T) (hn : E ≤ normalizer (Q : Set G))
    (hE : ∀ e ∈ E, e^2=1) :
    (frattini T).map T.subtype = (frattini Q).map Q.subtype ⊔ ⁅Q,T⁆ := by
  let : Fact (IsPGroup 2 T) := ⟨hpT⟩
  have he := frattini_map_eq_of_involutory_supplement T Q E hpT hpQ hjoin hn hE
  have hQT : Q ≤ T := le_sup_left.trans_eq hjoin
  have hET : E ≤ T := le_sup_right.trans_eq hjoin
  apply le_antisymm
  · rw [he]
    exact sup_le_sup_left (commutator_mono le_rfl hET) _
  · apply sup_le (le_sup_left.trans_eq he.symm)
    apply commutator_le.mpr
    intro q hq t ht
    exact mem_map_of_mem T.subtype (commutator_le_frattini_of_isPGroup (p := 2)
      (commutator_mem_commutator (mem_top (⟨q,hQT hq⟩ : T)) (mem_top (⟨t,ht⟩ : T))))

end Subgroup
