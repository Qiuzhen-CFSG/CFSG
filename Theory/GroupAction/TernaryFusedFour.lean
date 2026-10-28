module

public import Theory.GroupAction.TernaryFusedFour.Reduction
public import Theory.GroupAction.TernaryFusedFour.MatrixClassification

/-!
# Ternary automizers with fused elementary Sylow involutions

The determinant reduction identifies the given automorphism subgroup with
an actual subgroup of SL₃(3). The order divisibility, elementary Sylow condition
and internal involution fusion are transported through that isomorphism.
The certified matrix classification then proves order twelve and normal
Sylow two-subgroups, and the isomorphism transports both conclusions back
to the original automorphism subgroup.

Source application: Bender (1974), (4.1), printed p.225, citing Janko (1966),
Lemma 3.1.
-/

namespace TernaryFusedFour

/-- The literal action group is isomorphic to an SL₃(3) subgroup with all
three local conditions preserved, and with no element of order four. -/
public theorem exists_specialLinear_model
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 27) (K : Subgroup (MulAut E))
    (hfour : 4 ∣ Nat.card K)
    (hel : ∀ P : Sylow 2 K, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : K, orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    ∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)),
      Nonempty (K ≃* H) ∧ 4 ∣ Nat.card H ∧
      (∀ P : Sylow 2 H, IsElementaryAbelian 2 P) ∧
      (∀ x : H, orderOf x ≠ 4) ∧
      (∀ t u : H, orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  obtain ⟨f, hf⟩ := exists_injective_specialLinear E hcard K hfour hel hfuse
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  refine ⟨f.range, ⟨e⟩, ?_, ?_, ?_, ?_⟩
  · rwa [← Nat.card_congr e.toEquiv]
  · intro Q
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective e.surjective 2 Q
    let := hel P
    exact IsElementaryAbelian.map e.toMonoidHom
  · intro x hx
    apply no_order_four_of_elementary_sylow hel (e.symm x)
    exact (e.symm.orderOf_eq x).trans hx
  · intro t u ht hu
    have hh := e.toMonoidHom.map_isConj (hfuse (e.symm t) (e.symm u)
      ((e.symm.orderOf_eq t).trans ht) ((e.symm.orderOf_eq u).trans hu))
    change IsConj (e (e.symm t)) (e (e.symm u)) at hh
    simpa only [MulEquiv.apply_symm_apply] using hh

/-- Transport the required order and Sylow normality from an actual model. -/
public theorem card_and_normal_sylow_of_equiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (hcard : Nat.card H = 12)
    (hnormal : ∀ P : Sylow 2 H, (P : Subgroup H).Normal) :
    Nat.card G = 12 ∧ ∀ P : Sylow 2 G, (P : Subgroup G).Normal := by
  refine ⟨(Nat.card_congr e.toEquiv).trans hcard, ?_⟩
  intro P
  exact MulEquiv.normal_map_iff.mp (hnormal (P.mapSurjective e.surjective))

/-- An automizer of an elementary abelian group of order 27, with order
divisible by four, elementary Sylow two-subgroups and one internal involution
class, has order twelve and normal Sylow two-subgroups. -/
public theorem card_and_normal_sylow
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hcard : Nat.card E = 27) (K : Subgroup (MulAut E))
    (hfour : 4 ∣ Nat.card K)
    (hel : ∀ P : Sylow 2 K, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : K, orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    Nat.card K = 12 ∧ ∀ P : Sylow 2 K, (P : Subgroup K).Normal := by
  obtain ⟨H, ⟨e⟩, hfour', hel', -, hfuse'⟩ :=
    exists_specialLinear_model E hcard K hfour hel hfuse
  obtain ⟨hcard', hnormal⟩ := specialLinear_card_and_normal_sylow H hfour' hel' hfuse'
  exact card_and_normal_sylow_of_equiv e hcard' hnormal

end TernaryFusedFour
