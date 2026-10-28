module
public import Theory.GroupTheory.TwoPlaneCover.Rows
/-! # Exact rows of the two marked planes
Elementary full preimages preserve involution centralizers and their indices.
The row of the opposite plane is therefore the entire commutator row and is
disjoint from the marked kernel. Source: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.TwoPlaneCover
variable {E Q:Type*} [Group E] [Group Q] [Finite E] [Finite Q]
theorem marked_cover_rows (f:E→*Q) (hf:Function.Surjective f)
    (P₀ P₁ P:Subgroup Q) (hP:P=P₀∨P=P₁) (q:ℕ) (hq:1≤q)
    (hgen:P₀⊔P₁=⊤) (hZ:center Q≤P₀⊓P₁)
    [IsElementaryAbelian 2 (P₀.comap f)] [IsElementaryAbelian 2 (P₁.comap f)]
    (hcQ:_root_.commutator Q≤center Q)
    (hplanes:∀t:Q,t^2=1→t∉center Q→centralizer ({t}:Set Q)=P₀∨centralizer ({t}:Set Q)=P₁)
    (hindex:∀t:Q,t^2=1→t∉center Q→(centralizer ({t}:Set Q)).index=q)
    (hfull:∀t:Q,t^2=1→t∉P→P⊔centralizer ({t}:Set Q)=⊤) :
    (∀a∈P.comap f,Nat.card (⁅(⊤:Subgroup E),zpowers a⁆:Subgroup E)≤q) ∧
    (∀a:E,(f a)^2=1→f a∉P→
      q≤Nat.card (⁅P.comap f,zpowers a⁆:Subgroup E) ∧
      Disjoint (⁅P.comap f,zpowers a⁆:Subgroup E) f.ker) := by
  have hc:=class_two f hf P₀ P₁ hgen hZ hcQ
  have he (a:E) (ht:(f a)^2=1) (hz:f a∉center Q) :
      centralizer ({a}:Set E)=(centralizer ({f a}:Set Q)).comap f := by
    have hh:IsMulCommutative ((centralizer ({f a}:Set Q)).comap f):=by
      rcases hplanes (f a) ht hz with h|h
      all_goals rw [h];infer_instance
    let :=hh
    exact centralizer_eq_comap f a
  have hi:IsElementaryAbelian 2 (P.comap f):=by rcases hP with rfl|rfl <;> infer_instance
  let :=hi
  constructor
  · intro a ha
    have ht:(f a)^2=1:=by rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian a ha,map_one]
    by_cases hz:f a∈center Q
    · have hza:a∈center E:=preimage_center_le_center f hf P₀ P₁ hgen hZ hz
      have hrow:(⁅(⊤:Subgroup E),zpowers a⁆:Subgroup E)=⊥:=by
        rw [commutator_comm,commutator_eq_bot_iff_le_centralizer,coe_top,centralizer_univ]
        exact zpowers_le.mpr hza
      rw [hrow,Nat.card_unique]
      exact hq
    · rw [commutator_comm,commutator_card f hf hc a (he a ht hz),hindex (f a) ht hz]
  · intro a ht hp
    have hz:f a∉center Q:=by
      intro hz
      rcases hP with rfl|rfl
      · exact hp (hZ hz).1
      · exact hp (hZ hz).2
    have hrow:⁅P.comap f,zpowers a⁆=⁅(⊤:Subgroup E),zpowers a⁆:=by
      apply ClassTwo.commutator_row_eq_of_sup_centralizer hc
      rw [he a ht hz]
      exact comap_sup_eq_top f hf P _ (hfull (f a) ht hp)
    rw [hrow,commutator_comm]
    exact ⟨(commutator_card f hf hc a (he a ht hz)).trans (hindex (f a) ht hz) |>.ge,
      commutator_disjoint_kernel f hc a (he a ht hz)⟩
end Subgroup.TwoPlaneCover
