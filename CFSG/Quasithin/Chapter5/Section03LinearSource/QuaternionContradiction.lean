module
public import CFSG.Quasithin.Chapter5.Section03LinearSource.QuaternionCentralizer
public import CFSG.Quasithin.Chapter5.Section03CentralizerExceptional

/-!
# The marked quaternion contradiction in the actual centralizer

Transport both native quaternion factors through the one Sylow marking
and then into the literal ambient subgroup D. Their orders, intersection,
commutation and generation give the existing order-nine action theorem.
The original root plane keeps its order-eight intersection with Q and
its weak-closure property under the same embedding. The local two-group
normalizer bound contradicts the fixed cubic element supplied by that theorem.

The prepared Chapter6 row discharges every premise using its actual
normal closure, source index and binary flag. Source: Aschbacher--Smith
§5.3.7, printed p.661 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G : Type*} [Group G] [Finite G]

/-- Transport the native quaternion factors, the same marked root plane,
and the Sylow index to the literal centralizer before applying the
order-nine action contradiction. -/
theorem marked_quaternion_contradiction
    (c : Section03ExceptionalSylowModel.MarkedCopy G) (T : Sylow 2 G)
    (hT : c.carrier=(T : Subgroup G)) (D : Subgroup G)
    (hTD : (T : Subgroup G) ≤ D) (hQD : c.Q ≤ D)
    (hn : D ≤ normalizer (c.Q : Set G))
    (hself : D ⊓ centralizer (c.Q : Set G) ≤ c.Q)
    (hlower : 4 ≤ (T : Subgroup G).relIndex D)
    (hweak : ∀ g : G, c.V₁.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      c.V₁.map (MulAut.conj g).toMonoidHom=c.V₁)
    (htwo : IsPGroup 2 (D ⊓ normalizer (c.V₁ : Set G) : Subgroup G)) : False := by
  have hVT : c.V₁ ≤ (T : Subgroup G) := by
    rintro x ⟨a,ha,rfl⟩
    exact hT ▸ (c.equiv a).property
  have hVD := hVT.trans hTD
  let Q := c.Q.subgroupOf D
  let : Q.Normal := normal_subgroupOf_of_le_normalizer hn
  let V := c.V₁.subgroupOf D
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVD
  let e : Matrix.PSL3Four.SylowModel.Q ≃* Q :=
    (c.subgroupEquiv Matrix.PSL3Four.SylowModel.Q).trans (subgroupOfEquivOfLe hQD).symm
  let B := Matrix.PSL3Four.SylowModel.B.map e.toMonoidHom
  let E := Matrix.PSL3Four.SylowModel.D.map e.toMonoidHom
  have hcardQ : Nat.card Q=32 := (Nat.card_congr e.toEquiv).symm.trans
    Matrix.PSL3Four.SylowModel.card_Q
  have hcenter : Nat.card (center Q)=2 :=
    (Nat.card_congr (centerCongr e).toEquiv).symm.trans Matrix.PSL3Four.SylowModel.card_center_Q
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    ⟨(Matrix.PSL3Four.SylowModel.B.equivMapOfInjective e.toMonoidHom e.injective).symm.trans
      Matrix.PSL3Four.SylowModel.quaternionBEquiv⟩
  have hE : Nonempty (E ≃* QuaternionGroup 2) :=
    ⟨(Matrix.PSL3Four.SylowModel.D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans
      Matrix.PSL3Four.SylowModel.quaternionDEquiv⟩
  have hBE : Nat.card (B ⊓ E : Subgroup Q)=2 := by
    change Nat.card ((Matrix.PSL3Four.SylowModel.B.map e.toMonoidHom) ⊓
      (Matrix.PSL3Four.SylowModel.D.map e.toMonoidHom) : Subgroup Q)=2
    rw [←map_inf _ _ _ e.injective,card_map_of_injective e.injective,
      Matrix.PSL3Four.SylowModel.card_B_inf_D]
  have hcomm : ∀ b∈B, ∀ a∈E, b*a=a*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨a,ha,rfl⟩
    change e b*e a=e a*e b
    rw [←map_mul,←map_mul]
    exact congrArg e (Matrix.PSL3Four.SylowModel.B_D_commute b hb a ha)
  have hjoin : B ⊔ E=⊤ := by
    change (Matrix.PSL3Four.SylowModel.B.map e.toMonoidHom) ⊔
      (Matrix.PSL3Four.SylowModel.D.map e.toMonoidHom)=⊤
    rw [←Subgroup.map_sup,Matrix.PSL3Four.SylowModel.B_sup_D,map_top_of_surjective _ e.surjective]
  have hCQ : centralizer (Q : Set D) ≤ Q := by
    intro x hx
    apply hself
    refine ⟨x.property,?_⟩
    intro a ha
    exact congrArg Subtype.val (hx ⟨a,hQD ha⟩ ha)
  have hcardT : Nat.card (T.subtype hTD)=128 := by
    change Nat.card ((T : Subgroup G).subgroupOf D)=128
    rw [Nat.card_congr (subgroupOfEquivOfLe hTD).toEquiv,←hT]
    exact c.card_carrier
  have hcardV : Nat.card V=16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVD).toEquiv).trans c.card_V₁
  have hVQ : Nat.card (V ⊓ Q : Subgroup D)=8 := by
    change Nat.card ((c.V₁ ⊓ c.Q).subgroupOf D)=8
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hVD)).toEquiv]
    change Nat.card ((Matrix.PSL3Four.SylowModel.V₁.map c.embedding) ⊓
      (Matrix.PSL3Four.SylowModel.Q.map c.embedding) : Subgroup G)=8
    rw [←map_inf _ _ _ c.embedding_injective,card_map_of_injective c.embedding_injective,
      Matrix.PSL3Four.SylowModel.card_V₁_inf_Q]
  apply Section03CentralizerExceptional.exceptional_quaternion_core_contradiction
    Q hcardQ hCQ hcenter B E hB hE hBE hcomm hjoin (T.subtype hTD) hcardT hlower
    V hcardV hVQ (fun x hx => hVT hx)
  · intro g hg
    have hw : c.V₁.map (MulAut.conj (g:G)).toMonoidHom=c.V₁ := hweak g (by
      rintro _ ⟨v,hv,rfl⟩
      exact hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
        (show (⟨v,hVD hv⟩ : D)∈V from hv)))
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hw.le (mem_map_of_mem (MulAut.conj (g:G)).toMonoidHom hv)
    · intro hx
      obtain ⟨v,hv,hvx⟩ := hw.ge hx
      exact ⟨⟨v,hVD hv⟩,hv,Subtype.ext hvx⟩
  · rw [←subgroupOf_normalizer_eq hVD]
    have hh := htwo.comap_subtype (K := D)
    change IsPGroup 2 ((D ⊓ normalizer (c.V₁ : Set G)).subgroupOf D) at hh
    rwa [inf_subgroupOf_left] at hh
end CFSG.Quasithin.Chapter5.Section03LinearSource
