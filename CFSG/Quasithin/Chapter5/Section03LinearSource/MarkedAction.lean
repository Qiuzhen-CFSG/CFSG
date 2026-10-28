module
public import Theory.GroupTheory.Amalgam.RankTwo
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Faithful marked actions and their exact inner preimage

An action on a native group carries both source endpoint conjugations through
one compatible marking. When the native endpoints generate, the whole source
overlap acts by the corresponding inner automorphisms. If the native overlap
is self-normalizing, faithfulness gives the converse. This is the inner-kernel
step used to realize the full linear normalizers in Aschbacher–Smith 5.3.2,
printed p.659 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G X : Type*} [Group G] [Group X]

/-- A single faithful action on the native carrier, with both local markings. -/
structure MarkedAction (P Q D : Subgroup G) (R U : Subgroup X) where
  left : P ≃* R
  right : Q ≃* U
  middle : (P ⊓ Q : Subgroup G) ≃* (R ⊓ U : Subgroup X)
  left_middle : ∀ b, (left (inclusion inf_le_left b)).val = (middle b).val
  right_middle : ∀ b, (right (inclusion inf_le_right b)).val = (middle b).val
  middle_le : P ⊓ Q ≤ D
  action : D →* MulAut X
  faithful : Function.Injective action
  left_action : ∀ (g : D) (x : P), ∃ hx : g.val*x.val*g.val⁻¹ ∈ P,
    (left ⟨g.val*x.val*g.val⁻¹,hx⟩).val = action g (left x).val
  right_action : ∀ (g : D) (x : Q), ∃ hx : g.val*x.val*g.val⁻¹ ∈ Q,
    (right ⟨g.val*x.val*g.val⁻¹,hx⟩).val = action g (right x).val

namespace MarkedAction
variable {P Q D : Subgroup G} {R U : Subgroup X} (a : MarkedAction P Q D R U)

private theorem preserved (P : Subgroup G) (R : Subgroup X) (e : P ≃* R)
    (ρ : D →* MulAut X)
    (hc : ∀ (g : D) (x : P), ∃ hx : g.val*x.val*g.val⁻¹ ∈ P,
      (e ⟨g.val*x.val*g.val⁻¹,hx⟩).val = ρ g (e x).val) (g : D) :
    R.map (ρ g).toMonoidHom = R := by
  have hle (g : D) : R.map (ρ g).toMonoidHom ≤ R := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨h,he⟩ := hc g (e.symm ⟨x,hx⟩)
    rw [e.apply_symm_apply] at he
    exact he ▸ (e ⟨_,h⟩).property
  apply le_antisymm (hle g)
  intro x hx
  refine ⟨(ρ g)⁻¹ x,?_,by simp⟩
  have hh := hle g⁻¹ (mem_map_of_mem (ρ g⁻¹).toMonoidHom hx)
  rw [map_inv] at hh
  exact hh

theorem preserves_left (g : D) : R.map (a.action g).toMonoidHom = R :=
  preserved P R a.left a.action a.left_action g

theorem preserves_right (g : D) : U.map (a.action g).toMonoidHom = U :=
  preserved Q U a.right a.action a.right_action g

theorem inner_on_overlap (hgen : R ⊔ U = ⊤) (b : (P ⊓ Q : Subgroup G)) :
    a.action (inclusion a.middle_le b) = MulAut.conj (a.middle b).val := by
  have hleft (x : P) : a.action (inclusion a.middle_le b) (a.left x).val =
      (a.middle b).val * (a.left x).val * (a.middle b).val⁻¹ := by
    obtain ⟨hx,he⟩ := a.left_action (inclusion a.middle_le b) x
    rw [←he,←a.left_middle b]
    change (a.left ((inclusion inf_le_left b) * x * (inclusion inf_le_left b)⁻¹)).val = _
    rw [map_mul,map_mul,map_inv]
    rfl
  have hright (x : Q) : a.action (inclusion a.middle_le b) (a.right x).val =
      (a.middle b).val * (a.right x).val * (a.middle b).val⁻¹ := by
    obtain ⟨hx,he⟩ := a.right_action (inclusion a.middle_le b) x
    rw [←he,←a.right_middle b]
    change (a.right ((inclusion inf_le_right b) * x * (inclusion inf_le_right b)⁻¹)).val = _
    rw [map_mul,map_mul,map_inv]
    rfl
  have he : (⊤ : Subgroup X) ≤ (a.action (inclusion a.middle_le b)).toMonoidHom.eqLocus
      (MulAut.conj (a.middle b).val).toMonoidHom := by
    rw [←hgen]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · change a.action _ x = (a.middle b).val * x * (a.middle b).val⁻¹
      simpa only [a.left.apply_symm_apply] using hleft (a.left.symm ⟨x,hx⟩)
    · change a.action _ x = (a.middle b).val * x * (a.middle b).val⁻¹
      simpa only [a.right.apply_symm_apply] using hright (a.right.symm ⟨x,hx⟩)
  ext x
  exact he (mem_top x)

/-- The inner preimage is the WHOLE source overlap. -/
theorem inner_iff (hgen : R ⊔ U = ⊤)
    (hself : normalizer ((R ⊓ U : Subgroup X) : Set X) = R ⊓ U) (g : D) :
    a.action g ∈ (MulAut.conj : X →* MulAut X).range ↔ g.val ∈ P ⊓ Q := by
  constructor
  · rintro ⟨x,hx⟩
    have hnorm : x ∈ normalizer ((R ⊓ U : Subgroup X) : Set X) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [hx]
      change (R ⊓ U).map (a.action g).toMonoidHom = R ⊓ U
      rw [map_inf _ _ _ (a.action g).injective,a.preserves_left,a.preserves_right]
    have hxB : x ∈ R ⊓ U := hself ▸ hnorm
    let b := a.middle.symm ⟨x,hxB⟩
    have hh : a.action (inclusion a.middle_le b) = a.action g := by
      rw [a.inner_on_overlap hgen,a.middle.apply_symm_apply,hx]
    have hg := congrArg Subtype.val (a.faithful hh)
    exact hg ▸ b.property
  · intro hg
    exact ⟨(a.middle ⟨g.val,hg⟩).val,(a.inner_on_overlap hgen ⟨g.val,hg⟩).symm⟩
end MarkedAction
end CFSG.Quasithin.Chapter5.Section03LinearSource

namespace CFSG.Quasithin.Chapter5.Section03LinearSource
open Subgroup
variable {G X : Type*} [Group G] [Group X] {P Q D : Subgroup G} {R U : Subgroup X}
/-- Reverse both endpoint markings together. -/
def MarkedAction.reverse (a : MarkedAction P Q D R U) : MarkedAction Q P D U R where
  left := a.right
  right := a.left
  middle := (MulEquiv.subgroupCongr (inf_comm _ _)).trans
    (a.middle.trans (MulEquiv.subgroupCongr (inf_comm _ _)))
  left_middle b := a.right_middle ⟨b.val, b.property.2, b.property.1⟩
  right_middle b := a.left_middle ⟨b.val, b.property.2, b.property.1⟩
  middle_le := ((inf_comm _ _).le.trans a.middle_le)
  action := a.action
  faithful := a.faithful
  left_action := a.right_action
  right_action := a.left_action
end CFSG.Quasithin.Chapter5.Section03LinearSource
