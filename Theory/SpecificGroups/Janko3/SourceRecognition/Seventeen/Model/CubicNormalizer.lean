module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Torus
public import Theory.SpecificGroups.PSL2.CartanPanelFixedPoints

/-!
# The normalizer of an overlap cubic in the sixteen-field model

An actual cubic in the point-pair intersection has trivial field component.
Its nonidentity diagonal part fixes precisely the two distinguished points,
so its full normalizer preserves their unordered pair. The cubic is arbitrary
within the literal overlap; no chosen coordinate generator is assumed.
-/

public noncomputable section
open Subgroup MulAction
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

private theorem cubic_field_component {s : Model} (hs : orderOf s = 3) : s.right = 1 := by
  have h3 : s.right ^ 3 = 1 := by
    have hh := congrArg (SemidirectProduct.rightHom : Model →* Actor) (pow_orderOf_eq_one s)
    simpa only [hs,map_pow,map_one,SemidirectProduct.rightHom_eq_right] using hh
  have h2 : s.right ^ 2 = 1 := by
    have hc : Nat.card Actor = 2 := by rw [Nat.card_zpowers,fieldInvolution_order]
    simpa only [hc] using (pow_card_eq_one' (x := s.right))
  calc
    s.right = s.right ^ 2 * s.right := by rw [h2,one_mul]
    _ = 1 := by rw [←pow_succ,h3]

/-- Every actual cubic in the literal overlap fixes exactly the two marked points. -/
theorem overlap_cubic_fixed_pair {s : Model} (hs : orderOf s = 3)
    (hm : s ∈ point ⊓ pair) (x : Points) :
    s • x = x ↔ x = pInf F ∨ x = pZero F := by
  have hr := cubic_field_component hs
  obtain ⟨u,hu⟩ := (torus_range.symm ▸ (mem_overlap s).mp hm : s.left ∈ torusHom.range)
  have hu1 : u ≠ 1 := by
    intro h
    have hl : s.left = 1 := by simpa only [h,map_one] using hu.symm
    have he : s = 1 := SemidirectProduct.ext hl hr
    rw [he,orderOf_one] at hs
    omega
  rw [model_smul,hr,Subgroup.coe_one,fieldPoint_one,←hu]
  exact CartanPanel.diagonal_fixed_pair u (CartanPanel.diagonal_distinct u hu1) x

/-- The full normalizer of any actual overlap cubic lies in the actual pair stabilizer. -/
theorem overlap_cubic_normalizer_le_pair {s : Model} (hs : orderOf s = 3)
    (hm : s ∈ point ⊓ pair) : normalizer (zpowers s : Set Model) ≤ pair := by
  intro g hg
  have move_fixed (x : Points) (hx : s • x = x) : s • (g • x) = g • x := by
    have hn : g⁻¹ * s * g ∈ zpowers s := by
      have hh := (mem_normalizer_iff.mp ((normalizer (zpowers s : Set Model)).inv_mem hg) s).mp
        (mem_zpowers s)
      simpa only [inv_inv] using hh
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hn
    have hfix : (g⁻¹ * s * g) • x = x := by
      rw [←hn]
      exact mem_fixedBy_zpow hx n
    have he := congrArg (fun y : Points => g • y) hfix
    simpa only [mul_smul,smul_inv_smul] using he
  have hi := (overlap_cubic_fixed_pair hs hm (g • pInf F)).mp
    (move_fixed _ ((overlap_cubic_fixed_pair hs hm _).mpr (Or.inl rfl)))
  have hz := (overlap_cubic_fixed_pair hs hm (g • pZero F)).mp
    (move_fixed _ ((overlap_cubic_fixed_pair hs hm _).mpr (Or.inr rfl)))
  have hne : g • pInf F ≠ g • pZero F := (MulAction.injective g).ne inf_ne_zero
  have hp : (g • pInf F = pInf F ∧ g • pZero F = pZero F) ∨
      (g • pInf F = pZero F ∧ g • pZero F = pInf F) := by
    rcases hi with hi | hi <;> rcases hz with hz | hz
    · exact False.elim (hne (hi.trans hz.symm))
    · exact Or.inl ⟨hi,hz⟩
    · exact Or.inr ⟨hi,hz⟩
    · exact False.elim (hne (hi.trans hz.symm))
  rw [mem_pair]
  simpa only [model_smul,fieldPoint_inf,fieldPoint_zero] using hp

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
