module
public import Theory.Representation.SL2.FullFixedIndex
public import Theory.Representation.SL2.TwoSubgroupFixedIndex
public import Theory.Representation.SL2SylowFixedRecognition.Complementary

/-!
# Sharp Sylow fixed spaces and commutator covering

For a nontrivial binary SL₂(2ⁿ) action, two generating Sylows with fixed
codimension n have fixed spaces spanning the whole module. The uniform
involution lower bound makes both Sylows quadratic. More generally, a
quadratic Sylow pair whose fixed spaces span has its Sylow moved space
covering its fixed space modulo the whole ambient fixed space. The proof
uses the Sylow trace and retains arbitrary fixed central attachments.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(g),
printed p.47. The literal group application is
`Glauberman.PushingUpSL2DegreeCovering`.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem sharp_sylow_fixed_spaces (ρ : Representation (ZMod 2) SL(2,F) V)
    (hnt : ∃ g, ρ g ≠ 1) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R T : Sylow 2 SL(2,F)) (hgen : (R : Subgroup SL(2,F)) ⊔ T = ⊤)
    (hR : fixedCodim ρ R = n) (hT : fixedCodim ρ T = n) :
    fixedSpace ρ R ⊔ fixedSpace ρ T = ⊤ ∧
      fixedCodim ρ ⊤ = 2*n ∧
      SL2SylowFixedRecognition.FixedSpaceHypotheses ρ R := by
  have hi : fixedSpace ρ R ⊓ fixedSpace ρ T = fixedSpace ρ ⊤ := by
    have he : fixedSpace ρ ((R : Subgroup _) ⊔ T) = fixedSpace ρ R ⊓ fixedSpace ρ T := ρ.invariants_comp_sup _ _
    rw [hgen] at he
    exact he.symm
  have hd := (fixedSpace ρ R).finrank_sup_add_finrank_inf_eq (fixedSpace ρ T)
  rw [hi] at hd
  have hdimR := fixedCodim_add_finrank ρ (R : Subgroup SL(2,F))
  have hdimT := fixedCodim_add_finrank ρ (T : Subgroup SL(2,F))
  have hdimG := fixedCodim_add_finrank ρ ⊤
  have hlow := fixedCodim_top_lower ρ hnt hn hF
  have hu := Submodule.finrank_le (fixedSpace ρ R ⊔ fixedSpace ρ T)
  have hspan : fixedSpace ρ R ⊔ fixedSpace ρ T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    omega
  refine ⟨hspan,by omega,?_,?_⟩
  · apply top_unique
    rw [←hspan]
    apply sup_le (le_iSup_maps ρ _)
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) R T
    change fixedSpace ρ ((R : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom) ≤ _
    rw [SL2SylowFixedRecognition.fixedSpace_conjugate]
    exact le_iSup (fun g => (fixedSpace ρ R).map (ρ g)) g
  · intro r hr hr1
    have hr2 := Matrix.SpecialLinearGroup.twoSubgroup_pow_two
      (R : Subgroup SL(2,F)) R.isPGroup' ⟨r,hr⟩
    have hl := involution_fixedCodim_lower ρ hnt hn hF r hr1
      (congrArg Subtype.val hr2)
    have hle := fixedSpace_antitone ρ (zpowers_le.mpr hr)
    symm
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hd := fixedCodim_add_finrank ρ (zpowers r)
    have hm := Submodule.finrank_mono hle
    omega

end Representation.SL2

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem sylow_moved_fixed_cover_of_quadratic_pair
    (ρ : Representation (ZMod 2) G V) (R T : Sylow 2 G)
    (hgen : (R : Subgroup G) ⊔ T = ⊤)
    (hspan : fixedSpace ρ R ⊔ fixedSpace ρ T = ⊤)
    (hR : IsQuadratic ρ R) (hT : IsQuadratic ρ T) :
    subspaceCommutator ρ ⊤ R ⊔ fixedSpace ρ ⊤ = fixedSpace ρ R := by
  have hm (A : Subgroup G) (hA : IsQuadratic ρ A) :
      subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩ b
    exact hA b b.property a ha v
  have hz : fixedSpace ρ ⊤ = fixedSpace ρ R ⊓ fixedSpace ρ T := by
    have he : fixedSpace ρ ((R : Subgroup _) ⊔ T) = fixedSpace ρ R ⊓ fixedSpace ρ T := ρ.invariants_comp_sup _ _
    rw [hgen] at he
    exact he
  have hgens : (⨆ g : G, (fixedSpace ρ R).map (ρ g)) = ⊤ := by
    apply top_unique
    rw [←hspan]
    apply sup_le (le_iSup_maps ρ _)
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq G R T
    change fixedSpace ρ ((R : Subgroup G).map (MulAut.conj g).toMonoidHom) ≤ _
    rw [SL2SylowFixedRecognition.fixedSpace_conjugate]
    exact le_iSup (fun g => (fixedSpace ρ R).map (ρ g)) g
  have hfull := moved_sup_fixedSpace_of_sylow_fixed_generators ρ ⊤ R
    (top_sup_eq _) (fixedSpace ρ R) le_rfl hgens
  have he := BinaryGroupAction.moved_iSup ρ
    (fun b : Bool => if b then (R : Subgroup G) else (T : Subgroup G))
  simp only [iSup_bool_eq,Bool.false_eq_true,↓reduceIte] at he
  rw [hgen] at he
  rw [he] at hfull
  apply le_antisymm (sup_le (hm _ hR) (fixedSpace_antitone ρ le_top))
  intro v hv
  obtain ⟨w,hw,z,hzv,rfl⟩ := Submodule.mem_sup.mp (hfull.ge (Submodule.mem_top (x := v)))
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hw
  have hbR : b ∈ fixedSpace ρ R := by
    have hh := (fixedSpace ρ R).sub_mem
      ((fixedSpace ρ R).sub_mem hv (fixedSpace_antitone ρ le_top hzv)) (hm _ hR ha)
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using hh
  have hbG : b ∈ fixedSpace ρ ⊤ := by rw [hz]; exact ⟨hbR,hm _ hT hb⟩
  exact Submodule.mem_sup.mpr ⟨a,ha,b+z,(fixedSpace ρ ⊤).add_mem hbG hzv,by abel⟩
end Representation.BinaryOffender
