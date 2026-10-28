module
public import Theory.Representation.PSL3Two.RankTwoOuterMovement
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySectionSource

/-!
# The original binary section forces an automizer of order eight

The representation of the literal quotient H/J retains the coordinates of
L/Z. Restricting it to the marked component image, an involution displacement
inside the two-dimensional seed image and full movement give the natural–dual
recognition. The actual quotient action of an outer Sylow element moves a
vector of that seed image, hence an original element of B modulo Z.

Restricting the same coordinate map to T, the order-four action of L on V
is therefore proper in the T-action. This proves the original centralizer
index is at least eight. The action, full-movement and displacement premises
are supplied by the source binary-section construction; neither a module
marking nor a separate implementing linear map is assumed.

Source: Aschbacher–Smith E.2.17, printed p.230.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearThree
variable {H M : Type*} [Group H] [Finite H] [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M] [Nontrivial M]

omit [Finite H] in
theorem outer_moves_binary_section_image
    (J K L Z B : Subgroup H) [J.Normal]
    (σ : Representation (ZMod 2) (H ⧸ J) M)
    (c : BinaryConjugationSection ⊤ L Z
      (σ.comp ((QuotientGroup.mk' J).comp (⊤ : Subgroup H).subtype)))
    (e : K.map (QuotientGroup.mk' J) ≃* BinaryLinearThree.Group)
    (hfull : subspaceCommutator
      (σ.comp ((K.map (QuotientGroup.mk' J)).subtype.comp e.symm.toMonoidHom)) ⊤ ⊤ = ⊤)
    (a : K.map (QuotientGroup.mk' J)) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hB : LinearMap.range (σ (a : H ⧸ J) - LinearMap.id) ≤ c.imageSpace B)
    (hdim : Module.finrank (ZMod 2) (c.imageSpace B) ≤ 2)
    (t : H) (α : MulAut (K.map (QuotientGroup.mk' J)))
    (hα : α ∉ MulAut.innerSubgroup (K.map (QuotientGroup.mk' J)))
    (hact : ∀ d : K.map (QuotientGroup.mk' J), (α d : H ⧸ J) =
      QuotientGroup.mk' J t * (d : H ⧸ J) * (QuotientGroup.mk' J t)⁻¹) :
    ∃ b : L, (b : H) ∈ B ∧ σ (QuotientGroup.mk' J t) (c.coordinates b).toAdd ≠
      (c.coordinates b).toAdd := by
  let D := K.map (QuotientGroup.mk' J)
  let ρ := σ.comp (D.subtype.comp e.symm.toMonoidHom)
  let β := MulAut.congr e α
  have hβ : β ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
    intro hb
    rw [←MulAut.map_innerSubgroup_congr e] at hb
    obtain ⟨δ,hδ,he⟩ := hb
    exact hα ((MulAut.congr e).injective he ▸ hδ)
  let F := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom (QuotientGroup.mk' J t))
  have hF : ∀ g v, F (ρ g v) = ρ (β g) (F v) := by
    intro g v
    have he : e.symm (β g) = α (e.symm g) := by simp [β,MulAut.congr_apply]
    change σ (QuotientGroup.mk' J t) (σ ((e.symm g : D) : H ⧸ J) v) =
      σ ((e.symm (β g) : D) : H ⧸ J) (σ (QuotientGroup.mk' J t) v)
    rw [he,hact]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hab : LinearMap.range (ρ (e a) - LinearMap.id) ≤ c.imageSpace B := by
    change LinearMap.range (σ ((e.symm (e a) : D) : H ⧸ J) - LinearMap.id) ≤ c.imageSpace B
    rwa [e.symm_apply_apply]
  obtain ⟨v,hv,hmove⟩ := BinaryLinearThree.RankTwoOuterRecognition.exists_moved_in_subspace
    ρ hfull (e a) (by rw [←map_pow,ha,map_one]) (fun hh => hne (e.injective (hh.trans e.map_one.symm)))
    (c.imageSpace B) hab hdim β hβ F hF
  obtain ⟨b,hb,he⟩ := (c.mem_imageSpace_iff B v).mp hv
  refine ⟨b,hb,?_⟩
  rw [he]
  exact hmove

/-- The actual T-automizer of V has order at least eight in the recognized binary section. -/
theorem eight_le_binary_section_automizer
    (J K L Z B V T : Subgroup H) [J.Normal]
    (σ : Representation (ZMod 2) (H ⧸ J) M)
    (c : BinaryConjugationSection ⊤ L Z
      (σ.comp ((QuotientGroup.mk' J).comp (⊤ : Subgroup H).subtype)))
    (e : K.map (QuotientGroup.mk' J) ≃* BinaryLinearThree.Group)
    (hfull : subspaceCommutator
      (σ.comp ((K.map (QuotientGroup.mk' J)).subtype.comp e.symm.toMonoidHom)) ⊤ ⊤ = ⊤)
    (a : K.map (QuotientGroup.mk' J)) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hB : LinearMap.range (σ (a : H ⧸ J) - LinearMap.id) ≤ c.imageSpace B)
    (hdim : Module.finrank (ZMod 2) (c.imageSpace B) ≤ 2)
    (hLT : L ≤ T) (hTV : T ≤ normalizer (V : Set H)) (hBV : B ≤ V)
    (hcomm : ⁅L,B⁆ ≤ Z)
    (hfour : (centralizer (V : Set H)).relIndex L = 4)
    (t : T) (α : MulAut (K.map (QuotientGroup.mk' J)))
    (hα : α ∉ MulAut.innerSubgroup (K.map (QuotientGroup.mk' J)))
    (hact : ∀ d : K.map (QuotientGroup.mk' J), (α d : H ⧸ J) =
      QuotientGroup.mk' J (t : H) * (d : H ⧸ J) * (QuotientGroup.mk' J (t : H))⁻¹) :
    8 ≤ (centralizer (V : Set H)).relIndex T := by
  let ρ := σ.comp ((QuotientGroup.mk' J).comp T.subtype)
  let cT : BinaryConjugationSection T L Z ρ := {
    section_le := hLT
    kernel_le := c.kernel_le
    normalized := le_top.trans c.normalized
    coordinates := c.coordinates
    onto := c.onto
    kernel_eq := c.kernel_eq
    equivariant := fun g b => c.equivariant ⟨g,mem_top _⟩ b }
  have hm := outer_moves_binary_section_image J K L Z B σ c e hfull
    a ha hne hB hdim (t : H) α hα hact
  let φ := V.normalizerMonoidHom.comp (inclusion hTV)
  have hk : φ.ker = (centralizer (V : Set H)).subgroupOf T := by
    ext t
    change V.normalizerMonoidHom (inclusion hTV t) = 1 ↔ _
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
    rfl
  have hcardL : Nat.card ((L.subgroupOf T).map φ) = 4 := by
    rw [←relIndex_ker,hk,subgroupOf,relIndex_comap,map_subgroupOf_eq_of_le hLT]
    exact hfour
  have hcardT : Nat.card φ.range = (centralizer (V : Set H)).relIndex T := by
    rw [←index_ker,hk]
    rfl
  rw [←hcardT]
  exact cT.eight_le_automizer_of_moving_section V B hTV hBV hcomm hcardL t hm
end CFSG.Quasithin.ChapterE.Witnesses.LinearThree
