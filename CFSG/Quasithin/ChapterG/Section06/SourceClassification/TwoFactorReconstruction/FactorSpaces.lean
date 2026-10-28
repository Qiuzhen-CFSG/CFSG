module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.FixedKernel
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product

/-!
# The original pair of moved spaces

Injectivity on one moved summand and the given direct decomposition in the
fixed quotient imply that the two original summands are disjoint. Product
generation gives their full sum. Their invariance then makes each factor
centralize the other moved space. The subgroup inclusion adapter retains
the actual factors when passing from the normal closure back to G.

Source: Aschbacher–Smith, G.6.4(1)–(2), printed pp.345–346.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06.TwoFactorReconstruction
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

theorem original_spaces_disjoint (d : SourceTwoFactorCase ρ)
    (hf : Disjoint d.firstSpace.toSubmodule ρ.invariants) :
    Disjoint d.firstSpace.toSubmodule d.secondSpace.toSubmodule := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro v ⟨h₁, h₂⟩
  have hz : ρ.invariants.mkQ v = 0 := d.decomposition.disjoint.eq_bot.le
    ⟨⟨v, h₁, rfl⟩, ⟨v, h₂, rfl⟩⟩
  exact hf.eq_bot.le ⟨h₁, (Submodule.Quotient.mk_eq_zero _).mp hz⟩

theorem original_spaces_sum (d : SourceTwoFactorCase ρ)
    (h₁ : d.firstSpace.toSubmodule = moved ρ d.first)
    (h₂ : d.secondSpace.toSubmodule = moved ρ d.second)
    (hfull : moved ρ ⊤ = ⊤) :
    d.firstSpace.toSubmodule ⊔ d.secondSpace.toSubmodule = ⊤ := by
  apply top_unique
  rw [← hfull]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, _, v, _, rfl⟩
  obtain ⟨a, b, rfl⟩ := d.product.exists_mul g
  have ha : ρ a (ρ b v) - ρ b v ∈ d.firstSpace.toSubmodule := by
    rw [h₁]
    exact Submodule.subset_span ⟨a, a.property, ρ b v, Submodule.mem_top, rfl⟩
  have hb : ρ b v - v ∈ d.secondSpace.toSubmodule := by
    rw [h₂]
    exact Submodule.subset_span ⟨b, b.property, v, Submodule.mem_top, rfl⟩
  have hh := (d.firstSpace.toSubmodule ⊔ d.secondSpace.toSubmodule).add_mem
    ((le_sup_left : d.firstSpace.toSubmodule ≤
      d.firstSpace.toSubmodule ⊔ d.secondSpace.toSubmodule) ha)
    ((le_sup_right : d.secondSpace.toSubmodule ≤
      d.firstSpace.toSubmodule ⊔ d.secondSpace.toSubmodule) hb)
  change ρ ((a : D) * b) v - v ∈ d.firstSpace.toSubmodule ⊔ d.secondSpace.toSubmodule
  simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hh

theorem original_cross_commutator (d : SourceTwoFactorCase ρ)
    (h₁ : d.firstSpace.toSubmodule = moved ρ d.first)
    (h₂ : d.secondSpace.toSubmodule = moved ρ d.second)
    (hf : Disjoint d.firstSpace.toSubmodule ρ.invariants) :
    subspaceCommutator ρ d.secondSpace.toSubmodule d.first = ⊥ ∧
    subspaceCommutator ρ d.firstSpace.toSubmodule d.second = ⊥ := by
  have hd := original_spaces_disjoint d hf
  constructor
  · apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, hv, rfl⟩
    apply hd.eq_bot.le
    constructor
    · rw [h₁]
      exact Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩
    · exact d.secondSpace.toSubmodule.sub_mem (d.secondSpace.apply_mem_toSubmodule a hv) hv
  · apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, v, hv, rfl⟩
    apply hd.eq_bot.le
    constructor
    · exact d.firstSpace.toSubmodule.sub_mem (d.firstSpace.apply_mem_toSubmodule b hv) hv
    · rw [h₂]
      exact Submodule.subset_span ⟨b, hb, v, Submodule.mem_top, rfl⟩

variable {G : Type*} [Group G]

theorem hasModelOn_subtype {ρ : Representation (ZMod 2) G V}
    (K : Subgroup G) (A : Subgroup K) (U : Submodule (ZMod 2) V)
    {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) B W) (h : HasModelOn (ρ.comp K.subtype) A U τ) :
    HasModelOn ρ (A.map K.subtype) U τ := by
  obtain ⟨e, f, hs, he⟩ := h
  let j := A.equivMapOfInjective K.subtype K.subtype_injective
  have hj (a : A.map K.subtype) : ((j.symm a : A) : G) = (a : G) :=
    congrArg Subtype.val (j.apply_symm_apply a)
  have hs' (a : A.map K.subtype) (v : U) : ρ a v ∈ U := by
    simpa only [MonoidHom.comp_apply, coe_subtype, hj] using hs (j.symm a) v
  refine ⟨j.symm.trans e, f, hs', ?_⟩
  intro a v
  have hh := he (j.symm a) v
  simpa only [MonoidHom.comp_apply, coe_subtype, hj, MulEquiv.trans_apply] using hh

theorem smallFactorModel_subtype {ρ : Representation (ZMod 2) G V}
    (K : Subgroup G) (A : Subgroup K) (U : Submodule (ZMod 2) V)
    (h : SmallFactorModel (ρ.comp K.subtype) A U) :
    SmallFactorModel ρ (A.map K.subtype) U := by
  rcases h with h | h | h
  · exact Or.inl (hasModelOn_subtype K A U _ h)
  · exact Or.inr (Or.inl (hasModelOn_subtype K A U _ h))
  · exact Or.inr (Or.inr (hasModelOn_subtype K A U _ h))

/-- Restriction and the actual inclusion give the same displacement space. -/
theorem commutator_subtype_map (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) (A : Subgroup K) (U : Submodule (ZMod 2) V) :
    subspaceCommutator (ρ.comp K.subtype) U A =
      subspaceCommutator ρ U (A.map K.subtype) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact ⟨a, mem_map_of_mem K.subtype ha, w, hw, rfl⟩
  · rintro ⟨a, ⟨b, hb, rfl⟩, w, hw, rfl⟩
    exact ⟨b, hb, w, hw, rfl⟩

end CFSG.Quasithin.ChapterG.Section06.TwoFactorReconstruction
