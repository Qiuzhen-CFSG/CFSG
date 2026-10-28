module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldNormal128
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelExtraspecial
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The original escaping Sylow contains an actual plus extraspecial kernel

The same normal order-128 subgroup already constructed inside the original
T is identified with the retained native two-central kernel. Its now proved
extraspecial and three-dihedral-factor structure transports through that
whole-group equivalence. Its index in the original T is exactly eight.
The original overgroup Y and the full involution centralizer remain separate
source conclusions, not assumptions of this construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_extraspecial128
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ P : Subgroup G, P≤(T : Subgroup G) ∧
      (T : Subgroup G)≤normalizer (P : Set G) ∧ Nat.card P=128 ∧
      IsExtraspecial 2 P ∧ (T : Subgroup G)⊓centralizer (P : Set G)≤P ∧
      P.relIndex (T : Subgroup G)=8 ∧
      Nonempty (P≃*DihedralCentralProductThree.Model) := by
  obtain ⟨P,hPT,hTP,hPc,_,hC,⟨e⟩⟩ :=
    original_tripleSix_escaping_normal128 h structural D a t ht heven hout
  have hTc := (original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout).1
  have hex : IsExtraspecial 2 P := IsExtraspecial.of_mulEquiv e.symm
    Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.kernel_extraspecial
  obtain ⟨eQ⟩ := Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.kernel_equiv_dihedral_three
  refine ⟨P,hPT,hTP,hPc,hex,hC,?_,⟨e.trans eQ⟩⟩
  have hh := (P.subgroupOf (T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hPT).toEquiv,hPc,hTc] at hh
  change (P.subgroupOf (T : Subgroup G)).index=8
  omega

end CFSG.Quasithin.Chapter12.Section07
