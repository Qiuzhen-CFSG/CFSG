module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.FixedPoints
public import Stellmacher.ElementaryAbelianMaxGlobalClosure
public import Theory.GroupTheory.NormalizerCentralizerSupplement

/-!
# Campbell II.5.1 on the original marked local group

The moving maximum elementary subgroup gives S=J(S)O₂(H), and O₂(H)
normalizes J(S). The original minimal-parabolic hypothesis supplies one
maximal overgroup M of S. For every Z centralized by J(S) but not by J(H),
the normal-closure supplement argument proves N_H(Z)≤M. Sylow conjugacy
identifies this normal closure with the actual global Thompson subgroup.

Thus the same genuine maximal subgroup controls all points used in Campbell's
two-overgroup comparison. The later replacement contradiction and uniform
characteristic-pair selection are separate conclusions.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.2 and II.5.1,
printed pp.25–27; Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J] {e : B →* H}
 {F : Type} [Field F] [CharP F 2] [Finite F]

theorem InLocalClass.thompson_sup_core_eq_sylow (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) :
    Campbell.J (d.sylow : Subgroup H) ⊔ pCore 2 H = (d.sylow : Subgroup H) := by
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), ¬ A ≤ pCore 2 H := by
    by_contra! hn
    have hJQ : elementaryAbelianMaxJ (d.sylow : Subgroup H) ≤ pCore 2 H := sSup_le hn
    apply h.thompson_moves_moved hB d.sylow hS.symm
    exact hJQ.trans (Subgroup.le_centralizer_iff.mp
      (h.moved_le_coreOmegaCenter.trans (fun x hx =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2)))
  obtain ⟨A,hA,hAQ⟩ := hex
  apply le_antisymm (sup_le (sSup_le fun _ hA => hA.1) (pCore_isPGroup.le_sylow_of_normal d.sylow))
  exact (h.maxElementary_sup_core_eq_sylow hB m d A hA hAQ).ge.trans
    (sup_le_sup (le_sSup hA) le_rfl)

theorem InLocalClass.exists_campbell_maximal_normalizer_bound (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) :
    ∃ M : Subgroup H, (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤ ∧
      ∀ Z : Subgroup H, Z ≤ centralizer (Campbell.J (d.sylow : Subgroup H) : Set H) →
        ¬ Z ≤ centralizer (Campbell.J (⊤ : Subgroup H) : Set H) →
        normalizer (Z : Set H) ≤ M := by
  obtain ⟨S0,he,hS0⟩ := h.sylow
  have hu : Order.HasUniqueMaximalOver (d.sylow : Subgroup H) ⊤ := by
    rw [hS,he]
    exact hS0.1
  obtain ⟨M,hM,_⟩ := hu.2
  refine ⟨M,hM.1,hM.2,?_⟩
  intro Z hZ hn
  have hQT : pCore 2 H ≤ normalizer (Campbell.J (d.sylow : Subgroup H) : Set H) := by
    intro q hq
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ (d.sylow : Subgroup H)).map (MulAut.conj q).toMonoidHom = _
    rw [←elementaryAbelianMaxJ_map_equiv]
    have hSq : (d.sylow : Subgroup H).map (MulAut.conj q).toMonoidHom = (d.sylow : Subgroup H) :=
      mem_normalizer_iff_map_conj_eq.mp ((d.sylow : Subgroup H).le_normalizer
        (pCore_isPGroup.le_sylow_of_normal d.sylow hq))
    rw [hSq]
    rfl
  apply normalizer_le_unique_maximal_of_noncentral_closure (d.sylow : Subgroup H)
    (Campbell.J (d.sylow : Subgroup H)) (pCore 2 H) Z M hu hM
    (InLocalClass.thompson_sup_core_eq_sylow h hB m d hS) hQT (Subgroup.le_centralizer_iff.mp hZ)
  intro hc
  apply hn
  apply Subgroup.le_centralizer_iff.mpr
  change elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ centralizer (Z : Set H)
  rw [elementaryAbelianMaxJ_top_eq_normalClosure_sylow d.sylow]
  exact hc
end CFSG.Quasithin.ChapterC.GlaubermanNiles
