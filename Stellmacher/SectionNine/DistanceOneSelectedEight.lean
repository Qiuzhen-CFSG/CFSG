module
public import Stellmacher.SectionNine.DistanceOneTerminalCoreFactorSwap
public import Stellmacher.SectionNine.DistanceOneResidualCubicConjugation
public import Stellmacher.SectionNine.DistanceOneTerminalResidualGeneration
public import Theory.GroupTheory.QuaternionDiagonalActionSelection
public import Theory.GroupTheory.QuaternionDiagonalCentralizer

/-!
# The actual selected elementary eight at distance one

The original ambient distance-one hypotheses and explicit faithful/local
conclusions supply an elementary subgroup U of the exact Vstar of order8.
It contains the terminal center, is normal in the terminal residual and
normalized by the initial center, is moved by some terminal-core element,
and is self-centralizing inside Vstar.

Choose the intrinsic quaternion factors and an initial-center involution s
swapping them. The terminal-core factor-swap theorem supplies t for these
same factors, while the proved residual action supplies a nontrivial cubic g.
The actual modulo-Vstar conjugation relations distinguish s, which inverts g,
from t, which centralizes it. The intrinsic diagonal selector therefore gives
a diagonal normalized by Vstar, g and s but moved by t. Its retained factor
isomorphism supplies self-centralization inside Vstar.

Vstar and g generate the actual residual, so their normalization and the
proved residual containment give normality there. The order8 seed and the
outside involution s generate the order16 initial center, giving its full
normalization of U. The common factor intersection is the order2 Vstar center,
hence the terminal center. The moved core actor preserves the exceptional
subgroup exclusion required for the initial-vertex normalizer calculation.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48. This is an
existence theorem in the actual ambient context, with no selected-subgroup
assumption. The two local S4 normalizer quotients are subsequent results.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

private theorem le_of_index_two_of_outside
    {G : Type*} [Group G] (J A M : Subgroup G)
    (hindex : J.relIndex A = 2) (hJM : J ≤ M)
    (s : G) (hsA : s ∈ A) (hsJ : s ∉ J) (hsM : s ∈ M) : A ≤ M := by
  intro a ha
  by_cases haJ : a ∈ J
  · exact hJM haJ
  have hprod : (⟨s,hsA⟩ : A)*(⟨a,ha⟩ : A) ∈ J.subgroupOf A := by
    apply (Subgroup.mul_mem_iff_of_index_two hindex).mpr
    change (s ∈ J ↔ a ∈ J)
    simp only [hsJ,haJ]
  have hprod' : s*a ∈ J := hprod
  have hh := M.mul_mem (M.inv_mem hsM) (hJM hprod')
  simpa only [inv_mul_cancel_left] using hh

universe u
/-- Select the actual nonexceptional elementary eight, retaining all action
and intrinsic centralizer properties needed by its local normalizers. -/
public theorem distance_one_selected_eight
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    ∃ U : Subgroup G, U ≤ V ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8 ∧
      ZAt ctx.Γ ctx.criticalPath.a' ≤ U ∧ NormalIn U (EAt ctx.Γ ctx.criticalPath.a') ∧
      ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (U : Set G) ∧
      ¬ QAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (U : Set G) ∧
      V ⊓ Subgroup.centralizer (U : Set G) = U := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨left,right,hleft,hright,hjoin,hinter,hcomm,s,hsZa,hsB,hsL,hsR⟩ :=
    distance_one_vstar_factor_swap ctx.toLocalContext hlength hfaithful hlocal
  change V = left ⊔ right at hjoin
  have hcont := distance_one_vstar_containments ctx.toLocalContext hlength
  have hseed : Za ⊓ Q ≤ V := by
    intro x hx
    exact Subgroup.subset_closure ⟨1,⟨x,hx⟩,by simp⟩
  have hleftCard : Nat.card left = 8 := by
    rw [Nat.card_congr hleft.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hne : left ≠ right := by
    intro hh
    rw [← hh,inf_idem,hleftCard] at hinter
    omega
  have hVnormL : V ≤ Subgroup.normalizer (left : Set G) := by
    rw [hjoin]
    apply sup_le left.le_normalizer
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hsQ : s ∉ Q := by
    intro hsq
    have hsVL := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVnormL (hseed ⟨hsZa,hsq⟩))
    exact hne (hsVL.symm.trans hsL)
  have hneighbor : ctx.criticalPath.a' ∈
      CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood,ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hlength)
  let _ : IsElementaryAbelian 2 (ZAt ctx.Γ ctx.criticalPath.a) :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hsZa' : s ∈ ZAt ctx.Γ ctx.criticalPath.a := hsZa
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian s hsZa'
  obtain ⟨t,htQ,htL,htR⟩ := distance_one_terminal_core_factor_swap
    ctx hlength hfaithful hlocal left right hleft hright hjoin hinter hcomm
  obtain ⟨hcenter,hzcard,⟨g,hgE,hgorder⟩,_⟩ :=
    distance_one_vstar_three_action ctx hlength hfaithful hlocal
  have hgB : g ∈ GAt ctx.Γ ctx.criticalPath.a' := by
    apply SevenSix.twoResidualIn_le (GAt ctx.Γ ctx.criticalPath.a')
    simpa only [EAt,CosetGraphContext.e,ctx.Γ.twoResidualAt_def,
      GAt,CosetGraphContext.stabilizer] using hgE
  have hg3 : g^3=1 := by rw [← hgorder]; exact pow_orderOf_eq_one g
  have hgnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hcont.1.1).mp hcont.1.2 hgB
  have hgmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgnorm
  change V.map (MulAut.conj g).toMonoidHom = V at hgmap
  rw [hjoin] at hgmap
  have hcube (x : G) : (MulAut.conj g) ((MulAut.conj g) ((MulAut.conj g) x)) = x := by
    have hh : (MulAut.conj g)^3=1 := by rw [← map_pow,hg3,map_one]
    simpa [pow_succ] using congrArg (fun e : MulAut G => e x) hh
  have hgpres := Subgroup.quaternion_factors_invariant_of_cube_eq_one left right
    hleft hright hinter hcomm (MulAut.conj g) hgmap hcube
  have hgne : ∃ b : left, g*(b:G)*g⁻¹≠b := by
    by_contra hn
    push Not at hn
    have hle : left ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
      intro b hb
      apply (distance_one_vstar_residual_centralizer ctx hlength hfaithful hlocal hcenter).2
        g hgE hgorder b
      · change b ∈ V
        rw [hjoin]
        exact Subgroup.mem_sup_left hb
      · exact mul_inv_eq_iff_eq_mul.mp (hn ⟨b,hb⟩)
    have hh := Subgroup.card_le_of_le hle
    rw [hleftCard,hzcard] at hh
    omega
  have hconj := distance_one_residual_cubic_conjugation_mod_vstar
    ctx hlength hfaithful hlocal g hgE hgorder
  obtain ⟨θ,U,hUeq,hElem,hUcard,hIU,hUV,hVN,hgN,hsN,htN⟩ :=
    Subgroup.exists_quaternion_diagonal_of_swapped_cubic_actions left right hleft.some
      hinter hcomm g s t hg3 hs2
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgpres.1)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgpres.2) hgne hsL htL htR
      (hjoin ▸ hconj.2 s hsB hsQ hs2) (hjoin ▸ hconj.1 t htQ)
  have hUV' : U ≤ V := hUV.trans_eq hjoin.symm
  have hVN' : V ≤ Subgroup.normalizer (U : Set G) := hjoin.symm ▸ hVN
  have hVE := distance_one_vstar_le_terminal_residual ctx hlength hfaithful hlocal
  have hUE : U ≤ EAt ctx.Γ ctx.criticalPath.a' := hUV'.trans hVE
  have hEN : EAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (U : Set G) := by
    rw [distance_one_terminal_residual_eq_vstar_sup_zpowers ctx hlength hfaithful hlocal g hgE hgorder]
    exact sup_le hVN' (Subgroup.zpowers_le.mpr hgN)
  have hUN : NormalIn U (EAt ctx.Γ ctx.criticalPath.a') :=
    ⟨hUE,(Subgroup.normal_subgroupOf_iff_le_normalizer hUE).mpr hEN⟩
  have hZaN : Za ≤ Subgroup.normalizer (U : Set G) := by
    have hsCard := (distance_one_seed_data ctx.toLocalContext hlength hfaithful hlocal).1
    change Nat.card (Za ⊓ Q : Subgroup G) = 8 at hsCard
    have hZaCard : Nat.card Za = 16 := hfaithful.1
    have hi : (Za ⊓ Q).relIndex Za = 2 := by
      have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (Za ⊓ Q) Za bot_le inf_le_left
      simp only [Subgroup.relIndex_bot_left] at hh
      rw [hsCard,hZaCard] at hh
      omega
    exact le_of_index_two_of_outside (Za ⊓ Q) Za _ hi (hseed.trans hVN') s hsZa
      (fun hh => hsQ hh.2) hsN
  have hself : V ⊓ Subgroup.centralizer (U : Set G) = U := by
    rw [hjoin,hUeq]
    exact Subgroup.inf_centralizer_quaternionDiagonal left right hleft.some θ hinter hcomm
  have hIcenter : left ⊓ right ≤ CenterAmbient V := by
    intro x hx
    have hxV : x ∈ V := by rw [hjoin]; exact Subgroup.mem_sup_left hx.1
    refine ⟨⟨x,hxV⟩,Subgroup.mem_center_iff.mpr ?_,rfl⟩
    intro v
    apply Subtype.ext
    have hcent : x ∈ Subgroup.centralizer ((left ⊔ right : Subgroup G) : Set G) := by
      rw [Subgroup.sup_eq_closure,Subgroup.centralizer_closure,Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with hy | hy
      · exact hcomm y hy x hx.2
      · exact (hcomm x hx.1 y hy).symm
    exact Subgroup.mem_centralizer_iff.mp hcent v (hjoin ▸ v.property)
  have hIz : left ⊓ right = ZAt ctx.Γ ctx.criticalPath.a' := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact hIcenter.trans_eq hcenter
    · rw [hinter,hzcard]
  refine ⟨U,hUV',hElem,hUcard,?_,hUN,hZaN,?_,hself⟩
  · rw [← hIz]
    exact hIU
  · intro hn
    exact htN (hn htQ)
end Stellmacher.SectionNine
