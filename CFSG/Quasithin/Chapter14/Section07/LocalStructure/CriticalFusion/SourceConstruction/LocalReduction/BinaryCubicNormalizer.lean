module
public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.MarkedGeneration
public import Theory.GroupAction.EightCubicNormalizer
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Cubic normalizer control for the original point residual

Let A ≤ L₁ contain an actual element of order three, and let Y ≤ N_G(L)
normalize A. The action of O²(Y) on L/O₂(L) is inner because the outer
automorphism group of SL₃(2) is a two-group. In the original natural
L-action on V, the image of A fixes the unique nonidentity point V₁:
its cubic has precisely two fixed elements in V. An inner implementer
normalizing that image therefore fixes V₁. This preserves the literal
preimage L ∩ H of the point stabilizer, hence its two-residual L₁.

The quotient action and its kernel are constructed from the supplied
natural marking. This result needs no universal structural theorem and
is used by BinaryPlaneEscape for A = O²(C_{L₁}(P)) and the same Y supplied
by the original exchanged-component construction.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {C : GroupClass.{u}}

/-- The two-residual of a normalizer of a cubic-containing subgroup of L₁
normalizes the original L₁. All quotient and point stabilizer maps are literal. -/
theorem point_cubic_normalizer_residual
    (h : HigherRankHypothesis C T L V 3)
    (A Y : Subgroup G) (hA : A ≤ F.Li L 1)
    (hY : Y ≤ normalizer (L : Set G)) (hYA : Y ≤ normalizer (A : Set G))
    (l : G) (hl : l∈A) (hl3 : orderOf l=3) :
    (pResidual 2 Y).map Y.subtype ≤ normalizer (F.Li L 1 : Set G) := by
  let := h.chosen.elementary
  let ρ := setupSeedAction L V h.chosen.normalizes
  have hρ : Function.Surjective ρ := by
    intro a
    obtain ⟨l,hl,he⟩ := h.full_L_action a
    exact ⟨⟨l,hl⟩,MulEquiv.ext fun v => Subtype.ext (he v)⟩
  have hk : ρ.ker = pCore 2 L := by
    rw [setupSeedAction_ker]
    apply map_injective L.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm]
    exact h.centralizer_L
  let eQ : (L ⧸ pCore 2 L) ≃* MulAut V :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  let eV : MulAut V ≃* Matrix.PSL3Two.SL :=
    (InvariantFlag.naturalFlagActorEquiv h.naturalMarking.coordinates).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let e := eQ.trans eV
  have he (a : L) : e (QuotientGroup.mk' (pCore 2 L) a) = eV (ρ a) := rfl
  let f : Y →* MulAut Matrix.PSL3Two.SL := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hY)))
  let o := (QuotientGroup.mk' (MulAut.innerSubgroup Matrix.PSL3Two.SL)).comp f
  have ho := pResidual_le_ker_of_isPGroup 2 o
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup
  obtain ⟨z₀,hz₀,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  let z : V := ⟨z₀,(F.le_seed 1) (hZ ▸ mem_zpowers z₀)⟩
  have hz : z≠1 := fun he => hz₀ (congrArg Subtype.val he)
  have hpoint (a : L) : (a:G) ∈ F.H ↔ ρ a z=z := by
    rw [F.H_eq_centralizer (by decide) z₀ hZ]
    constructor
    · intro ha
      apply Subtype.ext
      change (a:G)*z₀*(a:G)⁻¹=z₀
      rw [←ha z₀ (Set.mem_singleton z₀),mul_inv_cancel_right]
    · intro ha x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val ha)).symm
  let B := (A.subgroupOf L).map ρ
  have hB : ∀ a ∈ B, a z=z := by
    rintro a ⟨x,hx,rfl⟩
    exact (hpoint x).mp ((F.Li_le L 1).trans inf_le_right (hA hx))
  let lL : L := ⟨l,(F.Li_le L 1).trans inf_le_left (hA hl)⟩
  have hlL : orderOf lL=3 := (L.orderOf_coe lL).symm.trans hl3
  have hρl : orderOf (ρ lL)=3 :=
    (ρ.orderOf_map_eq_of_coprime_of_isPGroup_ker (hk ▸ pCore_isPGroup) lL
      (by rw [hlL]; decide)).trans hlL
  have hcV : Nat.card V=8 := by simpa only [F.last,Nat.reducePow] using F.card 3 le_rfl
  rintro x ⟨y,hy,rfl⟩
  have hi : f y ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL :=
    (QuotientGroup.eq_one_iff _).mp (ho hy)
  obtain ⟨g,hg⟩ := hi
  let b := eV.symm g
  let yM : normalizer (L : Set G) := inclusion hY y
  have hconj (a : L) : ρ (L.normalizerMonoidHom yM a)=b*ρ a*b⁻¹ := by
    apply eV.injective
    have hh := DFunLike.congr_fun hg (e (QuotientGroup.mk' (pCore 2 L) a))
    have hh' : f y (e (QuotientGroup.mk' (pCore 2 L) a)) =
        e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom yM a)) := by
      change e ((quotientAut (pCore 2 L) (L.normalizerMonoidHom yM))
        (e.symm (e (QuotientGroup.mk' (pCore 2 L) a)))) = _
      rw [e.symm_apply_apply,quotientAut_apply_mk]
    rw [hh',he,he] at hh
    simpa only [map_mul,map_inv,b,eV.apply_symm_apply,MulAut.conj_apply] using hh.symm
  have hb : b ∈ normalizer (B : Set (MulAut V)) := by
    apply mem_normalizer_fintype
    rintro a ⟨r,hr,rfl⟩
    refine ⟨L.normalizerMonoidHom yM r,?_,hconj r⟩
    exact (mem_normalizer_iff.mp (hYA y.property) r).mp hr
  have hbz : b z=z := MulAut.normalizer_fixes_point_of_cubic B hcV z hz hB
    (ρ lL) (mem_map_of_mem ρ hl) hρl hb
  have hbzi : b⁻¹ z=z := by
    have hh := congrArg b.symm hbz
    exact hh.symm.trans (b.symm_apply_apply z)
  have hn : (y:G) ∈ normalizer ((L ⊓ F.H : Subgroup G) : Set G) := by
    apply mem_normalizer_fintype
    intro a ha
    have hL : (y:G)*a*(y:G)⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (hY y.property) a).mp ha.1
    refine ⟨hL,?_⟩
    let aL : L := ⟨a,ha.1⟩
    have hfix := (hpoint aL).mp ha.2
    apply (hpoint (L.normalizerMonoidHom yM aL)).mpr
    rw [hconj]
    simp only [MulAut.mul_apply,hbzi,hfix,hbz]
  have hh := normalizer_le_normalizer_characteristic_image
    (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)) hn
  have hLi : F.Li L 1 = (pResidual 2 (L ⊓ F.H : Subgroup G)).map
      (L ⊓ F.H).subtype := by
    simp only [InvariantFlag.Li,show ¬ (3=5 ∧ (1=2 ∨ 1=3)) by decide,if_false]
    rfl
  rw [hLi]
  exact hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
