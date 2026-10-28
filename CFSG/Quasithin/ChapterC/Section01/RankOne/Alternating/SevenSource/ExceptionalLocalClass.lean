module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Moved
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Parabolic
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The natural A₅ preimage in the exceptional A₇ source

The original moved natural four-space, the canonical omega-center span,
and the Baumann Sylow marking construct the literal C.1.17 local group.
The fixed alpha summand is retained throughout. The centralizer
quotient retains the supplied natural coordinates. Its two-group kernel
also lifts the rank-one unique maximal Sylow overgroup.

Source: Aschbacher–Smith C.1.21(4), C.1.24, printed pp.128–131.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource
open ChapterB ChapterB.QuasisimpleSource ChiProduct.SelectedRankOne
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := A)]
  exact solvableResidual_le_of_solvable_quotient N

/-- A rank-one quotient with a two-group kernel makes every Sylow two-subgroup
minimal parabolic in the original finite group. -/
theorem rankOne_minimal_of_twoKernel
    (F : BinaryField) (q : H →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (S : Sylow 2 H) : IsMinimalParabolicOver S ⊤ := by
  have hc : q.ker ≤ pCore 2 H := le_sSup ⟨inferInstance,hk⟩
  have hfr : q.ker ≤ (frattini (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) := by
    intro x hx
    change (x : H ⧸ pCore 2 H) ∈ frattini (H ⧸ pCore 2 H)
    rw [(QuotientGroup.eq_one_iff x).mpr (hc hx)]
    exact one_mem _
  refine ⟨rankOne_unique_of_coreFrattini_kernel F.Carrier q hq hfr S,?_⟩
  intro hn
  let : (S : Subgroup H).Normal := normalizer_eq_top_iff.mp (top_unique hn)
  exact Matrix.SpecialLinearGroup.no_normal_sylow F.Carrier 2 (S.mapSurjective hq)
    (Normal.map inferInstance q hq)

/-- Full original natural coordinates construct the local model on the
literal moved subgroup, including its actual fixed kernel. -/
theorem naturalModel_of_moved_natural
    {B : Type*} [Group B] (F : BinaryField) [IsQuasisimple SL(2,F.Carrier)]
    (U W N : Subgroup H) [U.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (b : B →* N) (q : H →* SL(2,F.Carrier))
    (hqN : Function.Surjective (q.comp N.subtype))
    (hk : q.ker = centralizer (U : Set H))
    (hkernel : GlaubermanNiles.localKernel b = (centralizer (U : Set H)).subgroupOf N)
    (hm : (⁅GlaubermanNiles.localV b,(⊤ : Subgroup N)⁆ : Subgroup N).map N.subtype = W)
    (p : Additive W ≃ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (he : ∀ (g : H) (v : Additive W),
      p (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        specialLinearNatural 2 (q g) (p v)) :
    Nonempty (GlaubermanNiles.NaturalModel b F.Carrier) := by
  let r := q.comp N.subtype
  have hrk : r.ker = GlaubermanNiles.localKernel b := by
    rw [hkernel]
    change q.ker.subgroupOf N = _
    rw [hk]
  let c : GlaubermanNiles.LocalStar b ≃* SL(2,F.Carrier) :=
    (QuotientGroup.quotientMulEquivOfEq hrk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hqN)
  let : IsQuasisimple (GlaubermanNiles.LocalStar b) := IsQuasisimple.of_mulEquiv c.symm
  have ha : GlaubermanNiles.actorLift b = ⊤ := by
    unfold GlaubermanNiles.actorLift
    rw [generalizedFitting_eq_top_of_quasisimple,comap_top]
  have hm' : (GlaubermanNiles.moved b).map N.subtype = W := by
    unfold GlaubermanNiles.moved
    rwa [ha]
  let k : GlaubermanNiles.moved b ≃* W :=
    ((GlaubermanNiles.moved b).equivMapOfInjective N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr hm')
  let f : GlaubermanNiles.moved b →* Multiplicative (Fin 2 → F.Carrier) :=
    p.toLinearMap.toAddMonoidHom.toMultiplicativeRight.comp k.toMonoidHom
  have hf : Function.Surjective f := p.surjective.comp k.surjective
  have hfi : Function.Injective f := p.injective.comp k.injective
  have hconj (n : N) (w : GlaubermanNiles.moved b) :
      k (GlaubermanNiles.movedConjugate b n w) = MulAut.conjNormal (n:H) (k w) := by
    apply Subtype.ext
    rfl
  have hfe (n : N) (w : GlaubermanNiles.moved b) :
      (f (GlaubermanNiles.movedConjugate b n w)).toAdd =
        specialLinearNatural 2 (r n) (f w).toAdd := by
    change p (Additive.ofMul (k (GlaubermanNiles.movedConjugate b n w))) = _
    rw [hconj]
    exact he n (Additive.ofMul (k w))
  have hfk : f.ker = GlaubermanNiles.movedFixed b := by
    ext w
    change f w = 1 ↔ (w:N) ∈ centralizer (GlaubermanNiles.actorLift b : Set N)
    constructor
    · intro hw
      have hw1 : w = 1 := hfi (hw.trans (map_one f).symm)
      rw [hw1]
      exact one_mem _
    · intro hw
      have hz : (f w).toAdd ∈ (ChapterB.QuasisimpleSource.linearNatural F 2).invariants := by
        intro a
        obtain ⟨n,rfl⟩ := hqN a
        change specialLinearNatural 2 (r n) (f w).toAdd = (f w).toAdd
        rw [←hfe]
        congr 2
        apply Subtype.ext
        change n*(w:N)*n⁻¹=(w:N)
        rw [hw n (ha.symm ▸ mem_top n),mul_inv_cancel_right]
      have hz0 := (ChapterB.QuasisimpleSource.ExtensionConsequences.linearNatural_invariants F
        (by decide : 2 ≤ 2)).le hz
      exact Multiplicative.toAdd.injective hz0
  apply naturalModel_of_star_coordinates b F.Carrier c f hf hfk
  intro a w
  exact hfe a w

/-- The original natural moved space and the actual local-span comparisons
supply the local class, without requiring the whole omega-center span to
be natural or to have dimension four. -/
theorem exceptional_inLocalClass_of_span
    (F : BinaryField) (hF : 3 < Nat.card F.Carrier)
    (T : Sylow 2 H) (U W : Subgroup H) [U.Normal] [W.Normal]
    [IsElementaryAbelian 2 W]
    (q : H →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H)) (hk2 : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H)
    (hB : Chapter1.IsSylowIn 2 (baumann (T : Subgroup H))
      (pResidual 2 H ⊔ baumann (T : Subgroup H)))
    (hkernel : GlaubermanNiles.localKernel (inclusion
      (show baumann (T : Subgroup H) ≤ pResidual 2 H ⊔ baumann (T : Subgroup H)
        from le_sup_right)) =
      (centralizer (U : Set H)).subgroupOf (pResidual 2 H ⊔ baumann (T : Subgroup H)))
    (hm : (⁅GlaubermanNiles.localV (inclusion
      (show baumann (T : Subgroup H) ≤ pResidual 2 H ⊔ baumann (T : Subgroup H)
        from le_sup_right)),(⊤ : Subgroup (pResidual 2 H ⊔ baumann (T : Subgroup H) : Subgroup H))⁆).map (pResidual 2 H ⊔ baumann (T : Subgroup H)).subtype = W)
    (p : Additive W ≃ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (he : ∀ (g : H) (v : Additive W),
      p (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        specialLinearNatural 2 (q g) (p v)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup H) ≤ pResidual 2 H ⊔ baumann (T : Subgroup H)
        from le_sup_right)) := by
  let A := SL(2,F.Carrier)
  let : Group.IsPerfect A := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hF
  let : IsQuasisimple A := ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  let N := pResidual 2 H ⊔ baumann (T : Subgroup H)
  let b := inclusion (show baumann (T : Subgroup H) ≤ N from le_sup_right)
  have hgen := pResidual_sup_sylow_eq_top T
  have hqN : Function.Surjective (q.comp N.subtype) := by
    have hr : (pResidual 2 H).map q = ⊤ := by
      rw [map_pResidual_of_surjective 2 q hq,(pResidual_eq_top_iff 2 A).mpr perfect_twoPerfect]
    intro a
    obtain ⟨x,hx,hxa⟩ := hr.symm ▸ mem_top a
    exact ⟨⟨x,(show pResidual 2 H ≤ N from le_sup_left) hx⟩,hxa⟩
  obtain ⟨S,hS⟩ := hB
  have hs : b.range = (S : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [hS,MonoidHom.map_range,show N.subtype.comp b = (baumann (T : Subgroup H)).subtype from rfl,
      range_subtype]
  have hkN : IsPGroup 2 (q.comp N.subtype).ker := by
    change IsPGroup 2 (q.ker.subgroupOf N)
    exact hk2.comap_subtype
  exact ⟨inclusion_injective _,⟨S,hs,rankOne_minimal_of_twoKernel F _ hqN hkN S⟩,
    selected_baumann_fitting (T : Subgroup H) (pResidual 2 H) hgen hfit,
    F.degree,F.degree_pos,F.Carrier,inferInstance,inferInstance,inferInstance,F.card_eq,
    naturalModel_of_moved_natural F U W N b q hqN hk hkernel hm p he⟩

/-- The actual natural rank-one preimage supplies the C.1.17 inclusion.
For the exceptional seven-letter source the marked field has four elements. -/
theorem exceptional_inLocalClass
    (F : BinaryField) (hF : 3 < Nat.card F.Carrier)
    (T : Sylow 2 H) (U W : Subgroup H) [U.Normal] [W.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W] (hU : IsPReduced 2 U)
    (q : H →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H)) (hk2 : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H)
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup H) : Set H))
    (hmove : ⁅U,pResidual 2 H⁆ = W)
    (halpha : thompsonAlpha (T : Subgroup H) ≤ W ⊔
      (thompsonAlpha (T : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)))
    (hB : Chapter1.IsSylowIn 2 (baumann (T : Subgroup H))
      (pResidual 2 H ⊔ baumann (T : Subgroup H)))
    (p : Additive W ≃ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (he : ∀ (g : H) (v : Additive W),
      p (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        specialLinearNatural 2 (q g) (p v)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup H) ≤ pResidual 2 H ⊔ baumann (T : Subgroup H)
        from le_sup_right)) := by
  let N := pResidual 2 H ⊔ baumann (T : Subgroup H)
  let b := inclusion (show baumann (T : Subgroup H) ≤ N from le_sup_right)
  have hgen := pResidual_sup_sylow_eq_top T
  have ha : thompsonAlpha (T : Subgroup H) ≤ ⁅U,pResidual 2 H⁆ ⊔
      (thompsonAlpha (T : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) := by
    rw [hmove]
    exact halpha
  have hkernel : GlaubermanNiles.localKernel b = (centralizer (U : Set H)).subgroupOf N :=
    localKernel_selected_baumann (T : Subgroup H) U hU hgen hspan ha
  have hm : (⁅GlaubermanNiles.localV b,(⊤ : Subgroup N)⁆ : Subgroup N).map N.subtype = W := by
    rw [localV_selected_full_commutator (T : Subgroup H) U hgen hspan ha,hmove]
  exact exceptional_inLocalClass_of_span F hF T U W q hq hk hk2 hfit hB hkernel hm p he

end CFSG.Quasithin.ChapterC.RankOne.SevenSource
