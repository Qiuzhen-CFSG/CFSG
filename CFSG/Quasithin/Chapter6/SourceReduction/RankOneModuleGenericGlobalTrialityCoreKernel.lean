module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialCenterAction
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LeviSemilinear
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityNonfusion

/-!
# Removing the original LT-core in the compatible triality comparison

Let K = O²(H), S = O₂(N_G(L) ∩ H), and Q = O₂(LT). The genuine central
coroot at t⁻² has the same action on the arms Levi as the arms coroot at
t, for t in the actual fixed field. Restriction to the original intrinsic
two-core quotient preserves this equality. The two compatible parabolic
maps and their agreement on the whole overlap lift this action into the
original left Borel, which normalizes Q.

Choose t generating the base-field units. Its arms quotient image has
order q−1. The image of Q on the right quotient PSL₂(q³) is a two-group
preserving the original quotient Sylow and normalized by this torus.
Every torus displacement therefore lies in that Sylow. After Sylow
alignment, the Borel projection injects the odd torus into the field
units; its order q−1 identifies its image with the actual base-field
units. Thus the right coefficient fixes the base field. The cubic
restriction kernel has order three and vanishes on the two-power actor.
The existing right-field kernel theorem gives Q ≤ S.

The accepted center-fixer bound C_T(Z(K)) ≤ Q S now gives containment
in the original S. Applying the existing marked source placements and
movement proves short-root nonfusion at every original exponent n > 1,
without a parity or centralizer-containment premise. The quotient field
remains GF(q³), the center field remains GF(q), and no local automorphism
is assumed to extend to the full triality model.

Source: Aschbacher–Smith F.4.29(2,7), pp.289–290, F.4.35, p.292, and
5.3.3, p.659 (`refs/quasithin.pdf`); genuine D₄ root and cubic-field
conventions follow GLS3 §§2.4–2.6. Ambient recognition is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.ParabolicOuterTwo
open Theory.AlgebraicGroup.StandardRootSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison

private theorem conjugate_product {M : Type*} [Group M] (g h x : M) :
    (g*h)*x*(g*h)⁻¹=g*(h*x*h⁻¹)*g⁻¹ := by group

private theorem same_conjugation_iff {M : Type*} [Group M] (g h x : M) :
    g*x*g⁻¹=h*x*h⁻¹ ↔ x*(h⁻¹*g)=(h⁻¹*g)*x := by
  constructor <;> intro he
  · calc
      x*(h⁻¹*g)=h⁻¹*(h*x*h⁻¹)*g := by group
      _=h⁻¹*(g*x*g⁻¹)*g := by rw [he]
      _=(h⁻¹*g)*x := by group
  · calc
      g*x*g⁻¹=h*((h⁻¹*g)*x)*g⁻¹ := by group
      _=h*(x*(h⁻¹*g))*g⁻¹ := by rw [he]
      _=h*x*h⁻¹ := by group

private theorem split_levi_action_ext (P : Parameters) (g h : SplitGroup P)
    (hpos : ∀ j ∈ Node.arms.support, ∀ u,
      g*positiveRoot P j u*g⁻¹=h*positiveRoot P j u*h⁻¹)
    (hneg : ∀ j ∈ Node.arms.support, ∀ u,
      g*negativeRoot P j u*g⁻¹=h*negativeRoot P j u*h⁻¹)
    (x : SplitGroup P) (hx : x ∈ splitLevi P .arms) : g*x*g⁻¹=h*x*h⁻¹ := by
  apply (same_conjugation_iff _ _ _).mpr
  have hc : h⁻¹*g ∈ centralizer (splitLevi P .arms : Set (SplitGroup P)) := by
    rw [splitLevi,centralizer_closure]
    apply mem_centralizer_iff.mpr
    rintro z ⟨j,hj,u,rfl | rfl⟩
    · exact (same_conjugation_iff _ _ _).mp (hpos j hj u)
    · exact (same_conjugation_iff _ _ _).mp (hneg j hj u)
  exact mem_centralizer_iff.mp hc x hx

private theorem fixed_torus_words (P : Parameters) (hp : P.prime=2)
    (s t : (ExtensionField P)ˣ) (hst : s.val^2=t.val⁻¹)
    (x : SplitGroup P) (hx : x ∈ splitLevi P .arms) :
    torusWord P 1 t*x*(torusWord P 1 t)⁻¹ =
      (torusWord P 0 s*torusWord P 2 s*torusWord P 3 s)*x*
        (torusWord P 0 s*torusWord P 2 s*torusWord P 3 s)⁻¹ := by
  apply split_levi_action_ext P _ _ ?_ ?_ x hx
  · intro j hj u
    simp only [conjugate_product,torusWord_positiveRoot_conjugate_cartan P hp]
    fin_cases j <;> simp_all [Node.support,typeDCartanMatrix]
  · intro j hj u
    simp only [conjugate_product,torusWord_negativeRoot_conjugate P hp]
    fin_cases j <;> simp_all [Node.support,typeDCartanMatrix]

private theorem fixed_torus_split_action (P : Parameters) (hp : P.prime=2)
    (t : (fixedField P)ˣ) (x : SplitGroup P) (hx : x ∈ splitLevi P .arms) :
    elementaryInclusion P (torusElementary P hp .central (t⁻¹^2))*x*
      (elementaryInclusion P (torusElementary P hp .central (t⁻¹^2)))⁻¹ =
    elementaryInclusion P (torusElementary P hp .arms (fixedUnit P t))*x*
      (elementaryInclusion P (torusElementary P hp .arms (fixedUnit P t)))⁻¹ := by
  have hcentral := torusElementary_central_val P hp (t⁻¹^2)
  have harms : elementaryInclusion P (torusElementary P hp .arms (fixedUnit P t)) =
      torusWord P 0 (fixedUnit P t)*torusWord P 2 (fixedUnit P t)*
        torusWord P 3 (fixedUnit P t) := by
    exact (torusElementary_arms_val P hp (fixedUnit P t)).trans (by
      rw [frobenius_fixedUnit,frobenius_fixedUnit])
  have hs : (fixedUnit P t).val^2=(fixedUnit P (t⁻¹^2)).val⁻¹ := by
    simp only [map_pow,map_inv,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,
      inv_pow,inv_inv]
  exact (congrArg (fun g : SplitGroup P => g*x*g⁻¹) hcentral).trans
    ((fixed_torus_words P hp _ _ hs x hx).trans
      (congrArg (fun g : SplitGroup P => g*x*g⁻¹) harms).symm)

private theorem fixed_torus_levi_action (P : Parameters) (hp : P.prime=2)
    (t : (fixedField P)ˣ) (x : levi P .arms) :
    torusActor P hp .central (t⁻¹^2)*x.val*(torusActor P hp .central (t⁻¹^2))⁻¹ =
      torusActor P hp .arms (fixedUnit P t)*x.val*(torusActor P hp .arms (fixedUnit P t))⁻¹ := by
  obtain ⟨y,hy,he⟩ := x.property
  rw [←he]
  change toCarrier P _ * toCarrier P y * (toCarrier P _)⁻¹ =
    toCarrier P _ * toCarrier P y * (toCarrier P _)⁻¹
  simp only [←map_inv,←map_mul]
  apply congrArg (toCarrier P)
  apply LeviCommutators.elementaryInclusion_injective P
  simp only [map_mul,map_inv]
  exact fixed_torus_split_action P hp t _ hy

theorem central_actor_mem_borel (P : Parameters) (hp : P.prime=2)
    (t : (fixedField P)ˣ) : torusActor P hp .central t ∈ borel P := by
  apply torus_le_borel P
  refine ⟨torusElementary P hp .central t,?_,rfl⟩
  change elementaryInclusion P _ ∈ splitTorus P
  rw [torusElementary_central_val]
  exact subset_closure ⟨1,fixedUnit P t,rfl⟩

/-- The actual central torus supplies the base-field arms-torus action on
its intrinsic quotient; the inverse square is the literal root weight. -/
theorem central_torus_arms_quotient_action (P : Parameters) (hp : P.prime=2)
    (t : (fixedField P)ˣ) :
    localQuotientAction P .arms (parabolicInner P .arms
      ⟨torusActor P hp .central (t⁻¹^2),
        borel_le_parabolic P .arms (central_actor_mem_borel P hp _)⟩) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 (localFactor P .arms))
        ⟨torusActor P hp .arms (fixedUnit P t),
          levi_le_localFactor P hp .arms (torusActor_mem_levi P hp .arms _)⟩) :=
  localQuotientAction_parabolicInner_of_levi P hp .arms _
    ⟨torusActor P hp .arms (fixedUnit P t),torusActor_mem_levi P hp .arms _⟩
    (fixed_torus_levi_action P hp t)

private theorem arms_actor_eq_torus (P : Parameters) (hp : P.prime=2)
    (t : (ExtensionField P)ˣ) :
    torusActor P hp .arms t = (torusMulEquiv P hp (t,1)).val := by
  have hone : torusElementary P hp .central 1 = 1 := by
    apply LeviCommutators.elementaryInclusion_injective P
    exact (torusElementary_central_val P hp 1).trans
      ((congrArg (torusWord P 1) (map_one (fixedUnit P))).trans
        ((torusWord_one P hp 1).trans (map_one (elementaryInclusion P)).symm))
  have hprod : orbitElementary P hp (t,1)=torusElementary P hp .arms t :=
    (congrArg (torusElementary P hp .arms t * ·) hone).trans (mul_one _)
  exact ((torusMulEquiv_val P hp (t,1)).trans (congrArg (toCarrier P) hprod)).symm

private theorem arms_actor_quotient_order (P : Parameters) (hp : P.prime=2)
    (t : (fixedField P)ˣ) :
    orderOf (QuotientGroup.mk' (pCore 2 (localFactor P .arms))
      ⟨torusActor P hp .arms (fixedUnit P t),
        levi_le_localFactor P hp .arms (torusActor_mem_levi P hp .arms _)⟩) = orderOf t := by
  let z : levi P .arms := ⟨torusActor P hp .arms (fixedUnit P t),torusActor_mem_levi P hp .arms _⟩
  have he : localFactorQuotientEquivLevi P hp .arms
      (QuotientGroup.mk' (pCore 2 (localFactor P .arms))
        (inclusion (levi_le_localFactor P hp .arms) z)) = z :=
    localLeviProjection_inclusion P hp .arms z
  have hinj : Function.Injective (fixedUnit P) := by
    intro a b hab
    apply Units.ext
    exact Subtype.ext (congrArg Units.val hab)
  calc
    _ = orderOf z := ((localFactorQuotientEquivLevi P hp .arms).orderOf_eq _).symm.trans
      (congrArg orderOf he)
    _ = orderOf z.val := (Subgroup.orderOf_coe z).symm
    _ = orderOf (torusMulEquiv P hp (fixedUnit P t,1)).val :=
      congrArg orderOf (arms_actor_eq_torus P hp (fixedUnit P t))
    _ = orderOf (torusMulEquiv P hp (fixedUnit P t,1)) := Subgroup.orderOf_coe _
    _ = orderOf (fixedUnit P t,(1 : (fixedField P)ˣ)) := (torusMulEquiv P hp).orderOf_eq _
    _ = orderOf (fixedUnit P t) := by simp only [Prod.orderOf_mk,orderOf_one,Nat.lcm_one_right]
    _ = orderOf t := orderOf_injective (fixedUnit P) hinj t

private theorem arms_actor_mem_borel (P : Parameters) (hp : P.prime=2)
    (t : (ExtensionField P)ˣ) : torusActor P hp .arms t ∈ borel P := by
  rw [arms_actor_eq_torus]
  exact torus_le_borel P (torusMulEquiv P hp (t,1)).property

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- Lift every base-field arms torus action through the original left Borel,
retaining the exact right representative and the same compatible maps. -/
theorem Preparation.triality_base_torus_action_lift
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (t : (fixedField (binaryParameters m hm))ˣ) :
    ∃ (a : normalizer (residual H : Set G)) (k : residual H),
      a.val ∈ localBorel T L ∧ k.val ∈ localBorel T (residual H) ∧
      orderOf (QuotientGroup.mk' (pCore 2 (residual H)) k) = orderOf t ∧
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val = k.val ∧ (e.right w).val =
          torusActor (binaryParameters m hm) rfl .arms (fixedUnit _ t)) ∧
      pCoreNormalizerAction 2 (residual H) a =
        MulAut.conj (QuotientGroup.mk' (pCore 2 (residual H)) k) := by
  let P := binaryParameters m hm
  have hq : 2 < P.q := by
    change 2^1 < 2^m
    exact Nat.pow_lt_pow_right (by decide) (d.triality_parameter_gt_one h hp m hm e)
  have hS := d.triality_sourceS_le_factors h hTH hp m hm (Or.inr ⟨e⟩)
  have hSL : sourceS L H ≤ L := hS 0
  have hSTL : sourceS L H = (T : Subgroup G) ⊓ L :=
    (d.ordinary_sylow_core_geometry h hTH hS).1 0
  let X := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let K := residual H
  let fL : X →* Carrier P := (parabolic P .central).subtype.comp e.left.toMonoidHom
  let fR : Y →* Carrier P := (parabolic P .arms).subtype.comp e.right.toMonoidHom
  have hfL : Function.Injective fL := (parabolic P .central).subtype_injective.comp e.left.injective
  have hfR : Function.Injective fR := (parabolic P .arms).subtype_injective.comp e.right.injective
  have hLX : L ≤ X := le_sup_left.trans le_sup_left
  have hKY : K ≤ Y := le_sup_left.trans le_sup_left
  have hLf : (L.subgroupOf X).map fL = localFactor P .central := by
    have hL : L.subgroupOf X = solvableResidual X := by
      apply map_injective X.subtype_injective
      rw [map_subgroupOf_eq_of_le hLX]
      exact (d.parabolic_residuals h hTH hp 0).symm
    rw [hL,show fL = (parabolic P .central).subtype.comp e.left.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.left.toMonoidHom e.left.surjective]
    exact parabolic_solvableResidual_map P rfl hq .central
  have hKf : (K.subgroupOf Y).map fR = localFactor P .arms := by
    have hK : K.subgroupOf Y = solvableResidual Y := by
      apply map_injective Y.subtype_injective
      rw [map_subgroupOf_eq_of_le hKY]
      exact (d.parabolic_residuals h hTH hp 1).symm
    rw [hK,show fR = (parabolic P .arms).subtype.comp e.right.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact TrialityComparison.arms_parabolic_residual P rfl
  let eK : K ≃* localFactor P .arms :=
    ((subgroupOfEquivOfLe hKY).symm.trans
      ((K.subgroupOf Y).equivMapOfInjective fR hfR)).trans (MulEquiv.subgroupCongr hKf)
  let eQ := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  have heK (k : K) : (eK k).val = fR ⟨k,hKY k.property⟩ := rfl
  have heQ (k : K) : eQ (QuotientGroup.mk' (pCore 2 K) k) =
      QuotientGroup.mk' (pCore 2 (localFactor P .arms)) (eK k) := rfl
  let y := torusActor P rfl .central (t⁻¹^2)
  have hyB : y ∈ borel P := TrialityTorusComparison.central_actor_mem_borel P rfl _
  have hyL : y ∈ localFactor P .central :=
    levi_le_localFactor P rfl .central (torusActor_mem_levi P rfl .central _)
  let aR : Y := e.right.symm ⟨y,borel_le_parabolic P .arms hyB⟩
  let aL : X := e.left.symm ⟨y,borel_le_parabolic P .central hyB⟩
  let ym : borel P := ⟨y,hyB⟩
  have haLR : aL.val = aR.val :=
    (congrArg Subtype.val (e.symm.left_commutes ym)).trans
      (congrArg Subtype.val (e.symm.right_commutes ym)).symm
  have haLf : fL aL = y := congrArg Subtype.val (e.left.apply_symm_apply _)
  have haRf : fR aR = y := congrArg Subtype.val (e.right.apply_symm_apply _)
  have haL : aR.val ∈ L := by
    rw [←haLR]
    have hh : fL aL ∈ (L.subgroupOf X).map fL := hLf.symm ▸ (haLf.symm ▸ hyL)
    exact (mem_map_iff_mem hfL).mp hh
  have hac : aR.val ∈ ChapterF.Source.commonBorel ![L,K] (sourceS L H) := by
    rw [←ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)]
    exact ⟨haLR ▸ aL.property,aR.property⟩
  have haS : aR.val ∈ normalizer (sourceS L H : Set G) := by
    have hh := (d.hypothesisF11 h hTH).commonBorel_normalizes_localSylow 0 hac
    change aR.val ∈ normalizer ((sourceS L H ⊓ L : Subgroup G) : Set G) at hh
    simpa only [inf_eq_left.mpr hSL] using hh
  have haB : aR.val ∈ localBorel T L := by
    refine ⟨haL,?_⟩
    rwa [←hSTL]
  have hYN : Y ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKY).mp
      ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)
  let a : normalizer (K : Set G) := ⟨aR.val,hYN aR.property⟩
  let z : localFactor P .arms := ⟨torusActor P rfl .arms (fixedUnit P t),
    levi_le_localFactor P rfl .arms (torusActor_mem_levi P rfl .arms _)⟩
  let k := eK.symm z
  have hk : eK k = z := eK.apply_symm_apply z
  have hkB : k.val ∈ localBorel T K := by
    have hzB : z.val ∈ borel P := TrialityTorusComparison.arms_actor_mem_borel P rfl _
    let zm : borel P := ⟨z.val,hzB⟩
    let zL : X := e.left.symm ⟨z.val,borel_le_parabolic P .central hzB⟩
    have hkY : e.right ⟨k.val,hKY k.property⟩ =
        ⟨z.val,borel_le_parabolic P .arms hzB⟩ := by
      have hh : (eK k).val = z.val := congrArg (fun v : localFactor P .arms => v.val) hk
      exact Subtype.ext hh
    have hzk : zL.val=k.val :=
      ((congrArg Subtype.val (e.symm.left_commutes zm)).trans
        (congrArg Subtype.val (e.symm.right_commutes zm)).symm).trans
        (congrArg (fun w : Y => w.val) ((congrArg e.right.symm hkY).symm.trans
          (e.right.symm_apply_apply _)))
    have hkc : k.val ∈ ChapterF.Source.commonBorel ![L,K] (sourceS L H) := by
      rw [←ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)]
      exact ⟨hzk ▸ zL.property,hKY k.property⟩
    have hkn := (d.hypothesisF11 h hTH).commonBorel_normalizes_localSylow 1 hkc
    have hSK : sourceS L H ≤ K := hS 1
    have hSTK : sourceS L H = (T : Subgroup G) ⊓ K :=
      (d.ordinary_sylow_core_geometry h hTH hS).1 1
    change k.val ∈ normalizer ((sourceS L H ⊓ K : Subgroup G) : Set G) at hkn
    rw [inf_eq_left.mpr hSK,hSTK] at hkn
    exact ⟨k.property,hkn⟩
  have hko : orderOf (QuotientGroup.mk' (pCore 2 K) k)=orderOf t := by
    rw [←eQ.orderOf_eq,heQ,hk]
    exact TrialityTorusComparison.arms_actor_quotient_order P rfl t
  refine ⟨a,k,haB,hkB,hko,⟨⟨k.val,hKY k.property⟩,rfl,?_⟩,?_⟩
  · exact congrArg Subtype.val hk
  · ext v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) v
    rw [pCoreNormalizerAction_mk]
    change QuotientGroup.mk' (pCore 2 K) (K.normalizerMonoidHom a x) =
      QuotientGroup.mk' (pCore 2 K) k * QuotientGroup.mk' (pCore 2 K) x *
        (QuotientGroup.mk' (pCore 2 K) k)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply eQ.injective
    rw [heQ,heQ]
    let yR : parabolic P .arms := ⟨y,borel_le_parabolic P .arms hyB⟩
    have haact : eK (K.normalizerMonoidHom a x) =
        localRestriction P .arms (parabolicInner P .arms yR) (eK x) := by
      apply Subtype.ext
      rw [heK]
      change fR ⟨aR.val*x.val*aR.val⁻¹,_⟩ = y*(eK x).val*y⁻¹
      have hh : (⟨aR.val*x.val*aR.val⁻¹,_⟩ : Y) =
          aR*⟨x.val,hKY x.property⟩*aR⁻¹ := Subtype.ext rfl
      rw [hh,map_mul,map_mul,map_inv,haRf,←heK]
    rw [haact,←localQuotientAction_mk,
      TrialityTorusComparison.central_torus_arms_quotient_action P rfl t]
    simp only [MulAut.conj_apply,map_mul,map_inv,hk]
    rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison
open scoped MatrixGroups
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Atlas.RankOneFieldAutomorphisms

private theorem coefficient_fixes_base_of_torus_card (P : Parameters)
    (D : Subgroup (ExtensionField P)ˣ) (hD : Nat.card D = P.q-1)
    (σ : ExtensionField P ≃+* ExtensionField P)
    (hfix : ∀ u ∈ D, Units.map σ.toMonoidHom u = u) :
    ∀ t : fixedField P, σ t.val = t.val := by
  have hinj : Function.Injective (fixedUnit P) := by
    intro a b he
    apply Units.ext
    exact Subtype.ext (congrArg Units.val he)
  have hle : D ≤ (fixedUnit P).range := by
    intro u hu
    have huq : u^(P.q-1)=1 := by
      have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨u,hu⟩ : D)))
      simpa only [hD,Subgroup.coe_pow,Subgroup.coe_one] using hh
    have huF : frobenius P u = u := by
      apply Units.ext
      change u.val^P.q=u.val
      have hq : P.q=(P.q-1)+1 := by have := P.q_ge_two; omega
      rw [hq,pow_succ,show u.val^(P.q-1)=1 from congrArg Units.val huq,one_mul]
    exact ⟨restrictUnit P u huF,fixedUnit_restrictUnit P u huF⟩
  have he : D = (fixedUnit P).range := eq_of_le_of_card_ge hle (by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,Nat.card_units,
      card_fixedField,hD])
  intro t
  by_cases ht : t=0
  · subst t; exact map_zero σ
  · let u := Units.mk0 t ht
    have hh := congrArg Units.val (hfix (fixedUnit P u) (he.symm ▸ ⟨u,rfl⟩))
    exact hh

private theorem inner_of_base_borel_displacements (m : ℕ) (hm : 0<m)
    (C : Subgroup (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))))
    (hC : C ≤ Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel
      (ExtensionField (binaryParameters m hm)))
    (hcard : Nat.card C = (binaryParameters m hm).q-1)
    (α : MulAut (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))))
    (hα : ∃ k : ℕ, α^(2^k)=1)
    (hU : (kernel (ExtensionField (binaryParameters m hm))).map α.toMonoidHom =
      kernel (ExtensionField (binaryParameters m hm)))
    (hd : ∀ x∈C, x⁻¹*α x ∈ kernel (ExtensionField (binaryParameters m hm))) :
    α ∈ MulAut.innerSubgroup (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))) := by
  let P := binaryParameters m hm
  let F := ExtensionField P
  have hF : Nat.card F = 2^(3*m) := by
    rw [card_extensionField]
    change (2^m)^3=2^(3*m)
    rw [←pow_mul,Nat.mul_comm m 3]
  have ho : Odd (Nat.card C) := by
    rw [hcard]
    exact Nat.Even.sub_odd (Nat.one_le_pow m 2 (by decide))
      (Even.pow_of_ne_zero even_two hm.ne') odd_one
  obtain ⟨g,σ,he⟩ := exists_inner_field F α
  have hg := inner_factor_mem_borel F g σ (he ▸ hU)
  let f : C →* Fˣ := (torusProjection F).comp (inclusion hC)
  have hker : IsPGroup 2 f.ker := by
    have hfker : f.ker ≤ (kernel F).subgroupOf C := by
      intro x hx
      exact (torusProjection_eq_one_iff F (inclusion hC x)).mp hx
    have hP : IsPGroup 2 (kernel F) :=
      (coe_standardSylow F) ▸ (standardSylow F).isPGroup'
    exact hP.comap_subtype.to_le hfker
  have hkinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_of_card_eq
    exact Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right
      hker.exists_card_eq.choose)
      f.ker.card_subgroup_dvd_card (dvd_of_eq hker.exists_card_eq.choose_spec)
  have hfcard : Nat.card f.range = P.q-1 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hkinj).toEquiv.symm]
    exact hcard
  have hfσ : ∀ u∈f.range, Units.map σ.toMonoidHom u = u := by
    rintro _ ⟨x,rfl⟩
    apply (borelActor_commutator_mem_core_iff F hF ⟨g,hg⟩ σ (inclusion hC x)).mp
    rw [twoCoreIn_eq_kernel F hF,←he]
    exact hd x x.property
  have hthree : σ^3=1 := coefficient_cube_eq_one_of_fixes_fixedField P σ
    (coefficient_fixes_base_of_torus_card P f.range hfcard σ hfσ)
  obtain ⟨k,hk⟩ := hα
  have htwo : σ^(2^k)=1 := field_pow_eq_one_of_actor_pow F ⟨g,hg⟩ σ (2^k) (he ▸ hk)
  have hσ : σ=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow_left k)
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hthree))
  rw [he,hσ]
  have hf : Atlas.fieldEquivPSL 2 (1 : F ≃+* F) = 1 := (pslFieldAction (F := F)).map_one
  rw [hf,mul_one]
  exact ⟨g,rfl⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison
open scoped MatrixGroups
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Atlas.RankOneFieldAutomorphisms

private theorem inner_of_base_sylow_displacements (m : ℕ) (hm : 0<m)
    (S : Sylow 2 (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))))
    (C : Subgroup (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))))
    (hC : C ≤ normalizer (S : Set _))
    (hcard : Nat.card C = (binaryParameters m hm).q-1)
    (α : MulAut (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))))
    (hα : ∃ k : ℕ, α^(2^k)=1)
    (hS : (S : Subgroup _).map α.toMonoidHom = S)
    (hd : ∀ x∈C, x⁻¹*α x ∈ (S : Subgroup _)) :
    α ∈ MulAut.innerSubgroup (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))) := by
  let F := ExtensionField (binaryParameters m hm)
  obtain ⟨c,hcU,hcB⟩ := sylow_normalizer_conjugate F S
  let e := MulAut.conj c
  let C' := C.map e.symm.toMonoidHom
  let β := MulAut.congr e.symm α
  have hC' : C' ≤ Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F := by
    rw [←map_symm_eq_iff_map_eq _ (e := e) |>.mpr hcB]
    exact map_mono hC
  have hcard' : Nat.card C' = (binaryParameters m hm).q-1 := by
    rw [card_map_of_injective e.symm.injective]
    exact hcard
  have hβ : ∃ k : ℕ, β^(2^k)=1 := by
    obtain ⟨k,hk⟩ := hα
    exact ⟨k,by rw [←map_pow,hk,map_one]⟩
  have hU : (kernel F).map β.toMonoidHom = kernel F := by
    calc
      _ = (((kernel F).map e.toMonoidHom).map α.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map,Subgroup.map_map]
        rfl
      _ = (S : Subgroup _).map e.symm.toMonoidHom := by rw [hcU,hS]
      _ = kernel F := (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
  have hd' : ∀ x∈C', x⁻¹*β x ∈ kernel F := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := mem_map_of_mem e.symm.toMonoidHom (hd x hx)
    have heS : (S : Subgroup _).map e.symm.toMonoidHom = kernel F :=
      (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
    rw [heS] at hh
    change (e.symm x)⁻¹*e.symm (α (e (e.symm x))) ∈ kernel F
    rw [e.apply_symm_apply]
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using hh
  obtain ⟨z,hz⟩ := inner_of_base_borel_displacements m hm C' hC' hcard' β hβ hU hd'
  refine ⟨e z,?_⟩
  have hh := congrArg (MulAut.congr e) hz
  rw [MulAut.congr_conj] at hh
  exact hh.trans (by ext x; simp [β,MulAut.congr_apply])

private theorem base_torus_actor_inner (m : ℕ) (hm : 0<m)
    (S : Sylow 2 (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))))
    (A : Subgroup (MulAut (Theory.PSL2.Group (ExtensionField (binaryParameters m hm)))))
    (hA : IsPGroup 2 A)
    (hS : ∀ α∈A, (S : Subgroup _).map α.toMonoidHom = S)
    (z : Theory.PSL2.Group (ExtensionField (binaryParameters m hm)))
    (hz : z ∈ normalizer (S : Set _))
    (ho : orderOf z = (binaryParameters m hm).q-1)
    (hzA : MulAut.conj z ∈ normalizer (A : Set _)) :
    A ≤ MulAut.innerSubgroup (Theory.PSL2.Group (ExtensionField (binaryParameters m hm))) := by
  let F := ExtensionField (binaryParameters m hm)
  let C := zpowers z
  have hC : C ≤ normalizer (S : Set _) := zpowers_le.mpr hz
  have hcA : C.map MulAut.conj ≤ normalizer (A : Set _) := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hzA
  let D := (A ⊓ MulAut.innerSubgroup (Theory.PSL2.Group F)).comap MulAut.conj
  have hinj : Function.Injective (MulAut.conj : Theory.PSL2.Group F →* _) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot (psl_center_eq_bot (F := F))
  have hD : IsPGroup 2 D := (hA.to_le inf_le_left).comap_of_injective _ hinj
  intro α hα
  apply inner_of_base_sylow_displacements m hm S C hC
    ((Nat.card_zpowers z).trans ho) α
    (by obtain ⟨k,hk⟩ := hA ⟨α,hα⟩; exact ⟨k,congrArg Subtype.val hk⟩) (hS α hα)
  intro x hx
  have hb := hcA (mem_map_of_mem MulAut.conj hx)
  have ha : (MulAut.conj x)⁻¹*α*MulAut.conj x ∈ A :=
    (mem_normalizer_iff.mp (inv_mem hb) α).mp hα
  have heq : MulAut.conj (x⁻¹*α x) = ((MulAut.conj x)⁻¹*α*MulAut.conj x)*α⁻¹ := by
    ext y
    change (x⁻¹*α x)*y*(x⁻¹*α x)⁻¹=x⁻¹*α (x*α.symm y*x⁻¹)*x
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  have hm : x⁻¹*α x ∈ D :=
    ⟨heq ▸ A.mul_mem ha (A.inv_mem hα),⟨x⁻¹*α x,rfl⟩⟩
  have hxα : α x ∈ normalizer (S : Set _) := by
    have hh := mem_map_of_mem α.toMonoidHom (hC hx)
    have heN : (normalizer (S : Set _)).map α.toMonoidHom=normalizer (S : Set _) := by
      change (normalizer ((S : Subgroup (Theory.PSL2.Group F)) : Set (Theory.PSL2.Group F))).map α.toMonoidHom = _
      rw [map_normalizer_eq_of_bijective _ α.bijective,hS α hα]
      rfl
    exact heN ▸ hh
  have hh : x⁻¹*α x ∈ D ⊓ normalizer (S : Set (Theory.PSL2.Group F)) := by
    constructor
    · exact hm
    · exact (normalizer (S : Set (Theory.PSL2.Group F))).mul_mem
        ((normalizer (S : Set (Theory.PSL2.Group F))).inv_mem (hC hx)) hxα
  rw [hD.inf_normalizer_sylow S] at hh
  exact hh.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison
private theorem base_torus_actor_inner_of_mulEquiv {C : Type*} [Group C] [Finite C]
    (m : ℕ) (hm : 0<m)
    (e : C ≃* Theory.PSL2.Group (ExtensionField (binaryParameters m hm)))
    (S : Sylow 2 C) (A : Subgroup (MulAut C)) (hA : IsPGroup 2 A)
    (hS : ∀ α∈A, (S : Subgroup C).map α.toMonoidHom = S)
    (z : C) (hz : z ∈ normalizer (S : Set C))
    (ho : orderOf z = (binaryParameters m hm).q-1)
    (hzA : MulAut.conj z ∈ normalizer (A : Set _)) :
    A ≤ MulAut.innerSubgroup C := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let f := (MulAut.congr e).toMonoidHom
  let D := A.map f
  have hQ : (Q : Subgroup _) = (S : Subgroup C).map e.toMonoidHom := rfl
  have hQP : ∀ β∈D, (Q : Subgroup _).map β.toMonoidHom = Q := by
    rintro β ⟨α,hα,rfl⟩
    change (Q : Subgroup _).map (MulAut.congr e α).toMonoidHom = Q
    rw [hQ,map_map]
    have hc : (MulAut.congr e α).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := by ext x; simp
    rw [hc,←map_map,hS α hα]
  have hzQ : e z ∈ normalizer (Q : Set _) :=
    (le_normalizer_map e.toMonoidHom) (mem_map_of_mem e.toMonoidHom hz)
  have hzD : MulAut.conj (e z) ∈ normalizer (D : Set _) := by
    rw [←MulAut.congr_conj]
    exact (le_normalizer_map f) (mem_map_of_mem f hzA)
  have hD := base_torus_actor_inner m hm Q D (hA.map f) hQP (e z) hzQ
    ((e.orderOf_eq z).trans ho) hzD
  intro α hα
  have hh := hD (mem_map_of_mem f hα)
  rw [←MulAut.map_innerSubgroup_congr e] at hh
  exact (mem_map_iff_mem (MulAut.congr e).injective).mp hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityTorusComparison

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem Preparation.left_core_le_sourceS_of_base_torus
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H)) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i)
    (m : ℕ) (hm : 0<m)
    (e : (residual H ⧸ pCore 2 (residual H)) ≃*
      Theory.PSL2.Group (ExtensionField (binaryParameters m hm)))
    (k : residual H) (hkB : k.val ∈ localBorel T (residual H))
    (hko : orderOf (QuotientGroup.mk' (pCore 2 (residual H)) k)=
      (binaryParameters m hm).q-1)
    (a : normalizer (residual H : Set G)) (ha : a.val ∈ localBorel T L)
    (hea : pCoreNormalizerAction 2 (residual H) a =
      MulAut.conj (QuotientGroup.mk' (pCore 2 (residual H)) k)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ sourceS L H := by
  have hchar : (binaryParameters m hm).prime=2 := rfl
  let : CharP (ExtensionField (binaryParameters m hm)) 2 := hchar ▸
    inferInstanceAs (CharP (ExtensionField (binaryParameters m hm)) (binaryParameters m hm).prime)
  let K := residual H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let N := normalizer (K : Set G)
  let f := pCoreNormalizerAction 2 K
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hTN : (T : Subgroup G) ≤ N := hTH.trans (le_normalizer_residual H)
  have hQN : Q ≤ N := hQT.trans hTN
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let D := (Q.subgroupOf N).map f
  have hD : IsPGroup 2 D := (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype.map f
  have hPs := d.sylow 1
  change ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = sourceS L H ⊓ K at hPs
  obtain ⟨P,hP⟩ := hPs
  have hSK : sourceS L H ≤ K := hS 1
  rw [inf_eq_left.mpr hSK] at hP
  have hP' : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,subgroupOf_map_subtype]
    exact (d.ordinary_sylow_core_geometry h hTH hS).1 1
  let q := QuotientGroup.mk' (pCore 2 K)
  let Pq := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  have hpre : (Pq : Subgroup (K ⧸ pCore 2 K)).comap q = P := by
    change ((P : Subgroup K).map q).comap q = _
    exact comap_map_eq_self (by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P)
  have hDP : ∀ α ∈ D, (Pq : Subgroup (K ⧸ pCore 2 K)).map α.toMonoidHom = Pq := by
    rintro α ⟨a,ha,rfl⟩
    let b := K.normalizerMonoidHom a
    have hPb : (P : Subgroup K).map b.toMonoidHom = P := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        rw [hP'] at hx ⊢
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem (hQT ha) hx)
          ((T : Subgroup G).inv_mem (hQT ha))
      · rw [card_map_of_injective (f := b.toMonoidHom) b.injective]
    have hc : (f a).toMonoidHom.comp q = q.comp b.toMonoidHom := by
      ext x
      exact pCoreNormalizerAction_mk 2 K a x
    change ((P : Subgroup K).map q).map (f a).toMonoidHom = _
    rw [map_map,hc,←map_map,hPb]
    rfl
  have hkNP : k ∈ normalizer (P : Set K) := by
    rw [localBorel_eq_map] at hkB
    obtain ⟨b,hb,hbk⟩ := hkB
    have he : b=k := Subtype.ext hbk
    subst b
    change k ∈ normalizer ((P : Subgroup K) : Set K)
    rwa [hP']
  have hkN : q k ∈ normalizer (Pq : Set (K ⧸ pCore 2 K)) :=
    (le_normalizer_map q) (mem_map_of_mem q hkNP)
  have hkD : MulAut.conj (q k) ∈ normalizer (D : Set (MulAut (K ⧸ pCore 2 K))) := by
    rw [←hea]
    apply le_normalizer_map f
    apply mem_map_of_mem f
    apply mem_normalizer_iff.mpr
    intro y
    change y.val ∈ Q ↔ a.val*y.val*a.val⁻¹ ∈ Q
    exact mem_normalizer_iff.mp (hLQ ha.1) y.val
  have hinner : D ≤ MulAut.innerSubgroup (K ⧸ pCore 2 K) :=
    TrialityTorusComparison.base_torus_actor_inner_of_mulEquiv m hm e Pq D hD hDP
      (q k) hkN hko hkD
  intro t ht
  have hti := hinner (mem_map_of_mem f (show (⟨t,hQN ht⟩ : N) ∈ Q.subgroupOf N from ht))
  have hk : (⟨t,hQT ht⟩ : T) ∈ (residualSylowFieldAction hTH e).ker := by
    change Theory.PSL2.fieldProjection (ExtensionField (binaryParameters m hm)) (MulAut.congr e (f ⟨t,hQN ht⟩)) = 1
    rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker]
    change MulAut.congr e (f ⟨t,hQN ht⟩) ∈ MulAut.innerSubgroup (Theory.PSL2.Group (ExtensionField (binaryParameters m hm)))
    rw [←MulAut.map_innerSubgroup_congr e]
    exact mem_map_of_mem (MulAut.congr e).toMonoidHom hti
  rw [d.residual_sylow_field_kernel h hTH hS e] at hk
  exact hk

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The left base-field torus detects the right coefficient up to a cubic
kernel. The original LT-core is a two-group, so this kernel vanishes. -/
theorem Preparation.triality_left_core_le_sourceS
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ sourceS L H := by
  have hS := d.triality_sourceS_le_factors h hTH hp m hm he
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp _ rfl he).elim
  obtain ⟨e⟩ := he
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : Y →* Carrier P := (parabolic P .arms).subtype.comp e.right.toMonoidHom
  have hf : Function.Injective f := (parabolic P .arms).subtype_injective.comp e.right.injective
  have hKY : residual H ≤ Y := le_sup_left.trans le_sup_left
  have hKf : ((residual H).subgroupOf Y).map f = localFactor P .arms := by
    have hK : (residual H).subgroupOf Y = solvableResidual Y := by
      apply map_injective Y.subtype_injective
      rw [map_subgroupOf_eq_of_le hKY]
      exact (d.parabolic_residuals h hTH hp 1).symm
    rw [hK,show f = (parabolic P .arms).subtype.comp e.right.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact TrialityComparison.arms_parabolic_residual P rfl
  let eK : residual H ≃* localFactor P .arms :=
    ((subgroupOfEquivOfLe hKY).symm.trans
      (((residual H).subgroupOf Y).equivMapOfInjective f hf)).trans (MulEquiv.subgroupCongr hKf)
  let eQ := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans
    (localFactorArmsQuotientEquivPSL2 P rfl)
  obtain ⟨t,ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (fixedField P)ˣ)
  rw [Nat.card_units,card_fixedField] at ht
  obtain ⟨a,k,ha,hk,ho,_,hea⟩ := d.triality_base_torus_action_lift h hTH hp m hm e t
  exact d.left_core_le_sourceS_of_base_torus h hTH hS m hm eQ k hk (ho.trans ht) a ha hea

/-- The original triality center fixer belongs to S at every field degree. -/
theorem Preparation.triality_center_fixer_le_sourceS
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H :=
  (d.triality_center_fixer_le_left_core_join_sourceS h hTH hp m hm he).trans
    (sup_le (d.triality_left_core_le_sourceS h hTH hp m hm he) le_rfl)

/-- The marked triality nonfusion conclusion, with the original center-fixer
premise discharged also at even field degrees. -/
theorem Preparation.triality_short_root_not_fused
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ v∈Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val=v ∧ (e.right w).val=short (binaryParameters m hm) rfl 2 1) ∧
      v∉Z ∧ orderOf v=2 ∧ ∀ g : G, v∉Z.conjBy g :=
  d.triality_short_root_not_fused_of_centralizer_le h hH hp m hm he
    (d.triality_center_fixer_le_sourceS h hH.1.1.2 hp m hm he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
