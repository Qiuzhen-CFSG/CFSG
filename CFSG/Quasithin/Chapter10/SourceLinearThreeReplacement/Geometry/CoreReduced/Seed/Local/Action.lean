module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Natural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Source
public import Theory.GroupTheory.WreathTwoCoreQuotient
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPoint

/-!
# The diagonal seed quotient and the actual factor permutation

The proved natural action of L₀T identifies the diagonal stabilizer with
a two-group cover of S₄ wr C₂. Its two-core quotient and the original
residual maps give X/O₂(X) elementary of order nine, so X is not a two-group.

A two-core element cannot swap the natural factors: its commutators with
the first point stabilizer would project a two-group onto the whole S₄.
The original coordinates then show that every core element preserves L.
This is an action calculation on the original L₀T, before any recognition
of the later K_zT or construction of CentralizerData.

Source: Aschbacher--Smith 10.1.1(3) and 10.2.11,
printed pp.741,753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Matrix
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local
open Overgroups.Closure.Parabolic Natural Natural.OriginalAction
open Matrix.PSL3Two
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

private def originalAction (c : Configuration s a b) : Natural.ActionData s c.fixed where
  hom := (Natural.OriginalAction.originalLift s c.fixed).hom
  onto := (Natural.OriginalAction.originalLift s c.fixed).surjective
  kernel_two := (Natural.OriginalAction.originalLift s c.fixed).kernel_two
  equivariant := (Natural.OriginalAction.originalLift s c.fixed).equivariant

private def diagonalVector (c : Configuration s a b) : D.fullModule :=
  ⟨a*b,D.fullModule.mul_mem (survivor_moved_le s c.first_mem)
    (survivor_partner_le s c.second_mem)⟩

private def pointMap (c : Configuration s a b) :
    diagonalParabolic T L (a*b) →*
      Natural.pointStabilizer (Natural.fullCoordinates s c.fixed (diagonalVector c)) := by
  let f := originalAction c
  exact (f.hom.comp (inclusion (diagonalParabolic_le_join (a*b)))).codRestrict _ (by
    intro x
    have hh : (⟨x,diagonalParabolic_le_join (a*b) x.property⟩ : localJoin T L) ∈
        (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) := x.property
    have hp := f.stabilizer_preimage (diagonalVector c)
    change (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) = _ at hp
    rw [hp] at hh
    exact hh)

private theorem pointMap_surjective (c : Configuration s a b) : Function.Surjective (pointMap c) := by
  let f := originalAction c
  intro y
  obtain ⟨g,hg⟩ := f.onto y.val
  have hm : g ∈ (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) := by
    have hp := f.stabilizer_preimage (diagonalVector c)
    change (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) = _ at hp
    rw [hp]
    change f.hom g ∈ Natural.pointStabilizer
      (Natural.fullCoordinates s c.fixed (diagonalVector c))
    rw [hg]
    exact y.property
  exact ⟨⟨g.val,hm⟩,Subtype.ext hg⟩

/-- The original point-centralizer quotient, obtained from its natural action. -/
def parabolicQuotient (c : Configuration s a b) :
    (diagonalParabolic T L (a*b) ⧸ pCore 2 (diagonalParabolic T L (a*b))) ≃*
      WreathTwoResidual.Actor := by
  let f := originalAction c
  let z : D.fullModule := ⟨a*b,D.fullModule.mul_mem
    (survivor_moved_le s c.first_mem) (survivor_partner_le s c.second_mem)⟩
  let v := Natural.fullCoordinates s c.fixed z
  have hv : ∀ i, v i ≠ 1 := Natural.diagonal_coordinates_ne_one s c.fixed
    c.first_mem c.second_mem c.first_ne c.second_ne
  let e := f.parabolicQuotientEquiv z
    (Natural.PointModel.pointStabilizerEquivSymmetricWreath v hv)
  let eSL := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  exact e.trans (RegularWreathProduct.congr eSL.symm (MulEquiv.refl _))

/-- The original seed modulo its own two-core is elementary of order nine. -/
theorem quotient_nine (c : Configuration s a b) :
    Nonempty ((centralizerSeed T L (a*b) ⧸ pCore 2 (centralizerSeed T L (a*b))) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  let P := diagonalParabolic T L (a*b)
  obtain ⟨e⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine (parabolicQuotient c)
  let f : pResidual 2 P ≃* centralizerSeed T L (a*b) :=
    ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr (diagonalParabolic_residual (a*b)))
  exact ⟨(QuotientGroup.congr _ _ f.symm (pCore_map_iso 2 f.symm)).trans e⟩

/-- The seed retains a nontrivial odd quotient. -/
theorem not_two (c : Configuration s a b) : ¬ IsPGroup 2 (centralizerSeed T L (a*b)) := by
  intro hp
  obtain ⟨e⟩ := quotient_nine c
  have hq := hp.of_surjective (QuotientGroup.mk' (pCore 2 (centralizerSeed T L (a*b))))
    (QuotientGroup.mk'_surjective _)
  have h9 : IsPGroup 2 (Multiplicative (Fin 2 → ZMod 3)) := hq.of_equiv e
  obtain ⟨n,hn⟩ := h9.exists_card_eq
  have hc : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
    change Nat.card (Fin 2 → ZMod 3) = 9
    simp
  have hd : 3 ∣ 2 ^ n := by rw [← hn,hc]; decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem point_not_two (v : Eight) (hv : v ≠ 1) :
    ¬ IsPGroup 2 (MulAction.stabilizer SL v.toAdd) := by
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    flagPoint.val v.toAdd flagPoint.property hv
  change g • flagPoint.val = v.toAdd at hg
  have he : MulAction.stabilizer SL v.toAdd =
      pointParabolicSL.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    congr 1
    ext x
    rw [← Fano.stabilizer_flagPoint_SL]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  intro h
  have hp := (he ▸ h).of_equiv ((MulAut.conj g).subgroupMap pointParabolicSL).symm
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : 3 ∣ 2^n := by rw [← hn,card_pointParabolicSL]; decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem core_right (v : Space) (hv : v 1 ≠ 1)
    (x : pointStabilizer v) (hx : x ∈ pCore 2 (pointStabilizer v)) :
    x.val.right = 1 := by
  classical
  by_contra hright
  have hr : x.val.right = other := (bit_cases x.val.right).resolve_left hright
  let S := pointStabilizer v
  let N := pCore 2 S
  let B : Subgroup S := (RegularWreathProduct.rightHom : Actor →* Bit).ker.comap S.subtype
  let NB := N ⊓ B
  let A : Subgroup SL := MulAction.stabilizer SL (v 1).toAdd
  have fix (y : NB) : y.val.val.left 1 ∈ A := by
    have hh := congrFun y.val.property 1
    have hr : y.val.val.right = 1 := y.property.2
    change action y.val.val v 1 = v 1 at hh
    rw [action_apply,hr] at hh
    change (y.val.val.left 1).val *ᵥ (v 1).toAdd = (v 1).toAdd
    simpa only [inv_one,one_mul,toAdd_ofAdd] using congrArg Multiplicative.toAdd hh
  let f : NB →* A := {
    toFun y := ⟨y.val.val.left 1,fix y⟩
    map_one' := rfl
    map_mul' y z := by
      apply Subtype.ext
      change y.val.val.left 1 * z.val.val.left (y.val.val.right⁻¹ * 1) = _
      rw [show y.val.val.right = 1 from y.property.2]
      simp }
  have onto : Function.Surjective f := by
    intro a
    have ha : firstBase a.val ∈ S := by
      change action (firstBase a.val) v = v
      funext i
      rw [firstBase_action]
      by_cases hi : i = 1
      · subst i
        simp only [ite_true]
        exact congrArg Multiplicative.ofAdd a.property
      · simp only [hi,if_false]
    let aS : S := ⟨firstBase a.val,ha⟩
    let y : S := aS * x * aS⁻¹ * x⁻¹
    have hyn : y ∈ N := N.mul_mem
      ((inferInstance : N.Normal).conj_mem x hx aS) (N.inv_mem hx)
    have hyb : y ∈ B := by
      change (firstBase a.val * x.val * (firstBase a.val)⁻¹ * x.val⁻¹).right = 1
      simp [firstBase]
    refine ⟨⟨y,hyn,hyb⟩,?_⟩
    apply Subtype.ext
    change (firstBase a.val * x.val * (firstBase a.val)⁻¹ * x.val⁻¹).left 1 = a.val
    simp [RegularWreathProduct.mul_left,RegularWreathProduct.inv_left,firstBase,hr]
  exact point_not_two (v 1) hv (((pCore_isPGroup (p := 2) (G := S)).to_le inf_le_left).of_surjective f onto)

private theorem normalizes_of_right (c : Configuration s a b) (g : localJoin T L)
    (hg : ((originalLift s c.fixed).hom g).right = 1) :
    (g : G) ∈ normalizer (L : Set G) := by
  by_contra hout
  have hgm : (g : G) ∈ D.maximalLocal :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) g.property
  have hLg : L.map (MulAut.conj (g : G)).toMonoidHom =
      L.map (MulAut.conj s.exchange).toMonoidHom := by
    exact (source_nonnormal_maximal_pair D (survivor_nonnormal s)
      s.exchange_mem s.exchange_moves g hgm).resolve_left
        (fun h => hout (mem_normalizer_iff_map_conj_eq.mpr h))
  have hVg : (⁅D.fullModule,L⁆).map (MulAut.conj (g : G)).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    have hV (m : G) (hm : m ∈ D.maximalLocal) :
        D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
    rw [map_commutator,map_commutator,hV g hgm,
      hV s.exchange (le_normalizer_componentOrbit L T s.exchange_mem),hLg]
  let av : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨a,c.first_mem⟩
  let bv : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :=
    ⟨(g : G)*a*(g : G)⁻¹, hVg ▸ mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom c.first_mem⟩
  have he : joinAction D g (factorProduct s c.fixed (av,1)) =
      factorProduct s c.fixed (1,bv) := by
    apply Subtype.ext
    rw [joinAction_apply,factorProduct_apply,factorProduct_apply]
    simp only [OneMemClass.coe_one,mul_one,one_mul]
    rfl
  have hh := congrFun ((originalLift s c.fixed).equivariant g
    (factorProduct s c.fixed (av,1))) 1
  rw [he,coordinates_factorProduct,action_apply,hg] at hh
  simp only [ite_true,map_one,inv_one,one_mul] at hh
  rw [coordinates_factorProduct] at hh
  simp only [ite_true] at hh
  have hz : Matrix.SpecialLinearGroup.toLin' (((originalLift s c.fixed).hom g).left 1)
      (s.natural.coordinates av).toAdd = 0 := (congrArg Multiplicative.toAdd hh).symm
  exact first_coordinates_ne_one c
    ((Matrix.SpecialLinearGroup.toLin' _).map_eq_zero_iff.mp hz)

/-- The literal diagonal-parabolic core preserves the original component. -/
theorem parabolic_core_le_stabilizer (c : Configuration s a b) :
    (diagonalParabolic T L (a*b)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let P := diagonalParabolic T L (a*b)
  have hQT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (sylow_le_diagonalParabolic c.central))
    change P.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P).map P.subtype at hh
    rwa [map_subgroupOf_eq_of_le (sylow_le_diagonalParabolic c.central)] at hh
  refine le_inf hQT ?_
  rintro g ⟨x,hx,rfl⟩
  have hmap : (pCore 2 P).map (pointMap c) ≤
      pCore 2 (Natural.pointStabilizer (Natural.fullCoordinates s c.fixed (diagonalVector c))) :=
    le_sSup ⟨(inferInstance : (pCore 2 P).Normal).map _ (pointMap_surjective c),
      pCore_isPGroup.map (pointMap c)⟩
  have hr := core_right _ (Natural.diagonal_coordinates_ne_one s c.fixed
    c.first_mem c.second_mem c.first_ne c.second_ne 1) (pointMap c x)
      (hmap (mem_map_of_mem (pointMap c) hx))
  exact normalizes_of_right c (inclusion (diagonalParabolic_le_join (a*b)) x) hr
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local
