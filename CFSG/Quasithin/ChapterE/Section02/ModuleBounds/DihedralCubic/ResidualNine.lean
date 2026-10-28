module

public import Theory.GroupTheory.ConjugatePairSeed.OrthogonalAction
public import Theory.GroupTheory.PResidual.Defs
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularInvolutionPairs
public import Theory.GroupTheory.WreathTwoThreeCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Excluding a residual-nine inverter on the marked quaternion subgroup

The unique subgroup of order nine in the orthogonal wreath actor consists of
independent cubic rotations of the two quaternion planes. An actor inverting
that subgroup preserves both planes. If its displacement squares are all one,
the square-form coordinates instead force this plane-preserving actor to be
the identity, which cannot invert a cubic rotation.

The literal conjugation consumers retain the original embedded quaternion
subgroup, elementary subgroup, and residual image. In the source consumer,
normality and order thirty-two place the quaternion subgroup in the specified
Sylow subgroup, whose normalization of the elementary subgroup supplies the
required displacement squares. Construction of the global normal quaternion
subgroup and descent of the residual inversion identity remain explicit inputs.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.2.17,
printed pp.229--230, exclusion of the order-nine orthogonal residual.
-/

public section

open Subgroup
namespace BinaryFourPlus

private theorem core_card : Nat.card (pCore 3 Wreath)=9 := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl C2)
  rw [← pCore_map_iso 3 e,card_map_of_injective e.injective]
  exact Theory.GroupTheory.WreathTwoResidual.threeCore_card

private theorem core_quotient_two : IsPGroup 2 (Wreath⧸pCore 3 Wreath) := by
  apply IsPGroup.of_card (n:=3)
  have h := (pCore 3 Wreath).card_mul_index
  have hc : Nat.card Wreath=72 :=
    (Nat.card_congr isometryEquivWreath.toEquiv).symm.trans card_isometrySubgroup
  rw [core_card,index_eq_card,hc] at h
  omega

private theorem subgroup_nine_eq_core (P : Subgroup Wreath) (hP : Nat.card P=9) :
    P=pCore 3 Wreath := by
  have hp : IsPGroup 3 P := IsPGroup.of_card (n:=2) hP
  let f := QuotientGroup.mk' (pCore 3 Wreath)
  have hd : Disjoint (P.map f) (⊤ : Subgroup (Wreath⧸pCore 3 Wreath)) :=
    IsPGroup.disjoint_of_coprime (hp.map f)
      (core_quotient_two.to_subgroup ⊤) (by decide)
  have hz : P.map f=⊥ := by simpa using hd
  have hle : P≤pCore 3 Wreath := by
    simpa only [f,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  exact eq_of_le_of_card_ge hle (by rw [hP,core_card])

private theorem cube_mem_core (w : Wreath) (hw : w^3=1) : w∈pCore 3 Wreath := by
  let f := QuotientGroup.mk' (pCore 3 Wreath)
  have hd : orderOf (f w)∣3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow,hw,map_one])
  have hc := core_quotient_two.orderOf_coprime (by decide : Nat.Coprime 2 3) (f w)
  exact (QuotientGroup.eq_one_iff w).mp (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd))

private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def axisCycle : Wreath := ⟨fun i=>if i=1 then cycle else 1,1⟩
private theorem cycle_cube : cycle^3=1 := by decide +kernel
private theorem axisCycle_cube : axisCycle^3=1 := by
  apply RegularWreathProduct.ext
  · funext i
    by_cases hi : i=1
    · simpa [axisCycle,pow_succ,hi] using cycle_cube
    · simp [axisCycle,pow_succ,hi]
  · simp [axisCycle,pow_succ]

private theorem inverter_preserving (w : Wreath)
    (hi : w*axisCycle*w⁻¹=axisCycle⁻¹) : w.right=1 := by
  by_contra hn
  have hs : w.right=swapIndex :=
    ((by decide : ∀ i : C2, i=1 ∨ i=swapIndex) w.right).resolve_left hn
  have he := congrArg (fun x : Wreath => x.left 1) hi
  have hc : (cycle : Equiv.Perm (Fin 3))⁻¹≠1 := by decide +kernel
  apply hc
  simpa [axisCycle,hs,swapIndex_inv,swapIndex_ne_one] using he.symm

private theorem not_singular_of_inverts_nine (w : Wreath) (P : Subgroup Wreath)
    (hP : Nat.card P=9) (hi : ∀ x∈P,w*x*w⁻¹=x⁻¹) :
    ¬SingularDisplacements w := by
  intro hw
  have hx : axisCycle∈P := by
    rw [subgroup_nine_eq_core P hP]
    exact cube_mem_core _ axisCycle_cube
  have he := eq_one_of_singular_preserving w hw (inverter_preserving w (hi _ hx))
  have h := hi _ hx
  rw [he,one_mul,inv_one,mul_one] at h
  have hc : cycle≠cycle⁻¹ := by decide +kernel
  exact hc (by simpa [axisCycle] using congrArg (fun x : Wreath => x.left 1) h)

end BinaryFourPlus

open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.DihedralCubic

/-- Every order-nine subgroup of the quaternion orthogonal actor is elementary. -/
theorem orthogonal_subgroup_nine_elementary
    (P : Subgroup BinaryFourPlus.Wreath) (hP : Nat.card P=9) :
    IsElementaryAbelian 3 P := by
  rw [BinaryFourPlus.subgroup_nine_eq_core P hP]
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl BinaryFourPlus.C2)
  rw [← pCore_map_iso 3 e]
  let := Theory.GroupTheory.WreathTwoResidual.threeCore_elementary
  exact IsElementaryAbelian.map e.toMonoidHom

/-- Inversion of an order-nine orthogonal subgroup forces a displacement
whose square is nontrivial in the original quaternion central product. -/
theorem quaternion_not_elementary_displacements_of_inverts_nine
    {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)
    (a : MulAut Q) (P : Subgroup BinaryFourPlus.Wreath) (hP : Nat.card P=9)
    (hi : ∀ x∈P,d.quotientWreathAction a*x*(d.quotientWreathAction a)⁻¹=x⁻¹) :
    ¬ ∀ x : Q,(a x*x⁻¹)^2=1 := by
  intro hs
  exact BinaryFourPlus.not_singular_of_inverts_nine _ P hP hi
    (d.wreath_singular_displacement a hs)

/-- Literal seed conjugation: an elementary subgroup normalized by the seed
cannot contain an inverter of an order-nine image. The hypothesis is expressed
as membership in the exact action kernel, before taking the image. -/
theorem seed_image_ne_nine_of_elementary_normalized
    {G : Type*} [Group G] [Finite G] (I U V : Subgroup G)
    (hn : I≤normalizer (U : Set G)) (d : QuaternionCentralProductData U)
    [IsElementaryAbelian 2 V] (hUV : U≤normalizer (V : Set G))
    (v : I) (hv : (v:G)∈V) (K : Subgroup I)
    (hi : ∀ k∈K,seedOrthogonalAction I U hn d (v*k*v⁻¹*k)=1) :
    Nat.card (K.map (seedOrthogonalAction I U hn d))≠9 := by
  intro h9
  let a := seedConjugation I U hn v
  apply quaternion_not_elementary_displacements_of_inverts_nine d a
    (K.map (seedOrthogonalAction I U hn d)) h9
  · rintro x ⟨k,hk,rfl⟩
    apply eq_inv_of_mul_eq_one_left
    simpa only [map_mul,map_inv,seedOrthogonalAction,MonoidHom.comp_apply,a] using hi k hk
  · intro u
    apply Subtype.ext
    change ((v:G)*(u:G)*(v:G)⁻¹*(u:G)⁻¹)^2=1
    apply elemPow_eq_one_of_isElementaryAbelian (A:=V)
    have hc : ⁅U,V⁆≤V := le_normalizer_iff_commutator_le_right.mp hUV
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator hv u.property)

/-- The E.2.17 residual-nine contradiction after constructing the global normal
quaternion subgroup. Its containment in the marked Sylow subgroup is proved
here; no normalization of the earlier local pair core is assumed. -/
theorem source_residual_image_ne_nine
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) (U V : Subgroup H)
    [U.Normal] [IsElementaryAbelian 2 V] (d : QuaternionCentralProductData U)
    (hVS : V≤(S : Subgroup H))
    (hn : (V.subgroupOf (S : Subgroup H)).Normal)
    (v : H) (hv : v∈V)
    (hi : ∀ k∈pResidual 2 H,
      (d.quotientWreathAction.comp MulAut.conjNormal) (v*k*v⁻¹*k)=1) :
    Nat.card ((pResidual 2 H).map (d.quotientWreathAction.comp MulAut.conjNormal))≠9 := by
  intro h9
  apply quaternion_not_elementary_displacements_of_inverts_nine d (MulAut.conjNormal v)
    ((pResidual 2 H).map (d.quotientWreathAction.comp MulAut.conjNormal)) h9
  · rintro x ⟨k,hk,rfl⟩
    apply eq_inv_of_mul_eq_one_left
    simpa only [map_mul,map_inv,MonoidHom.comp_apply] using hi k hk
  · intro u
    apply Subtype.ext
    change (v*(u:H)*v⁻¹*(u:H)⁻¹)^2=1
    apply elemPow_eq_one_of_isElementaryAbelian (A:=V)
    have hUS : U≤(S : Subgroup H) :=
      (IsPGroup.of_card (p:=2) (n:=5) (by simpa using d.card)).le_sylow_of_normal S
    have hUV : U≤normalizer (V : Set H) :=
      hUS.trans ((normal_subgroupOf_iff_le_normalizer hVS).mp hn)
    have hc : ⁅U,V⁆≤V := le_normalizer_iff_commutator_le_right.mp hUV
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator hv u.property)

end CFSG.Quasithin.ChapterE.DihedralCubic
