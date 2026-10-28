module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.PairAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates
import all Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.Bridge
public import Theory.GroupTheory.CommutatorOrbitCard
/-! # Five-actor displacement in the actual second J₄ local model

The eleven-dimensional elementary kernel has eight fixed elements under an
order-five quotient actor. A checked star word and its four nonidentity powers
supply the finite mask calculation. The star-group order has five-part five,
so Sylow conjugacy covers every actor. The mask equivalence identifies these
fixed points with the actual kernel centralizer; the conjugacy orbit bound
then gives displacement greater than sixteen.

The private quotient implementation is read with `import all` only to identify
its star projection with `Second.starHom`; no shared boundary is widened.
Source: the ATLAS max1 kernel and star labels, as used in Aschbacher–Smith
2.4.25, printed p.543, and 16.1.5(9), printed p.1172. -/
public section
open scoped Pointwise
namespace Janko4.InvolutionCentralizers.Second.FiveAction
open Subgroup Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
open LocalStructure.SylowCore LocalStructure.SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
set_option backward.isDefEq.respectTransparency true
private noncomputable def starAction : StarGroup →* Equiv.Perm max1Kernel :=
  (ActionImage matrixA_mul_self matrixB_pow_four).subtype.comp
    (actionImageEquivStarGroup matrixA_mul_self matrixB_pow_four).symm.toMonoidHom

private theorem starAction_starHom (g : Second.Local) :
    starAction (starHom g) = action matrixA_mul_self matrixB_pow_four g :=
  congrArg Subtype.val ((actionImageEquivStarGroup _ _).symm_apply_apply _)

private theorem starProjection_eq_starHom (g : Second.Local) :
    starProjection matrixA_mul_self matrixB_pow_four g = starHom g := rfl

private theorem starAction_mask (p : StarGroup) (m : Fin 2048) :
    maskEquiv matrixA_mul_self matrixB_pow_four
      ⟨starMask p m.val, starMask_lt _ _⟩ =
      starAction p (maskEquiv matrixA_mul_self matrixB_pow_four m) := by
  obtain ⟨g,rfl⟩ := starHom_surjective p
  rw [starAction_starHom,←starProjection_eq_starHom]
  exact maskEquiv_starMask _ _ _ _

private noncomputable def fixedCard (p : StarGroup) : ℕ := Nat.card {v : max1Kernel // starAction p v = v}

private theorem fixedCard_masks (p : StarGroup) :
    fixedCard p = Nat.card {m : Fin 2048 // starMask p m.val = m.val} := by
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (maskEquiv matrixA_mul_self matrixB_pow_four)
  intro m
  rw [←starAction_mask]
  constructor
  · intro h; congr 1; exact Fin.ext h
  · intro h
    exact congrArg Fin.val ((maskEquiv matrixA_mul_self matrixB_pow_four).injective h)

private theorem fixedCard_conj (p c : StarGroup) :
    fixedCard (c*p*c⁻¹) = fixedCard p := by
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (starAction c)
  intro v
  simp only [map_mul,map_inv,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  exact (starAction c).injective.eq_iff.symm

private theorem kernel_centralizer_card (g : Second.Local) :
    Nat.card ((centralizer ({g} : Set Second.Local)).subgroupOf max1Kernel) =
      fixedCard (starHom g) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl max1Kernel)
  intro v
  change v.val ∈ centralizer ({g} : Set Second.Local) ↔ _
  rw [mem_centralizer_singleton_iff,starAction_starHom]
  change v.val*g=g*v.val ↔ action matrixA_mul_self matrixB_pow_four g v=v
  constructor
  · intro h
    apply Subtype.ext
    change g*v.val*g⁻¹=v.val
    rw [←h,mul_assoc,mul_inv_cancel,mul_one]
  · intro h
    have hh := congrArg (fun u : max1Kernel => (u : Second.Local)) h
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem starHom_ker : starHom.ker = max1Kernel := by
  have he : starHom = starProjection matrixA_mul_self matrixB_pow_four :=
    MonoidHom.ext fun g => (starProjection_eq_starHom g).symm
  rw [he, starProjection_ker]


private def word {G : Type*} [Group G] (x y : G) : G :=
  x*y*x*y*y*x*y*x*y*x*y*y*x*y*y
private def r : StarGroup :=
  word ⟨rightX, by
    have h : starX ∈ StarGroup := Subgroup.subset_closure (Set.mem_insert _ _)
    exact StarGroup.inv_mem h⟩
    ⟨rightY, by
      have h : starY ∈ StarGroup := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      exact StarGroup.inv_mem h⟩
private theorem r_order : orderOf r = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (word rightX rightY) ^ 5 = 1
    decide +kernel
  · intro h
    have hh := congrArg (fun g : StarGroup => g.val (2 : Fin 24)) h
    change word rightX rightY 2 = 2 at hh
    exact (by decide : word rightX rightY 2 ≠ 2) hh
private def fixedMasks (i : Fin 5) : Finset (Fin 2048) :=
  Finset.univ.filter (fun m => starMask (r ^ i.val) m.val = m.val)
private theorem fixedMasks_card (i : Fin 5) (hi : i ≠ 0) : (fixedMasks i).card = 8 := by
  have h : ∀ i : Fin 5, i ≠ 0 → (fixedMasks i).card = 8 := by decide +kernel
  exact h i hi

private def fiveSylow (p : StarGroup) (hp : orderOf p = 5) : Sylow 5 StarGroup := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : Nat.card (zpowers p) = 5 := (Nat.card_zpowers p).trans hp
  refine (IsPGroup.of_card (n := 1) hc).toSylow ?_
  intro hi
  have hd : 25 ∣ Nat.card StarGroup := by
    rw [← (zpowers p).card_mul_index,hc]
    exact Nat.mul_dvd_mul_left 5 hi
  rw [starGroup_order] at hd
  norm_num at hd

private theorem align_five (p : StarGroup) (hp : orderOf p = 5) :
    ∃ c : StarGroup, ∃ i : Fin 5, i ≠ 0 ∧ c*p*c⁻¹ = r ^ i.val := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq StarGroup (fiveSylow p hp) (fiveSylow r r_order)
  have hm : c*p*c⁻¹ ∈ zpowers r := by
    have hh := Subgroup.smul_mem_pointwise_smul p (MulAut.conj c)
      (fiveSylow p hp : Subgroup StarGroup) (mem_zpowers p)
    change c*p*c⁻¹ ∈ c • fiveSylow p hp at hh
    rw [hc] at hh
    exact hh
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp
    ((isOfFinOrder_of_finite r).mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hk5 : k < 5 := by simpa [r_order] using hk
  refine ⟨c,⟨k,hk5⟩,?_,he.symm⟩
  intro hi
  have hk0 : k = 0 := congrArg Fin.val hi
  have hh : (MulAut.conj c) p = 1 := by
    change c*p*c⁻¹=1
    simpa only [hk0,pow_zero] using he.symm
  have hx1 : p = 1 := (MulAut.conj c).injective (hh.trans (map_one _).symm)
  rw [hx1,orderOf_one] at hp
  omega

private theorem fixedCard_rpow (i : Fin 5) (hi : i ≠ 0) : fixedCard (r^i.val) = 8 := by
  rw [fixedCard_masks,Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact fixedMasks_card i hi

/-- Each order-five actor on the literal elementary kernel fixes eight elements. -/
theorem kernel_centralizer_card_eq_eight (g : Second.Local)
    (hg : orderOf (starHom g) = 5) :
    Nat.card ((centralizer ({g} : Set Second.Local)).subgroupOf max1Kernel) = 8 := by
  rw [kernel_centralizer_card]
  obtain ⟨c,i,hi,hc⟩ := align_five (starHom g) hg
  rw [← fixedCard_conj (starHom g) c,hc]
  exact fixedCard_rpow i hi

/-- An order-five quotient actor displaces more than sixteen elements of E2048. -/
theorem sixteen_lt_displacement (g : Second.Local)
    (hg : orderOf (starHom g) = 5) :
    16 < Nat.card (⁅max1Kernel,zpowers g⁆ : Subgroup Second.Local) := by
  have h := card_le_commutator_card_mul_centralizer max1Kernel g
  rw [kernel_centralizer_card_eq_eight g hg] at h
  have he : Nat.card max1Kernel = 2048 := localKernel_card _ _
  rw [he] at h
  omega

end Janko4.InvolutionCentralizers.Second.FiveAction
