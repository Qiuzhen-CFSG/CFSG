module

public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway1
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.CentralizerQuotientOperations
public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The Monster section in the actual central cover

A central odd-kernel quotient lifts an involution uniquely, and its whole
centralizing numerator lifts to a centralizing preimage. The quotient map
on that preimage is the literal composite with the original surjection.
For the fixed Griess carrier the numerator is the actual embedded local C.

The source group enters through its given identification of G/Z(G) with
that carrier. The lifted involution is noncentral because its image is the
specified nonidentity griessZ, so its centralizer is a proper two-local.
The lattice Conway quotient is a nonabelian simple section of that subgroup.
A.2.15(2) then contradicts its rank-three witness.

The unconditional `monsterQuotientData` and `coverQuotientData` instantiate
the proved spin–Leech surjection. The final exclusion theorems also instantiate
the lattice rank-three witness. They retain only the earlier-source rank
implication from A.2.15(2), whose source assembly belongs to qt-a-02 via
qt-a02-minimal-reduction. Both trivial centers and odd-primary centers are
treated. The older theorems suffixed `of_model_inputs` remain available.

Source: Aschbacher–Smith, A.2.13, A.2.15(2), A.2.19, printed pp.37–41;
Aschbacher, *Sporadic Groups*, 27.5–27.9 and 28.12–28.13.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.InvolutionCentralizerQuotientData
variable {G H S : Type*} [Group G] [Group H] [Group S]

private theorem involution_square (d : InvolutionCentralizerQuotientData H S) :
    d.involution ^ 2 = 1 := d.involution_order ▸ pow_orderOf_eq_one d.involution

def liftCentralOdd (d : InvolutionCentralizerQuotientData H S)
    (q : G →* H) (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hcentral : q.ker ≤ Subgroup.center G) : InvolutionCentralizerQuotientData G S where
  involution := OddCentralLifting.involutionLift q hq hodd d.involution (by exact involution_square d)
  involution_order := by
    apply orderOf_eq_prime (OddCentralLifting.involutionLift_square q hq hodd _ _)
    intro he
    have hi := OddCentralLifting.involutionLift_image q hq hodd d.involution (by exact involution_square d)
    rw [he, map_one] at hi
    have ho := d.involution_order
    rw [← hi, orderOf_one] at ho
    norm_num at ho
  numerator := d.numerator.comap q
  centralizes := by
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply OddCentralLifting.centralizes_of_image q hodd hcentral
      (OddCentralLifting.involutionLift_square q hq hodd _ _)
    rw [OddCentralLifting.involutionLift_image]
    exact Subgroup.mem_centralizer_singleton_iff.mp (d.centralizes hx)
  quotientMap := d.quotientMap.comp (q.subgroupComap d.numerator)
  surjective := d.surjective.comp (q.subgroupComap_surjective_of_surjective d.numerator hq)

theorem liftCentralOdd_image (d : InvolutionCentralizerQuotientData H S)
    (q : G →* H) (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hc : q.ker ≤ Subgroup.center G) :
    q (d.liftCentralOdd q hq hodd hc).involution = d.involution :=
  OddCentralLifting.involutionLift_image q hq hodd d.involution (by exact involution_square d)

theorem liftCentralOdd_numerator (d : InvolutionCentralizerQuotientData H S)
    (q : G →* H) (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hc : q.ker ≤ Subgroup.center G) :
    (d.liftCentralOdd q hq hodd hc).numerator = d.numerator.comap q := rfl

theorem liftCentralOdd_quotientMap (d : InvolutionCentralizerQuotientData H S)
    (q : G →* H) (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hc : q.ker ≤ Subgroup.center G) (x : d.numerator.comap q) :
    (d.liftCentralOdd q hq hodd hc).quotientMap x =
      d.quotientMap ⟨q x.val, x.property⟩ := rfl

theorem section_of_centralizer (d : InvolutionCentralizerQuotientData G S) :
    Section02.IsSectionOf S (Subgroup.centralizer ({d.involution} : Set G)) := by
  let e := Subgroup.subgroupOfEquivOfLe d.centralizes
  exact ⟨d.numerator.subgroupOf _, d.quotientMap.comp e.toMonoidHom,
    d.surjective.comp e.surjective⟩

end CFSG.Quasithin.ChapterA.InvolutionCentralizerQuotientData

namespace CFSG.Quasithin.ChapterA.MonsterLocalObstruction
open Sporadic.Monster Sporadic.Monster.Construction
open Sporadic.Monster.Construction.QuasithinObstruction
open Atlas.Conway

/-- The nonabelian-simple, r=3 consequence of earlier source A.2.15(2).
Its producer is qt-a02-minimal-reduction; qt-a-02 discharges it in final assembly. -/
def SimpleTwoLocalThreeRankBound (G : Type*) [Group G] : Prop :=
  ∀ (M : Subgroup G), M ≠ ⊤ → IsTwoLocal M →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      ¬ IsMulCommutative S → Section02.IsSectionOf S M → primeRank 3 S ≤ 2

def monsterData (hs : Function.Surjective cToLeechQuotient) :
    InvolutionCentralizerQuotientData GriessGroup LeechCentralQuotient where
  involution := griessZ
  involution_order := orderOf_eq_prime griessZ_square griessZ_ne_one
  numerator := localSubgroup
  centralizes := localSubgroup_le_centralizer_griessZ
  quotientMap := localToLeechQuotient
  surjective := hs.comp cEquivLocalSubgroup.symm.surjective

variable {G : Type*} [Group G]

def centerQuotientMap (e : (G ⧸ Subgroup.center G) ≃* GriessGroup) : G →* GriessGroup :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))

theorem centerQuotientMap_surjective (e : (G ⧸ Subgroup.center G) ≃* GriessGroup) :
    Function.Surjective (centerQuotientMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem centerQuotientMap_kernel (e : (G ⧸ Subgroup.center G) ≃* GriessGroup) :
    (centerQuotientMap e).ker = Subgroup.center G := by
  ext x
  change e (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center G
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- The literal centralizing numerator above the actual local Monster subgroup. -/
def coverData (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) (hs : Function.Surjective cToLeechQuotient) :
    InvolutionCentralizerQuotientData G LeechCentralQuotient :=
  (monsterData hs).liftCentralOdd (centerQuotientMap e) (centerQuotientMap_surjective e)
    (by rwa [centerQuotientMap_kernel]) (by rw [centerQuotientMap_kernel])

theorem coverData_involution_image (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) (hs : Function.Surjective cToLeechQuotient) :
    centerQuotientMap e (coverData e ho hs).involution = griessZ :=
  (monsterData hs).liftCentralOdd_image _ _ _ _

theorem coverData_numerator (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) (hs : Function.Surjective cToLeechQuotient) :
    (coverData e ho hs).numerator = localSubgroup.comap (centerQuotientMap e) := rfl

theorem coverData_quotientMap (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) (hs : Function.Surjective cToLeechQuotient)
    (x : localSubgroup.comap (centerQuotientMap e)) :
    (coverData e ho hs).quotientMap x =
      localToLeechQuotient ⟨e (QuotientGroup.mk x.val), x.property⟩ := rfl

theorem coverData_centralizer_ne_top (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) (hs : Function.Surjective cToLeechQuotient) :
    Subgroup.centralizer ({(coverData e ho hs).involution} : Set G) ≠ ⊤ := by
  apply OddCentralLifting.centralizer_ne_top_of_image (centerQuotientMap e)
    (by rw [centerQuotientMap_kernel])
  rw [coverData_involution_image]
  exact griessZ_ne_one

/-- A.2.19's Monster exclusion, conditional only on its two concrete model
producers and the explicitly retained earlier-source rank implication. -/
theorem false_of_odd_center_of_model_inputs [Finite G]
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G)))
    (hs : Function.Surjective cToLeechQuotient)
    (hr : 3 ≤ primeRank 3 LeechCentralQuotient)
    (hsource : SimpleTwoLocalThreeRankBound G) : False := by
  let d := coverData e ho hs
  let : IsSimpleGroup LeechCentralQuotient := Atlas.Sporadic.Conway1.isSimpleGroup
  have hnoncomm : ¬ IsMulCommutative LeechCentralQuotient := by
    intro hc
    let := hc
    obtain ⟨g, h, hne⟩ := Atlas.Sporadic.Conway1.exists_mul_ne_mul
    exact hne (mul_comm g h)
  have hb := hsource (Subgroup.centralizer ({d.involution} : Set G))
    (coverData_centralizer_ne_top e ho hs)
    (Theory.GroupTheory.isTwoLocal_involution_centralizer d.involution_order)
    LeechCentralQuotient hnoncomm d.section_of_centralizer
  omega

theorem false_of_center_eq_bot_of_model_inputs [Finite G]
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup) (hz : Subgroup.center G = ⊥)
    (hs : Function.Surjective cToLeechQuotient)
    (hr : 3 ≤ primeRank 3 LeechCentralQuotient)
    (hsource : SimpleTwoLocalThreeRankBound G) : False := by
  apply false_of_odd_center_of_model_inputs e _ hs hr hsource
  rw [hz, Subgroup.card_bot]
  decide

theorem false_of_odd_primary_center_of_model_inputs [Finite G]
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (hZ : IsPGroup p (Subgroup.center G))
    (hs : Function.Surjective cToLeechQuotient)
    (hr : 3 ≤ primeRank 3 LeechCentralQuotient)
    (hsource : SimpleTwoLocalThreeRankBound G) : False := by
  apply false_of_odd_center_of_model_inputs e _ hs hr hsource
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  rw [hn]
  exact hp.pow

/-- The actual Monster local section, with the concrete surjectivity input discharged. -/
def monsterQuotientData : InvolutionCentralizerQuotientData GriessGroup LeechCentralQuotient :=
  monsterData cToLeechQuotient_surjective

@[simp] theorem monsterQuotientData_involution :
    monsterQuotientData.involution = griessZ := rfl

@[simp] theorem monsterQuotientData_numerator :
    monsterQuotientData.numerator = localSubgroup := rfl

@[simp] theorem monsterQuotientData_quotientMap :
    monsterQuotientData.quotientMap = localToLeechQuotient := rfl

/-- The quotient map retains the original Leech representative of the tensor action. -/
theorem monsterQuotientData_pullback (x : LocalC.localPullback) :
    monsterQuotientData.quotientMap (cEquivLocalSubgroup (LocalC.pullbackToC x)) =
      leechCentralProjection x.val.2 :=
  localToLeechQuotient_pullback x

/-- The actual central-cover section; no additional model map or rank premise remains. -/
def coverQuotientData (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) :
    InvolutionCentralizerQuotientData G LeechCentralQuotient :=
  coverData e ho cToLeechQuotient_surjective

theorem coverQuotientData_involution_image
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) :
    centerQuotientMap e (coverQuotientData e ho).involution = griessZ :=
  coverData_involution_image e ho cToLeechQuotient_surjective

theorem coverQuotientData_numerator
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) :
    (coverQuotientData e ho).numerator = localSubgroup.comap (centerQuotientMap e) := rfl

/-- The lifted quotient map is the literal composite with the given central quotient. -/
theorem coverQuotientData_quotientMap
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G)))
    (x : localSubgroup.comap (centerQuotientMap e)) :
    (coverQuotientData e ho).quotientMap x =
      localToLeechQuotient ⟨e (QuotientGroup.mk x.val), x.property⟩ := rfl

/-- All elements centralizing the image lift to elements centralizing the chosen involution. -/
theorem coverQuotientData_centralizer
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) :
    Subgroup.centralizer ({(coverQuotientData e ho).involution} : Set G) =
      (Subgroup.centralizer ({griessZ} : Set GriessGroup)).comap (centerQuotientMap e) := by
  rw [OddCentralLifting.centralizer_eq_comap (centerQuotientMap e)
    (by rwa [centerQuotientMap_kernel]) (by rw [centerQuotientMap_kernel])
    ((coverQuotientData e ho).involution_order ▸
      pow_orderOf_eq_one (coverQuotientData e ho).involution),
    coverQuotientData_involution_image]

theorem coverQuotientData_centralizer_ne_top
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G))) :
    Subgroup.centralizer ({(coverQuotientData e ho).involution} : Set G) ≠ ⊤ :=
  coverData_centralizer_ne_top e ho cToLeechQuotient_surjective

/-- A.2.19's Monster branch for the actual odd central cover, using earlier A.2.15(2). -/
theorem false_of_odd_center [Finite G]
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (ho : Odd (Nat.card (Subgroup.center G)))
    (hsource : SimpleTwoLocalThreeRankBound G) : False :=
  false_of_odd_center_of_model_inputs e ho cToLeechQuotient_surjective
    leechCentralQuotient_three_le_primeRank hsource

/-- The source's simple, centerless branch of the Monster exclusion. -/
theorem false_of_center_eq_bot [Finite G]
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup) (hz : Subgroup.center G = ⊥)
    (hsource : SimpleTwoLocalThreeRankBound G) : False :=
  false_of_center_eq_bot_of_model_inputs e hz cToLeechQuotient_surjective
    leechCentralQuotient_three_le_primeRank hsource

/-- The source's quasisimple branch after the odd-primary central-kernel reduction. -/
theorem false_of_odd_primary_center [Finite G]
    (e : (G ⧸ Subgroup.center G) ≃* GriessGroup)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (hZ : IsPGroup p (Subgroup.center G))
    (hsource : SimpleTwoLocalThreeRankBound G) : False :=
  false_of_odd_primary_center_of_model_inputs e p hp hZ cToLeechQuotient_surjective
    leechCentralQuotient_three_le_primeRank hsource

end CFSG.Quasithin.ChapterA.MonsterLocalObstruction
