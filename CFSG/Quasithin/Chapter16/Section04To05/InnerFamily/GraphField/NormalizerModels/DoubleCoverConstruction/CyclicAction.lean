module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.Marking
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.DoubleCoverConstruction.Normalizer
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.CyclicKernelAction

/-!
# The cyclic-four action in the actual center-C₂ normalizer

Let Q be the lifted quaternion normalizer constructed in `Normalizer`, and
E = ⟨r,z⟩. The projective displacement character identifies the image of
C_Q(E) with its kernel in the concrete projective Q₈. More precisely, the
part of C_Q(E) inside the lifted quaternion subgroup projects onto that
kernel, and adjoining E gives all of C_Q(E). The first and second
isomorphism theorems therefore identify C_Q(E)/E with this kernel.

The covering calculation makes the character surjective, so the intrinsic
matrix calculation identifies its kernel with C₄ and proves irreducibility
on the displayed E₉. Invariant subgroups of the actual residual map to
invariant subgroups of this E₉. The two-group covering kernel is disjoint
from the three-group residual, so injectivity transports irreducibility
back to G.

`sourceLocalCoverData` constructs all the covered normalizer and action
witnesses, retaining only the permitted exact E₉ residual input of
16.1.4(5) and the involution-lifting clause of I.2.2(3b). It neither assumes
`NormalizerData` nor includes the separately owned ambient residual-fixer
bound. Every quotient uses normality inside its specified numerator.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.9(2), printed p.1191, and I.2.2(3b), printed pp.409–410.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels.DoubleCoverConstruction
open Matrix.PSL3Four ExtendedCentralizer.ProjectiveFixer
open InnerFamilyNormalizer.DoubleCover
noncomputable section
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The actual marked cover displacement restricted to the projective Q₈. -/
def localCharacter (d : MarkedCover L r) (hc : Nat.card (center L) = 2) :
    InnerFamilyNormalizer.Centerless.quaternion →* center L :=
  quaternionCharacter d.cover (L.normalizerMonoidHom ⟨r, d.actor_mem⟩)
    d.compatible d.kernel_center hc

/-- The part of the lifted quaternion subgroup that fixes E pointwise. -/
def centralizingComponent (d : MarkedCover L r) (z : G) : Subgroup G :=
  componentQuaternion d ⊓ centralizer (fourGroup r z : Set G)

/-- Vanishing projective displacement is precisely centralization of E in the cover. -/
theorem componentProjection_mem_character_kernel (h : IntersectionSetup T z L g R)
    (d : MarkedCover L r) (hc : Nat.card (center L) = 2) (x : componentQuaternion d) :
    componentProjection d x ∈ (localCharacter d hc).ker ↔
      (x : G) ∈ centralizer (fourGroup r z : Set G) := by
  obtain ⟨y, hy, he⟩ := x.property
  have hx : x = ⟨(y : G), mem_map_of_mem L.subtype hy⟩ := Subtype.ext he.symm
  rw [hx, MonoidHom.mem_ker, componentProjection_apply d ⟨y, hy⟩]
  change quaternionCharacter d.cover _ _ _ hc (quaternionProjection d.cover ⟨y, hy⟩) = 1 ↔ _
  rw [quaternionCharacter_apply, Subtype.ext_iff]
  change L.normalizerMonoidHom ⟨r, d.actor_mem⟩ y * y⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one, Subtype.ext_iff]
  have hec : (y : G) ∈ centralizer (fourGroup r z : Set G) ↔
      (y : G) ∈ centralizer ({r} : Set G) := by
    constructor
    · intro hyc
      exact ((component_centralizer_four h).le ⟨y.property, hyc⟩).2
    · intro hyc
      exact ((component_centralizer_four h).ge ⟨y.property, hyc⟩).2
  rw [hec, mem_centralizer_singleton_iff]
  change r * (y : G) * r⁻¹ = (y : G) ↔ (y : G) * r = r * (y : G)
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

/-- The original projective covering restricted to the pointwise centralizer. -/
def centralizerProjection (h : IntersectionSetup T z L g R)
    (d : MarkedCover L r) (hc : Nat.card (center L) = 2) :
    centralizingComponent d z →* (localCharacter d hc).ker :=
  ((componentProjection d).comp (inclusion inf_le_left)).codRestrict _ (fun x =>
    (componentProjection_mem_character_kernel h d hc ⟨x, x.property.1⟩).mpr x.property.2)

/-- Every element of the character kernel lifts to an element centralizing E. -/
theorem centralizerProjection_surjective (h : IntersectionSetup T z L g R)
    (d : MarkedCover L r) (hc : Nat.card (center L) = 2) :
    Function.Surjective (centralizerProjection h d hc) := by
  intro b
  obtain ⟨x, hx⟩ := componentProjection_surjective d b.val
  have hxC := (componentProjection_mem_character_kernel h d hc x).mp (hx.symm ▸ b.property)
  exact ⟨⟨x, x.property, hxC⟩, Subtype.ext hx⟩

/-- The restricted covering kernel is exactly the relative intersection with E. -/
theorem centralizerProjection_kernel (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r)
    (hc : Nat.card (center L) = 2) :
    (centralizerProjection h d hc).ker =
      (fourGroup r z).subgroupOf (centralizingComponent d z) := by
  ext x
  change centralizerProjection h d hc x = 1 ↔ (x : G) ∈ fourGroup r z
  rw [Subtype.ext_iff]
  change componentProjection d ⟨x, x.property.1⟩ = 1 ↔ _
  rw [← MonoidHom.mem_ker, componentProjection_kernel h hr hr2 hout hZ d]
  rfl

/-- Adjoining E to its centralizer in the lifted component gives all of C_Q(E). -/
theorem localQuaternion_centralizer_four_eq (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r) :
    localQuaternion d z ⊓ centralizer (fourGroup r z : Set G) =
      centralizingComponent d z ⊔ fourGroup r z := by
  let : IsElementaryAbelian 2 (fourGroup r z) := (fourGroup_elementary_card h hr hr2 hout).1
  have hEE : fourGroup r z ≤ centralizer (fourGroup r z : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (componentQuaternion d : Set G) * (fourGroup r z : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _
        (componentQuaternion_normalizes_four h hr hr2 hout hZ d)]
      exact hx.1
    obtain ⟨p, hp, e, he, rfl⟩ := hp
    have hpc : p ∈ centralizer (fourGroup r z : Set G) := by
      have hh := (centralizer (fourGroup r z : Set G)).mul_mem hx.2
        (hEE ((fourGroup r z).inv_mem he))
      simpa only [mul_inv_cancel_right] using hh
    exact (centralizingComponent d z ⊔ fourGroup r z).mul_mem
      (mem_sup_left ⟨hp, hpc⟩) (mem_sup_right he)
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hEE)


/-- I.2.2(3b), through the proved displacement calculation, gives a nontrivial character. -/
theorem localCharacter_surjective (hr2 : orderOf r = 2)
    (d : MarkedCover L r) (hc : Nat.card (center L) = 2)
    (hlift : NontrivialDisplacement.InvolutionLifting d.cover) :
    Function.Surjective (localCharacter d hc) := by
  apply quaternionCharacter_surjective
  · rw [← map_pow]
    have he : (⟨r, d.actor_mem⟩ : normalizer (L : Set G)) ^ 2 = 1 :=
      Subtype.ext (hr2 ▸ pow_orderOf_eq_one r)
    rw [he, map_one]
  · exact hlift

/-- The relative quotient C_Q(E)/E is the actual projective character kernel. -/
theorem localQuaternion_centralizer_quotient (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r)
    (hc : Nat.card (center L) = 2) :
    let C := localQuaternion d z ⊓ centralizer (fourGroup r z : Set G)
    letI : ((fourGroup r z).subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer
        (inf_le_left.trans (localQuaternion_normalizes_four h hr hr2 hout hZ d))
    Nonempty ((C ⧸ (fourGroup r z).subgroupOf C) ≃* (localCharacter d hc).ker) := by
  let : ((fourGroup r z).subgroupOf
      (localQuaternion d z ⊓ centralizer (fourGroup r z : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer
      (inf_le_left.trans (localQuaternion_normalizes_four h hr hr2 hout hZ d))
  let hPN : centralizingComponent d z ≤ normalizer (fourGroup r z : Set G) :=
    inf_le_right.trans (centralizer_le_normalizer _)
  let : ((fourGroup r z).subgroupOf (centralizingComponent d z)).Normal :=
    normal_subgroupOf_of_le_normalizer hPN
  let : ((fourGroup r z).subgroupOf (centralizingComponent d z ⊔ fourGroup r z)).Normal :=
    normal_subgroupOf_sup_of_le_normalizer hPN
  let eC := QuotientGroup.equivQuotientSubgroupOfOfEq (rfl : fourGroup r z = fourGroup r z)
    (localQuaternion_centralizer_four_eq h hr hr2 hout hZ d)
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient
    (centralizingComponent d z) (fourGroup r z) hPN
  exact ⟨eC.trans (e.symm.trans ((QuotientGroup.quotientMulEquivOfEq
    (centralizerProjection_kernel h hr hr2 hout hZ d hc).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (centralizerProjection h d hc)
        (centralizerProjection_surjective h d hc))))⟩

/-- The centralizer quotient in the original ambient group is cyclic of order four. -/
theorem localQuaternion_cyclic_four (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r)
    (hc : Nat.card (center L) = 2)
    (hlift : NontrivialDisplacement.InvolutionLifting d.cover) :
    let C := localQuaternion d z ⊓ centralizer (fourGroup r z : Set G)
    letI : ((fourGroup r z).subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer
        (inf_le_left.trans (localQuaternion_normalizes_four h hr hr2 hout hZ d))
    Nonempty ((C ⧸ (fourGroup r z).subgroupOf C) ≃* Multiplicative (ZMod 4)) := by
  let : ((fourGroup r z).subgroupOf
      (localQuaternion d z ⊓ centralizer (fourGroup r z : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer
      (inf_le_left.trans (localQuaternion_normalizes_four h hr hr2 hout hZ d))
  obtain ⟨e⟩ := localQuaternion_centralizer_quotient h hr hr2 hout hZ d hc
  obtain ⟨f⟩ := CyclicKernelAction.kernel_equiv (localCharacter d hc) hc
    (localCharacter_surjective hr2 d hc hlift)
  exact ⟨e.trans f⟩


omit [Finite G] in
/-- The quaternion projection retains the original covering map on each element. -/
theorem componentProjection_coe (d : MarkedCover L r) (x : componentQuaternion d) :
    (componentProjection d x : PSL) =
      d.cover.toMonoidHom ⟨x, componentQuaternion_le_component d x.property⟩ := by
  obtain ⟨y, hy, he⟩ := x.property
  have hx : x = ⟨(y : G), mem_map_of_mem L.subtype hy⟩ := Subtype.ext he.symm
  subst x
  rw [componentProjection_apply d ⟨y, hy⟩]
  rfl

/-- Actual ambient invariance transports to matrix conjugation by the character kernel. -/
theorem character_kernel_normalizes_image (h : IntersectionSetup T z L g R)
    (d : MarkedCover L r) (hc : Nat.card (center L) = 2)
    (A : Subgroup G) (hAL : A ≤ L)
    (hN : localQuaternion d z ⊓ centralizer (fourGroup r z : Set G) ≤ normalizer (A : Set G)) :
    (localCharacter d hc).ker.map InnerFamilyNormalizer.Centerless.quaternion.subtype ≤
      normalizer (((A.subgroupOf L).map d.cover.toMonoidHom : Subgroup PSL) : Set PSL) := by
  rintro b ⟨b, hb, rfl⟩
  obtain ⟨x, hx⟩ := componentProjection_surjective d b
  have hxC := (componentProjection_mem_character_kernel h d hc x).mp (hx.symm ▸ hb)
  have hn : (⟨x, componentQuaternion_le_component d x.property⟩ : L) ∈
      normalizer (A.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq hAL]
    exact hN ⟨mem_sup_left x.property, hxC⟩
  have hh := (A.subgroupOf L).le_normalizer_map d.cover.toMonoidHom
    (mem_map_of_mem d.cover.toMonoidHom hn)
  rw [← componentProjection_coe d x, hx] at hh
  exact hh

/-- The actual centralizer C_Q(E) acts irreducibly on the source residual. -/
theorem localQuaternion_irreducible (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (d : MarkedCover L r) (hc : Nat.card (center L) = 2)
    (hlift : NontrivialDisplacement.InvolutionLifting d.cover)
    (hD : IsElementaryAbelian 3 (residual L r))
    (A : Subgroup G) (hA : A ≤ residual L r)
    (hN : localQuaternion d z ⊓ centralizer (fourGroup r z : Set G) ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = residual L r := by
  have hDL : residual L r ≤ L := (residual_le_centralizer L r).trans inf_le_left
  let DL := (residual L r).subgroupOf L
  let := hD
  have h3 : IsPGroup 3 DL :=
    (IsElementaryAbelian.isPGroup 3 (residual L r)).of_equiv
      (subgroupOfEquivOfLe hDL).symm
  have hinj := InnerFamilyNormalizer.projection_injective d.cover.toMonoidHom d.kernel_two DL h3
  have hAm : (A.subgroupOf L).map d.cover.toMonoidHom ≤ model := by
    rw [← d.residual_image]
    exact map_mono (comap_mono hA)
  rcases CyclicKernelAction.kernel_irreducible (localCharacter d hc) hc
    (localCharacter_surjective hr2 d hc hlift) _ hAm
    (character_kernel_normalizes_image h d hc A (hA.trans hDL) hN) with hbot | htop
  · left
    apply bot_unique
    intro x hx
    let xL : L := ⟨x, hDL (hA hx)⟩
    have hxmap : d.cover.toMonoidHom xL ∈ (A.subgroupOf L).map d.cover.toMonoidHom :=
      mem_map_of_mem d.cover.toMonoidHom hx
    rw [hbot] at hxmap
    have he : (⟨xL, hA hx⟩ : DL) = 1 := hinj (by
      change d.cover.toMonoidHom xL = d.cover.toMonoidHom 1
      rw [map_one]
      exact mem_bot.mp hxmap)
    exact congrArg (fun y : DL => ((y : L) : G)) he
  · right
    apply le_antisymm hA
    intro x hx
    let xL : L := ⟨x, hDL hx⟩
    have hxmap : d.cover.toMonoidHom xL ∈ (A.subgroupOf L).map d.cover.toMonoidHom := by
      rw [htop, ← d.residual_image]
      exact mem_map_of_mem d.cover.toMonoidHom hx
    obtain ⟨y, hy, he⟩ := hxmap
    have hyx : (⟨y, hA hy⟩ : DL) = ⟨xL, hx⟩ := hinj he
    have heG : (y : G) = x := congrArg (fun w : DL => ((w : L) : G)) hyx
    exact heG ▸ hy


/-- The full covered normalizer and action witnesses, without the independently
proved ambient residual-fixer bound. -/
structure LocalCoverData (L : Subgroup G) (r z : G) extends LocalNormalizerData L r z where
  cyclic_four :
    let C := Q ⊓ centralizer (fourGroup r z : Set G)
    letI : ((fourGroup r z).subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer (inf_le_left.trans normalizes_four)
    Nonempty ((C ⧸ (fourGroup r z).subgroupOf C) ≃* Multiplicative (ZMod 4))
  irreducible : ∀ A : Subgroup G, A ≤ residual L r →
    Q ⊓ centralizer (fourGroup r z : Set G) ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = residual L r

/-- Construct all covered witnesses from the original compatible marking. -/
def localCoverData (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hZ : (center L).map L.subtype = zpowers z) (d : MarkedCover L r)
    (hc : Nat.card (center L) = 2)
    (hlift : NontrivialDisplacement.InvolutionLifting d.cover)
    (hD : IsElementaryAbelian 3 (residual L r)) : LocalCoverData L r z where
  toLocalNormalizerData := localNormalizerData h hr hr2 hout hZ d hc hlift
  cyclic_four := localQuaternion_cyclic_four h hr hr2 hout hZ d hc hlift
  irreducible := localQuaternion_irreducible h hr2 d hc hlift hD

/-- Source 16.4.9(2)'s actual center-C₂ normalizer and cyclic-four action.
Only the exact earlier E₉ residual and I.2.2(3b) involution-lifting inputs
remain explicit. Neither a normalizer witness nor an action conclusion is assumed. -/
def sourceLocalCoverData {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z) (hcore : pCore 2 L ≠ ⊥)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hlift : NontrivialDisplacement.InvolutionLifting (markedCover hG h hmodel hD h9).cover) :
    LocalCoverData L r z := by
  have hcenter := hG.evenType.component_center_eq_twoCore h.involution h.component
  exact localCoverData h hr hr2 hout
    (center_eq_zpowers_of_nontrivial_core h hTC hcenter hcore) (markedCover hG h hmodel hD h9)
    (center_card_two h hTC hcenter hcore) hlift hD

end
end CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels.DoubleCoverConstruction
