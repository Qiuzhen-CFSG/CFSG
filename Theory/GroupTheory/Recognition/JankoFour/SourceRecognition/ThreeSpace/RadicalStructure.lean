module

public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CentralCover
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PairAction
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.PCoreCoverEquiv
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The special radical and symmetric-five quotient of the source three-space

The simultaneous centralizer of two source points normalizes Z because it
preserves the full cubic lift generating Z. Its original quotient map has
kernel of order 2¹² and image of shape E₃₂.S₅. The two-point fixer in the
full K-action has order four, so the pair two-core has order 2¹⁷ and its
kernel R has order 2¹⁵. This also identifies R with O₂(S) and gives the
literal quotient S/R ≃ S₅.

Every two point-core centralizers now generate all of R. Their extraspecial
quotients put every square and commutator in the original triple intersection
Z. The large centralizers are nonabelian, so each point of Z is an actual
commutator. Maximal elementary intersections in the two extraspecial cores
force Z(R)=Z; the elementary quotient then gives Φ(R)=R′=Z.

All the data are constructed from IsTypeJ4. No splitting, point-group geometry,
ambient recognition or tensor-module identification is assumed.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
The tensor-action clause of (4.4) is not asserted by this module.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
private theorem extraspecial_comm_mem {G : Type*} [Group G]
    (Q : Subgroup G) [IsExtraspecial 2 Q] {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    ⁅a,b⁆ ∈ (center Q).map Q.subtype := by
  exact ⟨⁅(⟨a,ha⟩ : Q),(⟨b,hb⟩ : Q)⁆,
    (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _)),rfl⟩

private theorem central_product_mem_inf {G : Type*} [Group G]
    (Q P : Subgroup G) [IsExtraspecial 2 Q] [IsExtraspecial 2 P]
    (hQ : Subgroup.centralizer ((Q ⊓ P).subgroupOf Q : Set Q) = (Q ⊓ P).subgroupOf Q)
    (hP : Subgroup.centralizer ((Q ⊓ P).subgroupOf P : Set P) = (Q ⊓ P).subgroupOf P)
    (hd : Disjoint ((center Q).map Q.subtype) ((center P).map P.subtype))
    {a b : G} (ha : a ∈ Q) (hb : b ∈ P)
    (hab : a*b ∈ Subgroup.centralizer (Q ⊓ P : Set G)) : a*b ∈ Q ⊓ P := by
  have hc (v : G) (hv : v ∈ Q ⊓ P) : ⁅a⁻¹,v⁆ = 1 ∧ ⁅b,v⁆ = 1 := by
    have hh := hab v hv
    have he : a⁻¹*v*a = b*v*b⁻¹ := by
      calc
        a⁻¹*v*a = a⁻¹*(v*(a*b))*b⁻¹ := by group
        _ = a⁻¹*((a*b)*v)*b⁻¹ := by rw [hh]
        _ = b*v*b⁻¹ := by group
    have he' : ⁅a⁻¹,v⁆ = ⁅b,v⁆ := by
      simpa only [commutatorElement_def,inv_inv,mul_assoc] using congrArg (fun x => x*v⁻¹) he
    have haC := extraspecial_comm_mem Q (Q.inv_mem ha) hv.1
    have hbC := extraspecial_comm_mem P hb hv.2
    have hzero : ⁅a⁻¹,v⁆ = 1 := (Subgroup.disjoint_def.mp hd) haC (he' ▸ hbC)
    exact ⟨hzero,he'.symm.trans hzero⟩
  have haT : a⁻¹ ∈ Q ⊓ P := by
    have hh : (⟨a,ha⟩ : Q)⁻¹ ∈ Subgroup.centralizer ((Q ⊓ P).subgroupOf Q : Set Q) := by
      intro v hv
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp (hc v hv).1).symm
    rw [hQ] at hh
    exact hh
  have hbT : b ∈ Q ⊓ P := by
    have hh : (⟨b,hb⟩ : P) ∈ Subgroup.centralizer ((Q ⊓ P).subgroupOf P : Set P) := by
      intro v hv
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp (hc v hv).2).symm
    rw [hP] at hh
    exact hh
  exact (Q ⊓ P).mul_mem (by simpa only [inv_inv] using (Q ⊓ P).inv_mem haT) hbT

namespace ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

private theorem z_in_space : z ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)
private theorem r_in_space : d.r ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)
private theorem z_ne_one (h : IsTypeJ4 z) : z ≠ 1 := by
  intro he
  have hi := h.involution
  simp [he] at hi
private theorem r_ne_one (h : IsTypeJ4 z) : d.r ≠ 1 := by
  intro he
  exact z_ne_one h (isConj_one_left.mp (he ▸ d.r_conj))

def pairCentralizer : Subgroup G := centralizer z ⊓ centralizer d.r

theorem S_le_pairCentralizer : d.S ≤ d.pairCentralizer :=
  le_inf (d.S_le_point_centralizer d.z_in_space)
    (d.S_le_point_centralizer d.r_in_space)

/-- Fixing the two marked points preserves their cubic-generated three-space. -/
theorem pairCentralizer_le_normalizer (h : IsTypeJ4 z) :
    d.pairCentralizer ≤ normalizer (d.space : Set G) := by
  let U := (cubicSylowImage e X).map (centralizer z).subtype
  let D := (LocalGeometry.CubicLift.subgroup e).map (centralizer z).subtype
  have hD : D = ambientCore z ⊔ U := by
    change (LocalGeometry.CubicLift.subgroup e).map (centralizer z).subtype = _
    rw [← core_sup_cubicSylow e h X, Subgroup.map_sup]
    rfl
  have hDN : D ≤ normalizer (d.space : Set G) := by
    rw [hD]
    exact sup_le (d.cores_normalize z d.z_in_space (z_ne_one h)) d.cubic_normalizes
  have hUD : U ≤ D := hD ▸ le_sup_right
  intro g hg
  have hDg : g ∈ normalizer (D : Set G) := by
    exact ((LocalGeometry.CubicLift.subgroup e).le_normalizer_map
      (centralizer z).subtype) (by
        exact ⟨⟨g,hg.1⟩, by simp only [Subgroup.normalizer_eq_top]; exact mem_top _,rfl⟩)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj g).injective])
  have hz : MulAut.conj g z = z := by
    change g*z*g⁻¹=z
    rw [mem_centralizer_singleton_iff.mp hg.1,mul_inv_cancel_right]
  have hr : MulAut.conj g d.r = d.r := by
    change g*d.r*g⁻¹=d.r
    rw [mem_centralizer_singleton_iff.mp hg.2,mul_inv_cancel_right]
  have hUg : U.map (MulAut.conj g).toMonoidHom ≤ D := by
    exact (map_mono hUD).trans_eq (mem_normalizer_iff_map_conj_eq.mp hDg)
  change (d.space.map (MulAut.conj g).toMonoidHom) ≤ d.space
  conv_lhs => rw [show d.space = zpowers z ⊔ ⁅zpowers d.r,U⁆ from d.cubic_commutator,
    Subgroup.map_sup,Subgroup.map_commutator,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  change zpowers (MulAut.conj g z) ⊔ ⁅zpowers (MulAut.conj g d.r),_⁆ ≤ _
  rw [hz,hr]
  apply sup_le (zpowers_le.mpr d.z_in_space)
  exact (commutator_mono (zpowers_le.mpr d.r_in_space) (hUg.trans hDN)).trans
    (le_normalizer_iff_commutator_le_left.mp le_rfl)

/-- Relative normality of the literal centralizer inside the marked pair group. -/
theorem S_normal_in_pairCentralizer (h : IsTypeJ4 z) :
    (d.S.subgroupOf d.pairCentralizer).Normal :=
  (normal_subgroupOf_iff_le_normalizer d.S_le_pairCentralizer).mpr
    ((d.pairCentralizer_le_normalizer h).trans d.S_normalized)

/-- The marked returning point in the original point-centralizer. -/
def rInCentralizer : centralizer z := ⟨d.r,LocalGeometry.ambientCore_le z d.r_mem⟩

def rInCore : core z := ⟨d.rInCentralizer,by
  obtain ⟨q,hq,he⟩ := d.r_mem
  exact (show q = d.rInCentralizer from Subtype.ext he) ▸ hq⟩

/-- The original quotient image of the simultaneous centralizer. -/
def pairImage : Subgroup (centralizer z ⧸ core z) :=
  (Subgroup.centralizer ({d.rInCentralizer} : Set (centralizer z))).map
    (QuotientGroup.mk' (core z))

/-- Restriction of the original map H → H/Q, with its actual image. -/
def pairProjection : d.pairCentralizer →* d.pairImage :=
  ((QuotientGroup.mk' (core z)).comp (inclusion (show d.pairCentralizer ≤ centralizer z from inf_le_left))).codRestrict
    d.pairImage (fun a => by
      refine ⟨⟨a.val,a.property.1⟩,?_,rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp a.property.2)))

theorem pairProjection_surjective : Function.Surjective d.pairProjection := by
  rintro ⟨b,a,ha,rfl⟩
  refine ⟨⟨a.val,a.property,?_⟩,rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))

/-- Every element of the pair two-core is in the original seven-core join. -/
theorem pair_twoCore_le_K (h : IsTypeJ4 z) : d.pairCentralizer.pCoreIn 2 ≤ d.K := by
  have hc : (pCore 2 d.pairCentralizer).map d.pairProjection ≤ pCore 2 d.pairImage :=
    le_sSup ⟨(inferInstance : (pCore 2 d.pairCentralizer).Normal).map _
      d.pairProjection_surjective,pCore_isPGroup.map _⟩
  let := h.extraspecial
  have hret := returningImage_eq_twoCore h d.rInCore d.r_conj d.r_ne
  change (returningImage z d.r).subgroupOf d.pairImage = pCore 2 d.pairImage at hret
  have hQK : ambientCore z ≤ d.K :=
    core_le_threeSpaceCores d.space d.z_in_space (z_ne_one h)
  have hRK : ambientCore d.r ≤ d.K :=
    core_le_threeSpaceCores d.space d.r_in_space (d.r_ne_one h)
  rintro x ⟨x,hx,rfl⟩
  have him := hc (mem_map_of_mem d.pairProjection hx)
  rw [← hret] at him
  change QuotientGroup.mk' (core z) (⟨x.val,x.property.1⟩ : centralizer z) ∈
    returningImage z d.r at him
  obtain ⟨y,hy,he⟩ := him
  have hxy : (⟨x.val,x.property.1⟩ : centralizer z) * y⁻¹ ∈ core z := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (core z) ((⟨x.val,x.property.1⟩ : centralizer z) * y⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hxyK : x.val * (y : G)⁻¹ ∈ d.K := hQK (mem_map_of_mem (centralizer z).subtype hxy)
  simpa only [Subgroup.subtype_apply,inv_mul_cancel_right] using d.K.mul_mem hxyK (hRK hy)

/-- AS91 (4.4): the two-core of the three-space centralizer is the literal R. -/
theorem R_eq_S_twoCore (h : IsTypeJ4 z) : d.R = d.S.pCoreIn 2 := by
  apply le_antisymm
  · apply le_pCoreIn_of_normalizes
    · rw [d.R_eq_K_twoCore h]
      exact isPGroup_pCoreIn 2 d.K
    · exact inf_le_right
    · apply (le_inf ?_ d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf
      exact ((centralizer_le_normalizer _).trans
        ((normal_subgroupOf_iff_le_normalizer d.K_le_normalizer).mp d.K_normal))
  · apply le_inf ?_ (pCoreIn_le 2 d.S)
    exact (pCoreIn_mono_of_normalizes d.S_le_pairCentralizer
      ((d.pairCentralizer_le_normalizer h).trans d.S_normalized)).trans (d.pair_twoCore_le_K h)

private theorem rInCore_noncentral (h : IsTypeJ4 z) : d.rInCore ∉ center (core z) := by
  intro hc
  have hm : d.r ∈ zpowers z := by
    rw [← LocalGeometry.core_center_image h]
    exact mem_map_of_mem _ (mem_map_of_mem _ hc)
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : zpowers z)).mp
    ((Nat.card_zpowers z).trans h.involution)
  exact d.r_ne (congrArg Subtype.val ((hw ⟨_,hm⟩
    (fun he => d.r_ne_one h (congrArg Subtype.val he))).trans
      (hw ⟨z,mem_zpowers z⟩ (fun he => z_ne_one h (congrArg Subtype.val he))).symm))

theorem pairImage_structure (h : IsTypeJ4 z) :
    Nat.card d.pairImage = 3840 ∧ Nat.card (pCore 2 d.pairImage) = 32 ∧
      Nonempty ((d.pairImage ⧸ pCore 2 d.pairImage) ≃* Equiv.Perm (Fin 5)) := by
  let := h.extraspecial
  have hc := coreVectorStabilizer_card_four h e X d.rInCore
    (returning_label_four h e X d.rInCore d.r_conj d.r_ne)
  rw [coreVectorStabilizer_eq_centralizer_image h d.rInCore (d.rInCore_noncentral h)] at hc
  exact ⟨hc,(coreCentralizerImage_structure_of_card h e d.rInCore
    (d.rInCore_noncentral h) hc).2⟩

theorem pairProjection_ker : d.pairProjection.ker =
    (ambientCore z).subgroupOf d.pairCentralizer := by
  ext x
  change (⟨QuotientGroup.mk' (core z) ⟨x.val,x.property.1⟩,_⟩ : d.pairImage) = 1 ↔ _
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (core z) (⟨x.val,x.property.1⟩ : centralizer z) = 1 ↔ _
  constructor
  · intro hx
    exact mem_map_of_mem (centralizer z).subtype ((QuotientGroup.eq_one_iff _).mp hx)
  · rintro ⟨q,hq,he⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (show q = ⟨x.val,x.property.1⟩ from Subtype.ext he) ▸ hq

theorem pairProjection_kernel_isTwoGroup (h : IsTypeJ4 z) : IsPGroup 2 d.pairProjection.ker := by
  rw [d.pairProjection_ker]
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient z) h.extraspecial
  exact (IsExtraspecial.isPGroup 2 (ambientCore z)).comap_subtype

theorem pairProjection_kernel_card (h : IsTypeJ4 z) : Nat.card d.pairProjection.ker = 4096 := by
  let := h.extraspecial
  let C := Subgroup.centralizer ({d.rInCore} : Set (core z))
  have hc : Nat.card C = 4096 := by
    have he := C.card_mul_index
    rw [ExtraspecialIntersection.centralizer_index_two d.rInCore (d.rInCore_noncentral h),h.core_card] at he
    omega
  let f : C →* d.pairProjection.ker :=
    { toFun := fun q => ⟨⟨((q : core z) : centralizer z),
        ((q : core z) : centralizer z).property,
        mem_centralizer_singleton_iff.mpr (congrArg (fun x : core z => ((x : centralizer z) : G))
          (mem_centralizer_singleton_iff.mp q.property))⟩,by
          rw [d.pairProjection_ker]
          exact mem_map_of_mem _ (q : core z).property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun x : d.pairProjection.ker => ((x : d.pairCentralizer) : G)) hab)))
    · rintro ⟨x,hx⟩
      rw [d.pairProjection_ker] at hx
      obtain ⟨q,hq,he⟩ := hx
      let q₀ : core z := ⟨q,hq⟩
      have hqC : q₀ ∈ C := by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        apply Subtype.ext
        change (q : G)*d.r = d.r*(q : G)
        change (q : G) = (x : G) at he
        rw [he]
        exact mem_centralizer_singleton_iff.mp x.property.2
      exact ⟨⟨q₀,hqC⟩,Subtype.ext (Subtype.ext he)⟩
  exact (Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv).symm.trans hc

theorem pair_twoCore_card (h : IsTypeJ4 z) : Nat.card (d.pairCentralizer.pCoreIn 2) = 131072 := by
  rw [pCoreIn,card_map_of_injective d.pairCentralizer.subtype_injective,
    d.pairProjection.card_pCore_of_ker_isPGroup d.pairProjection_surjective
      (d.pairProjection_kernel_isTwoGroup h), d.pairProjection_kernel_card h,
    (d.pairImage_structure h).2.1]

/-- The pair centralizer has its original S₅ quotient after removing its two-core. -/
theorem pair_quotient_symmetricFive (h : IsTypeJ4 z) :
    Nonempty ((d.pairCentralizer ⧸ pCore 2 d.pairCentralizer) ≃* Equiv.Perm (Fin 5)) :=
  ⟨(d.pairProjection.quotientPCoreEquivOfSurjective d.pairProjection_surjective
    (d.pairProjection_kernel_isTwoGroup h)).trans (d.pairImage_structure h).2.2.some⟩

private def pairFixer : Subgroup (MulAut d.space) :=
  MulAction.stabilizer (MulAut d.space) (⟨z,d.z_in_space⟩ : d.space) ⊓
    MulAction.stabilizer (MulAut d.space) (⟨d.r,d.r_in_space⟩ : d.space)

private theorem pairFixer_card (h : IsTypeJ4 z) : Nat.card d.pairFixer = 4 := by
  let := d.elementary
  exact elementaryEight_pairFixer_card d.card _ _
    (fun he => z_ne_one h (congrArg Subtype.val he))
    (fun he => d.r_ne_one h (congrArg Subtype.val he))
    (fun he => d.r_ne (congrArg Subtype.val he).symm)

private def pairKAction : (d.K ⊓ d.pairCentralizer : Subgroup G) →* d.pairFixer :=
  (d.KAction.comp (inclusion inf_le_left)).codRestrict _ (fun k => by
    constructor
    · apply Subtype.ext
      change k.val*z*k.val⁻¹=z
      rw [mem_centralizer_singleton_iff.mp k.property.2.1,mul_inv_cancel_right]
    · apply Subtype.ext
      change k.val*d.r*k.val⁻¹=d.r
      rw [mem_centralizer_singleton_iff.mp k.property.2.2,mul_inv_cancel_right])

private theorem pairKAction_surjective (h : IsTypeJ4 z) : Function.Surjective d.pairKAction := by
  intro a
  obtain ⟨k,hk⟩ := d.KAction_surjective h a.val
  have hfix (t : G) (ht : t ∈ d.space) (ha : a.val ⟨t,ht⟩ = ⟨t,ht⟩) :
      k.val ∈ centralizer t := by
    have he := congrArg (fun f : MulAut d.space => (f ⟨t,ht⟩ : G)) hk
    change k.val*t*k.val⁻¹ = (a.val ⟨t,ht⟩ : G) at he
    rw [ha] at he
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  exact ⟨⟨k.val,k.property,hfix z _ a.property.1,hfix d.r _ a.property.2⟩,Subtype.ext hk⟩

private theorem pairKAction_ker : d.pairKAction.ker =
    d.R.subgroupOf (d.K ⊓ d.pairCentralizer) := by
  ext k
  change (⟨d.KAction ⟨k.val,k.property.1⟩,_⟩ : d.pairFixer) = 1 ↔ _
  rw [Subtype.ext_iff]
  change d.KAction (⟨k.val,k.property.1⟩ : d.K) = 1 ↔ _
  change (⟨k.val,k.property.1⟩ : d.K) ∈ d.KAction.ker ↔ _
  rw [d.KAction_ker]
  rfl

private theorem R_le_pairK : d.R ≤ d.K ⊓ d.pairCentralizer :=
  le_inf inf_le_left (inf_le_right.trans d.S_le_pairCentralizer)

/-- The pair stabilizer inside K is exactly the two-core of the full pair centralizer. -/
theorem pair_twoCore_eq_K_inf (h : IsTypeJ4 z) :
    d.pairCentralizer.pCoreIn 2 = d.K ⊓ d.pairCentralizer := by
  apply le_antisymm (le_inf (d.pair_twoCore_le_K h) (pCoreIn_le _ _))
  have hR : IsPGroup 2 d.R := by
    rw [d.R_eq_K_twoCore h]
    exact isPGroup_pCoreIn 2 d.K
  have hk : IsPGroup 2 d.pairKAction.ker := by
    rw [d.pairKAction_ker]
    exact hR.comap_subtype
  have hA : IsPGroup 2 d.pairFixer := IsPGroup.of_card (n := 2) (d.pairFixer_card h)
  have hKA : IsPGroup 2 (d.K ⊓ d.pairCentralizer : Subgroup G) := by
    have hp := (hA.to_subgroup ⊤).comap_of_ker_isPGroup d.pairKAction hk
    rw [comap_top] at hp
    exact hp.of_equiv topEquiv
  apply le_pCoreIn_of_normalizes hKA inf_le_right
  apply (le_inf ?_ d.pairCentralizer.le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact (d.pairCentralizer_le_normalizer h).trans
    ((normal_subgroupOf_iff_le_normalizer d.K_le_normalizer).mp d.K_normal)

/-- AS91 (4.4): the literal radical has order 2¹⁵. -/
theorem R_card (h : IsTypeJ4 z) : Nat.card d.R = 32768 := by
  have hc := d.pairKAction.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (d.pairKAction_surjective h),card_top,
    d.pairFixer_card h,d.pairKAction_ker,
    Nat.card_congr (subgroupOfEquivOfLe d.R_le_pairK).toEquiv,
    ← d.pair_twoCore_eq_K_inf h,d.pair_twoCore_card h] at hc
  omega

/-- The order-2¹⁵ core-centralizer join is the entire radical. -/
theorem R_eq_coreCentralizerJoin (h : IsTypeJ4 z) : d.R = d.coreCentralizerJoin := by
  symm
  apply eq_of_le_of_card_ge (d.coreCentralizerJoin_le_R h)
  rw [d.R_card h,d.coreCentralizerJoin_card h]

theorem S_twoCore_quotient_symmetricFive (h : IsTypeJ4 z) :
    Nonempty ((d.S ⧸ pCore 2 d.S) ≃* Equiv.Perm (Fin 5)) := by
  have hcover : (d.pairCentralizer : Set G) ⊆
      (d.S : Set G) * (d.pairCentralizer.pCoreIn 2 : Set G) := by
    intro p hp
    obtain ⟨k,hk,s,hs,he⟩ := d.normalizer_product h p⁻¹
      ((d.pairCentralizer_le_normalizer h) (d.pairCentralizer.inv_mem hp))
    have hkP : k ∈ d.pairCentralizer := by
      have hm := d.pairCentralizer.mul_mem (d.pairCentralizer.inv_mem hp)
        (d.pairCentralizer.inv_mem (d.S_le_pairCentralizer hs))
      rwa [←he,mul_inv_cancel_right] at hm
    refine ⟨s⁻¹,d.S.inv_mem hs,k⁻¹,?_,?_⟩
    · rw [d.pair_twoCore_eq_K_inf h]
      exact ⟨d.K.inv_mem hk,d.pairCentralizer.inv_mem hkP⟩
    · change s⁻¹*k⁻¹=p
      rw [←mul_inv_rev,he,inv_inv]
  obtain ⟨a,_⟩ := Subgroup.exists_pCoreQuotientEquiv_of_cover
    (p := 2) d.S_le_pairCentralizer hcover
  exact ⟨a.trans (d.pair_quotient_symmetricFive h).some⟩

/-- Normality for the literal quotient S/R. -/
theorem R_normal_in_S (h : IsTypeJ4 z) : (d.R.subgroupOf d.S).Normal := by
  rw [d.R_eq_S_twoCore h,pCoreIn,← comap_subtype,comap_map_eq_self_of_injective d.S.subtype_injective]
  infer_instance

/-- AS91 (4.4): S/R is the actual symmetric group on five letters. -/
theorem S_quotient_symmetricFive (h : IsTypeJ4 z) :
    letI := d.R_normal_in_S h
    Nonempty ((d.S ⧸ d.R.subgroupOf d.S) ≃* Equiv.Perm (Fin 5)) := by
  let := d.R_normal_in_S h
  have he : d.R.subgroupOf d.S = pCore 2 d.S := by
    rw [d.R_eq_S_twoCore h,pCoreIn,← comap_subtype,comap_map_eq_self_of_injective d.S.subtype_injective]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq he).trans
    (d.S_twoCore_quotient_symmetricFive h).some⟩

private theorem s_in_space : d.s ∈ d.space := by
  rw [space,d.generated]
  exact subset_closure (by simp)
private theorem s_ne_one (h : IsTypeJ4 z) : d.s ≠ 1 := by
  intro he
  exact z_ne_one h (isConj_one_left.mp (he ▸ d.s_conj))

/-- Every pair of distinct source points generates R through its core centralizers. -/
theorem R_eq_pointCore_join (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    d.R = (ambientCore t ⊓ d.S) ⊔ (ambientCore u ⊓ d.S) := by
  have htuConj : IsConj t u := by
    obtain ⟨a,_,ha⟩ := d.normalizer_transitive t ht ht1
    obtain ⟨b,_,hb⟩ := d.normalizer_transitive u hu hu1
    exact (isConj_iff.mpr ⟨a,ha⟩).symm.trans (isConj_iff.mpr ⟨b,hb⟩)
  have huQt := d.contained_in_cores t ht ht1 hu
  let := returningIntersection_elementary (d.point_type h ht ht1) htuConj (Ne.symm htu)
  have hTS : ambientCore t ⊓ ambientCore u ≤ d.S := by
    intro x hx y hy
    let xT : (ambientCore t ⊓ ambientCore u : Subgroup G) := ⟨x,hx⟩
    let yT : (ambientCore t ⊓ ambientCore u : Subgroup G) :=
      ⟨y,d.contained_in_cores t ht ht1 hy,d.contained_in_cores u hu hu1 hy⟩
    exact congrArg Subtype.val (mul_comm yT xT)
  have hi : (ambientCore t ⊓ d.S) ⊓ (ambientCore u ⊓ d.S) =
      ambientCore t ⊓ ambientCore u := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · exact le_inf (le_inf inf_le_left hTS) (le_inf inf_le_right hTS)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (ambientCore t ⊓ d.S) (ambientCore u ⊓ d.S)
    (inf_le_right.trans (d.coreCentralizer_normalized h ht ht1))
  rw [d.coreCentralizer_card h ht ht1,d.coreCentralizer_card h hu hu1,hi,
    (returning_intersection_image_orders (d.point_type h ht ht1) htuConj huQt (Ne.symm htu)).1] at hc
  symm
  apply eq_of_le_of_card_ge
    (sup_le (d.coreCentralizer_le_R ht ht1) (d.coreCentralizer_le_R hu hu1))
  rw [d.R_card h]
  omega

private theorem pointCore_commutator (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    ⁅ambientCore t,ambientCore t⁆ = zpowers t := by
  let ht' := d.point_type h ht ht1
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient t) ht'.extraspecial
  rw [←map_subtype_commutator,IsExtraspecial.commutator_eq_center (p := 2),
    LocalGeometry.ambientCore_center_image ht']

private theorem R_commutator_le_pointCore (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    ⁅d.R,d.R⁆ ≤ ambientCore t := by
  have hn : d.S ≤ normalizer (ambientCore t : Set G) := by
    rw [LocalGeometry.normalizer_ambientCore (d.point_type h ht ht1)]
    exact d.S_le_point_centralizer ht
  have hAB : ⁅ambientCore t ⊓ d.S,ambientCore u ⊓ d.S⁆ ≤ ambientCore t :=
    (commutator_mono inf_le_left inf_le_right).trans
      (le_normalizer_iff_commutator_le_left.mp hn)
  have hBB : ⁅ambientCore u ⊓ d.S,ambientCore u ⊓ d.S⁆ ≤ ambientCore t :=
    (commutator_mono inf_le_left inf_le_left).trans
      ((d.pointCore_commutator h hu hu1).le.trans
        (zpowers_le.mpr (d.contained_in_cores t ht ht1 hu)))
  have hBR : ⁅ambientCore u ⊓ d.S,d.R⁆ ≤ ambientCore t := by
    rw [commutator_comm]
    calc
      ⁅d.R,ambientCore u ⊓ d.S⁆ =
          ⁅(ambientCore t ⊓ d.S) ⊔ (ambientCore u ⊓ d.S),ambientCore u ⊓ d.S⁆ :=
        congrArg (fun B : Subgroup G => ⁅B,ambientCore u ⊓ d.S⁆)
          (d.R_eq_pointCore_join h ht hu ht1 hu1 htu)
      _ ≤ ambientCore t := commutator_sup_le_of_relative_normal d.S _ _ _ _ hn
        inf_le_right inf_le_right hAB hBB
  have hAR : ⁅ambientCore t ⊓ d.S,d.R⁆ ≤ ambientCore t :=
    (commutator_mono inf_le_left (show d.R ≤ d.S from inf_le_right)).trans
      (le_normalizer_iff_commutator_le_left.mp hn)
  calc
    ⁅d.R,d.R⁆ = ⁅(ambientCore t ⊓ d.S) ⊔ (ambientCore u ⊓ d.S),d.R⁆ :=
      congrArg (fun B : Subgroup G => ⁅B,d.R⁆) (d.R_eq_pointCore_join h ht hu ht1 hu1 htu)
    _ ≤ ambientCore t := commutator_sup_le_of_relative_normal d.S _ _ _ _ hn
      inf_le_right inf_le_right hAR hBR

/-- The radical has nilpotence class at most two, with all commutators in Z. -/
theorem R_commutator_le_space (h : IsTypeJ4 z) : ⁅d.R,d.R⁆ ≤ d.space :=
  le_inf (le_inf
    (d.R_commutator_le_pointCore h d.z_in_space d.r_in_space (z_ne_one h) (d.r_ne_one h) d.r_ne.symm)
    (d.R_commutator_le_pointCore h d.r_in_space d.z_in_space (d.r_ne_one h) (z_ne_one h) d.r_ne))
    (d.R_commutator_le_pointCore h d.s_in_space d.z_in_space (d.s_ne_one h) (z_ne_one h) d.s_ne)

private theorem R_square_mem_pointCore (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u)
    {x : G} (hx : x ∈ d.R) : x^2 ∈ ambientCore t := by
  have hprod : x ∈ ((ambientCore t ⊓ d.S : Subgroup G) : Set G) *
      ((ambientCore u ⊓ d.S : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (d.coreCentralizer_normalized h ht ht1)),
      ← d.R_eq_pointCore_join h ht hu ht1 hu1 htu]
    exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hprod
  have hn : b ∈ normalizer (ambientCore t : Set G) := by
    rw [LocalGeometry.normalizer_ambientCore (d.point_type h ht ht1)]
    exact d.S_le_point_centralizer ht hb.2
  have hb2 : b^2 ∈ ambientCore t := by
    let hu' := d.point_type h hu hu1
    let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient u) hu'.extraspecial
    have hbc : b^2 ∈ (center (ambientCore u)).map (ambientCore u).subtype :=
      ⟨(⟨b,hb.1⟩ : ambientCore u)^2,IsExtraspecial.square_mem_center _,rfl⟩
    rw [LocalGeometry.ambientCore_center_image hu'] at hbc
    exact (zpowers_le.mpr (d.contained_in_cores t ht ht1 hu)) hbc
  have he : (a*b)^2 = a*(b*a*b⁻¹)*b^2 := by simp only [pow_two]; group
  rw [he]
  exact (ambientCore t).mul_mem ((ambientCore t).mul_mem ha.1
    ((mem_normalizer_iff.mp hn a).mp ha.1)) hb2

/-- Every square in the radical belongs to the original three-space. -/
theorem R_square_mem_space (h : IsTypeJ4 z) {x : G} (hx : x ∈ d.R) : x^2 ∈ d.space :=
  ⟨⟨d.R_square_mem_pointCore h d.z_in_space d.r_in_space (z_ne_one h) (d.r_ne_one h) d.r_ne.symm hx,
    d.R_square_mem_pointCore h d.r_in_space d.z_in_space (d.r_ne_one h) (z_ne_one h) d.r_ne hx⟩,
    d.R_square_mem_pointCore h d.s_in_space d.z_in_space (d.s_ne_one h) (z_ne_one h) d.s_ne hx⟩

/-- Each point is an actual commutator in its large core centralizer. -/
theorem point_mem_R_commutator (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) : t ∈ ⁅d.R,d.R⁆ := by
  let Q := ambientCore t
  let A := Q ⊓ d.S
  let ht' := d.point_type h ht ht1
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient t) ht'.extraspecial
  have hnc : ¬ IsMulCommutative A := by
    intro hA
    let := hA
    let A₀ := A.subgroupOf Q
    let : IsMulCommutative A₀ :=
      Subgroup.subgroupOf_isMulCommutative (H := A) (K := Q)
    have hb := extraspecial_prime_abelian_card_sq_le_any (p := 2) A₀
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ Q from inf_le_left)).toEquiv] at hb
    have hQ : Nat.card Q = 8192 :=
      (Nat.card_congr (LocalGeometry.coreEquivAmbient t).toEquiv).symm.trans ht'.core_card
    have hAcard : Nat.card A = 2048 := d.coreCentralizer_card h ht ht1
    rw [hQ,hAcard] at hb
    norm_num at hb
  obtain ⟨a,b,hab⟩ : ∃ a b : A, a*b ≠ b*a := by
    by_contra! hh
    exact hnc ⟨⟨hh⟩⟩
  have hcomm : ⁅(a : G),(b : G)⁆ ∈ zpowers t := by
    rw [←d.pointCore_commutator h ht ht1]
    exact commutator_mem_commutator a.property.1 b.property.1
  have hne : ⁅(a : G),(b : G)⁆ ≠ 1 := by
    intro he
    exact hab (Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp he))
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : zpowers t)).mp
    ((Nat.card_zpowers t).trans ht'.involution)
  have he : ⁅(a : G),(b : G)⁆ = t := congrArg Subtype.val
    ((hw ⟨_,hcomm⟩ (fun he => hne (congrArg Subtype.val he))).trans
      (hw ⟨t,mem_zpowers t⟩ (fun he => ht1 (congrArg Subtype.val he))).symm)
  rw [←he]
  exact commutator_mem_commutator ((d.coreCentralizer_le_R ht ht1) a.property)
    ((d.coreCentralizer_le_R ht ht1) b.property)

/-- The derived subgroup of R is exactly the original three-space. -/
theorem R_commutator_eq_space (h : IsTypeJ4 z) : ⁅d.R,d.R⁆ = d.space := by
  apply le_antisymm (d.R_commutator_le_space h)
  intro t ht
  by_cases ht1 : t = 1
  · exact ht1 ▸ one_mem _
  · exact d.point_mem_R_commutator h ht ht1

private theorem R_center_le_pointCore (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    (center d.R).map d.R.subtype ≤ ambientCore t := by
  let ht' := d.point_type h ht ht1
  let hu' := d.point_type h hu hu1
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient t) ht'.extraspecial
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient u) hu'.extraspecial
  have htuConj : IsConj t u := by
    obtain ⟨a,_,ha⟩ := d.normalizer_transitive t ht ht1
    obtain ⟨b,_,hb⟩ := d.normalizer_transitive u hu hu1
    exact (isConj_iff.mpr ⟨a,ha⟩).symm.trans (isConj_iff.mpr ⟨b,hb⟩)
  let T := ambientCore t ⊓ ambientCore u
  let := returningIntersection_elementary ht' htuConj (Ne.symm htu)
  have hT : Nat.card T = 128 :=
    (returning_intersection_image_orders ht' htuConj (d.contained_in_cores t ht ht1 hu) (Ne.symm htu)).1
  have hTS : T ≤ d.S := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm
      (⟨y,d.contained_in_cores t ht ht1 hy,d.contained_in_cores u hu hu1 hy⟩ : T) (⟨x,hx⟩ : T))
  have hTR : T ≤ d.R :=
    (le_inf inf_le_left hTS).trans (d.coreCentralizer_le_R ht ht1)
  have hself (Q : Subgroup G) [IsExtraspecial 2 Q] (hTQ : T ≤ Q) (hcard : Nat.card Q = 8192) :
      Subgroup.centralizer (T.subgroupOf Q : Set Q) = T.subgroupOf Q := by
    let := IsElementaryAbelian.subgroupOf (p := 2) hTQ
    apply extraspecial_prime_selfcentralizing_of_card_sq (p := 2)
    rw [Nat.card_congr (subgroupOfEquivOfLe hTQ).toEquiv,hT,hcard]
    norm_num
  have hQcard : Nat.card (ambientCore t) = 8192 :=
    (Nat.card_congr (LocalGeometry.coreEquivAmbient t).toEquiv).symm.trans ht'.core_card
  have hPcard : Nat.card (ambientCore u) = 8192 :=
    (Nat.card_congr (LocalGeometry.coreEquivAmbient u).toEquiv).symm.trans hu'.core_card
  have hd : Disjoint ((center (ambientCore t)).map (ambientCore t).subtype)
      ((center (ambientCore u)).map (ambientCore u).subtype) := by
    apply ExtraspecialIntersection.disjoint_centers_of_ne
    rw [LocalGeometry.ambientCore_center_image ht',LocalGeometry.ambientCore_center_image hu']
    intro he
    have huT : u ∈ zpowers t := he ▸ mem_zpowers u
    obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : zpowers t)).mp
      ((Nat.card_zpowers t).trans ht'.involution)
    exact htu (congrArg Subtype.val ((hw ⟨t,mem_zpowers t⟩
      (fun he => ht1 (congrArg Subtype.val he))).trans
      (hw ⟨u,huT⟩ (fun he => hu1 (congrArg Subtype.val he))).symm))
  rintro x ⟨x,hx,rfl⟩
  have hprod : (x : G) ∈ ((ambientCore t ⊓ d.S : Subgroup G) : Set G) *
      ((ambientCore u ⊓ d.S : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (d.coreCentralizer_normalized h ht ht1)),
      ←d.R_eq_pointCore_join h ht hu ht1 hu1 htu]
    exact x.property
  obtain ⟨a,ha,b,hb,he⟩ := hprod
  change a*b = (x : G) at he
  have hab : a*b ∈ Subgroup.centralizer (T : Set G) := by
    intro v hv
    have hh := congrArg Subtype.val (mem_center_iff.mp hx (⟨v,hTR hv⟩ : d.R))
    change v*(x : G) = (x : G)*v at hh
    rwa [he]
  have hm := central_product_mem_inf (ambientCore t) (ambientCore u)
    (hself _ inf_le_left hQcard) (hself _ inf_le_right hPcard) hd ha.1 hb.1 hab
  change (x : G) ∈ ambientCore t
  exact he ▸ hm.1

/-- AS91 (4.4): the center of R is exactly the original three-space. -/
theorem R_center_eq_space (h : IsTypeJ4 z) : (center d.R).map d.R.subtype = d.space := by
  apply le_antisymm
  · exact le_inf (le_inf
      (d.R_center_le_pointCore h d.z_in_space d.r_in_space (z_ne_one h) (d.r_ne_one h) d.r_ne.symm)
      (d.R_center_le_pointCore h d.r_in_space d.z_in_space (d.r_ne_one h) (z_ne_one h) d.r_ne))
      (d.R_center_le_pointCore h d.s_in_space d.z_in_space (d.s_ne_one h) (z_ne_one h) d.s_ne)
  · intro x hx
    have hZR : d.space ≤ d.R := (d.R_commutator_eq_space h).symm.le.trans d.R.commutator_le_self
    refine ⟨⟨x,hZR hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (y.property.2 x hx).symm

/-- The intrinsic derived subgroup and center of R coincide. -/
theorem R_derived_eq_center (h : IsTypeJ4 z) : commutator d.R = center d.R := by
  apply Subgroup.map_injective d.R.subtype_injective
  rw [map_subtype_commutator,d.R_commutator_eq_space h,d.R_center_eq_space h]

/-- The center quotient is elementary abelian, including the square condition. -/
theorem R_center_quotient_elementary (h : IsTypeJ4 z) :
    IsElementaryAbelian 2 (d.R ⧸ center d.R) := by
  refine { toIsMulCommutative :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (d.R_derived_eq_center h).le
           exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  refine QuotientGroup.induction_on x ?_
  intro r
  apply (QuotientGroup.eq_one_iff (r^2)).mpr
  have hs := d.R_square_mem_space h r.property
  rw [←d.R_center_eq_space h] at hs
  have hm : r^2 ∈ ((center d.R).map d.R.subtype).comap d.R.subtype := hs
  rwa [comap_map_eq_self_of_injective d.R.subtype_injective] at hm

/-- The Frattini subgroup equals the center, completing the special-group clauses. -/
theorem R_frattini_eq_center (h : IsTypeJ4 z) : frattini d.R = center d.R := by
  have hp : IsPGroup 2 d.R := by
    rw [d.R_eq_K_twoCore h]
    exact isPGroup_pCoreIn 2 d.K
  let : Fact (IsPGroup 2 d.R) := ⟨hp⟩
  apply le_antisymm
    (frattini_le_of_elementary_quotient hp (center d.R) (d.R_center_quotient_elementary h))
  rw [←d.R_derived_eq_center h]
  exact commutator_le_frattini_of_isPGroup (p := 2)

/-- The elementary center quotient has order 2¹². -/
theorem R_center_quotient_card (h : IsTypeJ4 z) : Nat.card (d.R ⧸ center d.R) = 4096 := by
  have hZ : Nat.card (center d.R) = 8 := by
    rw [←card_map_of_injective d.R.subtype_injective,d.R_center_eq_space h]
    exact d.card
  have hc := (center d.R).card_mul_index
  rw [hZ,d.R_card h] at hc
  exact (by omega : (center d.R).index = 4096)

/-- The source rank m(R/Z) is twelve. -/
theorem R_center_quotient_rank (h : IsTypeJ4 z) : primeRank 2 (d.R ⧸ center d.R) = 12 := by
  let := d.R_center_quotient_elementary h
  rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 2),d.R_center_quotient_card h]
  norm_num

end ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The constructed source three-space has all special-radical and S₅ clauses
of AS91 (4.4), retaining the original cubic quotient and its Sylow subgroup. -/
theorem source_three_space_radical_structure (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)) :
    ∃ d : ThreeSpaceData z e X,
      Function.Surjective d.normalizerAction ∧ Function.Surjective d.KAction ∧
      normalizer (d.space : Set G) = d.K ⊔ d.S ∧
      (letI := d.R_normal_in_K
       Nonempty ((d.K ⧸ d.R.subgroupOf d.K) ≃* Matrix.PSL3Two.PSL)) ∧
      d.R = d.K.pCoreIn 2 ∧ d.R = d.S.pCoreIn 2 ∧ Nat.card d.R = 32768 ∧
      (center d.R).map d.R.subtype = d.space ∧
      commutator d.R = center d.R ∧ frattini d.R = center d.R ∧
      IsElementaryAbelian 2 (d.R ⧸ center d.R) ∧
      Nat.card (d.R ⧸ center d.R) = 4096 ∧ primeRank 2 (d.R ⧸ center d.R) = 12 ∧
      ∃ hR : (d.R.subgroupOf d.S).Normal,
        letI := hR
        Nonempty ((d.S ⧸ d.R.subgroupOf d.S) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨d⟩ := source_three_space_data h e X
  exact ⟨d,d.normalizerAction_surjective h,d.KAction_surjective h,d.normalizer_eq_K_sup_S h,
    d.K_quotient_PSL3 h,d.R_eq_K_twoCore h,d.R_eq_S_twoCore h,d.R_card h,
    d.R_center_eq_space h,d.R_derived_eq_center h,d.R_frattini_eq_center h,
    d.R_center_quotient_elementary h,d.R_center_quotient_card h,d.R_center_quotient_rank h,
    d.R_normal_in_S h,d.S_quotient_symmetricFive h⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
