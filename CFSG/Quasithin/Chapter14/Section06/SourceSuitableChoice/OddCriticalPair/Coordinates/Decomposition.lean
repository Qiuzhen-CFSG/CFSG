module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.MarkedFactors
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.CoreRank

/-!
# The literal orthogonal supports and fixed seed supplement

The two covering planes span [U_H,H] and meet in the central line Z. Lifting
its quotient fixed space retains a full fixed supplement C. The actual
exchanged-factor element identifies the other plane with the original H₂
support. The residual of the full quotient centralizer fixes the entire first
plane and C, normalizes the second plane, and has commutator containing Z there.

The source application uses the same H, M, Mc and u. It supplies these geometric
facts to the residual-coordinate construction; the nonzero seed projections
and their commutator generation are still needed for that construction.

Source: Aschbacher--Smith 14.6.12 and 14.6.17(5), printed pp.1031, 1035--1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 OddNormalizer OrthogonalSource
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

noncomputable def fixedSupport (a : LocalQuotientAction H U Z) : Subgroup G :=
  supportPreimage a (fixedSpace a.representation ⊤)

/-- Quotient fixedness is stated as an actual central-line commutator bound. -/
theorem fixedSupport_commutator (a : LocalQuotientAction H U Z) :
    ⁅fixedSupport a,H⁆ ≤ Z := by
  rw [commutator_comm,commutator_le]
  intro x hx c hc
  have hcU := supportPreimage_le a _ hc
  let cU : U := ⟨c,hcU⟩
  have hf := (mem_supportPreimage a (fixedSpace a.representation ⊤) cU).mp hc
  have he := hf ⟨QuotientGroup.mk' (pCore 2 H) ⟨x,hx⟩,mem_top _⟩
  change a.representation (QuotientGroup.mk' (pCore 2 H) ⟨x,hx⟩)
    (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) cU)) = _ at he
  rw [a.conjugation] at he
  have hz := QuotientGroup.eq_iff_div_mem.mp (congrArg Additive.toMul he)
  change x*c*x⁻¹/c ∈ Z at hz
  simpa only [div_eq_mul_inv,commutatorElement_def] using hz

/-- The whole quotient decomposition lifts while retaining its fixed factor. -/
theorem support_cover_of_moved_fixed (a : LocalQuotientAction H U Z)
    (hZ : Z ≤ ⁅U,H⁆)
    (hd : movedSpace a ⊔ fixedSpace a.representation ⊤ = ⊤) :
    U = ⁅U,H⁆ ⊔ fixedSupport a := by
  apply le_antisymm ?_ (sup_le (moved_le a) (supportPreimage_le a _))
  intro u hu
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  obtain ⟨v,hv,c,hc,he⟩ := Submodule.mem_sup.mp
    (hd.ge (Submodule.mem_top (x := Additive.ofMul (q ⟨u,hu⟩))))
  obtain ⟨k,hk⟩ := movedMap_surjective a (Multiplicative.ofAdd ⟨v,hv⟩)
  have hkq : q ⟨k,moved_le a k.property⟩ = v.toMul :=
    congrArg (fun w => w.toAdd.val.toMul) hk
  obtain ⟨cU,hcq⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) c.toMul
  have hcC : (cU : G) ∈ fixedSupport a := by
    apply (mem_supportPreimage a _ cU).mpr
    simpa only [hcq,ofMul_toMul] using hc
  let w : U := ⟨u,hu⟩ * ((⟨k,moved_le a k.property⟩ : U)*cU)⁻¹
  have hw : q w = 1 := by
    rw [map_mul,map_inv,map_mul,hkq,hcq]
    apply mul_inv_eq_one.mpr
    exact (congrArg Additive.toMul he).symm
  have hwZ : (w : G) ∈ Z := (QuotientGroup.eq_one_iff w).mp hw
  have hh := (⁅U,H⁆ ⊔ fixedSupport a).mul_mem
    ((le_sup_left : ⁅U,H⁆ ≤ ⁅U,H⁆ ⊔ fixedSupport a) (hZ hwZ))
    ((⁅U,H⁆ ⊔ fixedSupport a).mul_mem ((le_sup_left : ⁅U,H⁆ ≤ ⁅U,H⁆ ⊔ fixedSupport a) k.property) ((le_sup_right : fixedSupport a ≤ ⁅U,H⁆ ⊔ fixedSupport a) hcC))
  simpa only [fixedSupport,w,coe_mul,coe_inv,mul_assoc,inv_mul_cancel,mul_one] using hh

variable [Finite G] {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
include h

/-- The full residual centralizes every lift of the globally fixed quotient factor. -/
theorem residual_centralizes_fixedSupport
    [IsElementaryAbelian 2 D.UH] (a : LocalQuotientAction D.H D.UH D.V₁)
    (u : G) (hu : u ∈ D.UH) :
    (pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype ≤
      centralizer (fixedSupport a : Set G) := by
  have hPH : h.kernel (zpowers u) ≤ D.H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp hx).1
  apply residual_centralizes_of_two_layer _ _ D.V₁
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa using h.point_card))
    (hPH.trans h.H_centralizes)
  rw [commutator_comm]
  exact (commutator_mono le_rfl hPH).trans (fixedSupport_commutator a)

/-- O²(P) fixes the entire first covering plane, not merely the selected u. -/
theorem original_residual_centralizes_first_support
    [IsElementaryAbelian 2 D.UH]
    (a : LocalQuotientAction D.H D.UH D.V₁) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (D.T : Subgroup G) 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i : OrthogonalPlaneIndex) (hi : o.plane i = firstSupport a H1)
    (u : (⁅D.UH,D.H⁆ : Subgroup G))
    (hu : (u : G) ∈ o.plane i) (huz : (u : G) ∉ D.V₁) :
    (pResidual 2 (h.kernel (zpowers (u : G)))).map (h.kernel (zpowers (u : G))).subtype ≤
      centralizer (o.plane i : Set G) := by
  rw [← (original_second_factor_residual h a H0 H1 H2 d o i hi u hu huz).2.2,hi]
  apply residual_centralizes_of_two_layer H2 _ D.V₁
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa using h.point_card))
    ((d.second_le.trans d.zero_le).trans h.H_centralizes)
  rw [commutator_comm]
  exact second_factor_fixes_first_support a (D.T : Subgroup G) 3 H0 H1 H2 d

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.SourceOrthogonalFourAction
open Chapter15.Section03
variable {G : Type*} [Group G] {H U Z Q : Subgroup G}
variable (d : SourceOrthogonalFourAction H U Z Q)

/-- The two literal covering planes generate the actual moved group. -/
theorem planes_join_eq (i j : OrthogonalPlaneIndex) (hji : j ≠ i) :
    d.plane i ⊔ d.plane j = ⁅U,H⁆ := by
  apply le_antisymm (sup_le (d.plane_le i) (d.plane_le j))
  intro x hx
  let xK : (⁅U,H⁆ : Subgroup G) := ⟨x,hx⟩
  let v := d.coordinates xK
  let v1 : OrthogonalVector := fun k => if k = i then v k else 1
  let v2 : OrthogonalVector := fun k => if k = i then 1 else v k
  have hs1 : BinaryWreathPointStabilizer.Supported i v1 := fun k hk => if_neg hk
  have hs2 : BinaryWreathPointStabilizer.Supported j v2 := by
    intro k hk
    have hh : ∀ i j k : OrthogonalPlaneIndex, j ≠ i → k ≠ j → k = i := by decide
    exact if_pos (hh i j k hji hk)
  have hv : v1*v2 = v := by
    funext k
    by_cases hk : k = i <;> simp [v1,v2,hk]
  obtain ⟨a,ha⟩ := d.surjective v1
  obtain ⟨b,hb⟩ := d.surjective v2
  have haA : (a : G) ∈ d.plane i := (d.mem_plane_iff i a).mpr (ha.symm ▸ hs1)
  have hbB : (b : G) ∈ d.plane j := (d.mem_plane_iff j b).mpr (hb.symm ▸ hs2)
  let w : (⁅U,H⁆ : Subgroup G) := xK*(a*b)⁻¹
  have hw : w ∈ d.coordinates.ker := by
    change d.coordinates w = 1
    simp only [w,map_mul,map_inv,ha,hb,hv]
    exact mul_inv_cancel _
  have hwZ : (w : G) ∈ Z := by rwa [d.vector_kernel] at hw
  have hh := (d.plane i ⊔ d.plane j).mul_mem
    ((le_sup_left : d.plane i ≤ d.plane i ⊔ d.plane j) (d.point_le_plane i hwZ))
    ((d.plane i ⊔ d.plane j).mul_mem ((le_sup_left : d.plane i ≤ d.plane i ⊔ d.plane j) haA) ((le_sup_right : d.plane j ≤ d.plane i ⊔ d.plane j) hbB))
  simpa only [w,coe_mul,coe_inv,mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The two covering planes meet in exactly the source line. -/
theorem planes_inf_eq (i j : OrthogonalPlaneIndex) (hji : j ≠ i) :
    d.plane i ⊓ d.plane j = Z := by
  apply le_antisymm ?_ (le_inf (d.point_le_plane i) (d.point_le_plane j))
  intro x hx
  let v : (⁅U,H⁆ : Subgroup G) := ⟨x,d.plane_le i hx.1⟩
  have hi := (d.mem_plane_iff i v).mp hx.1
  have hj := (d.mem_plane_iff j v).mp hx.2
  have he : d.coordinates v = 1 := by
    funext k
    by_cases hk : k = i
    · subst k
      exact hj i (Ne.symm hji)
    · exact hi k hk
  have hh : v ∈ d.coordinates.ker := he
  rwa [d.vector_kernel] at hh

end CFSG.Quasithin.Chapter14.Section06.SourceOrthogonalFourAction

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 OddNormalizer OrthogonalSource
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
attribute [local instance] orthogonalAction

/-- The whole fixed supplement meets the moved group only in the central line. -/
theorem moved_inf_fixedSupport_le (a : LocalQuotientAction H U Z)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2)) :
    ⁅U,H⁆ ⊓ fixedSupport a ≤ Z := by
  intro x hx
  let v : (⁅U,H⁆ : Subgroup G) := ⟨x,hx.1⟩
  have hfix : ∀ g : OrthogonalActor, g • o.coordinates v = o.coordinates v := by
    intro g
    obtain ⟨y,rfl⟩ := o.onto g
    apply (o.fixed_iff_commutator_mem y v).mpr
    exact fixedSupport_commutator a (commutator_mem_commutator hx.2 y.property)
  have he := BinaryWreathPointStabilizer.fixed_vector_eq_one (o.coordinates v) hfix
  have hh : v ∈ o.coordinates.ker := he
  rwa [o.vector_kernel] at hh

private theorem support_separation {A B C K : Subgroup G}
    (hAU : A ≤ U) (hBU : B ≤ U) (hCU : C ≤ U)
    (hAK : A ≤ K) (hBK : B ≤ K) (hAB : A ⊓ B ≤ Z)
    (hKC : K ⊓ C ≤ Z) (hZB : Z ≤ B) : A ⊓ (B ⊔ C) ≤ Z := by
  intro x hx
  have hxU : x ∈ U := hAU hx.1
  have hsub : (⟨x,hxU⟩ : U) ∈ B.subgroupOf U ⊔ C.subgroupOf U := by
    rw [←subgroupOf_sup hBU hCU]
    exact hx.2
  obtain ⟨b,hb,c,hc,he⟩ := mem_sup_of_normal_right.mp hsub
  have heG : (b : G)*(c : G) = x := congrArg Subtype.val he
  have hcK : (c : G) ∈ K := by
    have hh := K.mul_mem (K.inv_mem (hBK hb)) (hAK hx.1)
    change (b : G)⁻¹*x ∈ K at hh
    rw [←heG,inv_mul_cancel_left] at hh
    exact hh
  have hxB : x ∈ B := heG ▸ B.mul_mem hb (hZB (hKC ⟨hcK,hc⟩))
  exact hAB ⟨hx.1,hxB⟩

/-- The first covering plane remains independent after adjoining the entire
fixed supplement to the second plane. -/
theorem first_plane_separated_fixed (a : LocalQuotientAction H U Z)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) :
    o.plane i ⊓ (o.plane j ⊔ fixedSupport a) ≤ Z := by
  have hKU : ⁅U,H⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp o.normalized
  exact support_separation ((o.plane_le i).trans hKU) ((o.plane_le j).trans hKU)
    (supportPreimage_le a _) (o.plane_le i) (o.plane_le j)
    (o.planes_inf_eq i j hji).le (moved_inf_fixedSupport_le a o) (o.point_le_plane j)

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
attribute [local instance] orthogonalAction
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
include h

/-- The full quotient centralizer preserves both covering planes. -/
theorem suitable_kernel_normalizes_planes
    (o : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i j : OrthogonalPlaneIndex) (u : (⁅D.UH,D.H⁆ : Subgroup G))
    (hu : (u : G) ∈ o.plane i) (huz : (u : G) ∉ D.V₁) :
    h.kernel (zpowers (u : G)) ≤ normalizer (o.plane j : Set G) := by
  have huU : (u : G) ∈ D.UH :=
    (le_normalizer_iff_commutator_le_left.mp o.normalized) u.property
  have huH := h.UH_le_H huU
  have hun : o.coordinates u ≠ 1 := by
    intro hh
    have hk : u ∈ o.coordinates.ker := hh
    rw [o.vector_kernel] at hk
    exact huz hk
  apply le_normalizer_iff.mpr
  intro x hx w hw
  obtain ⟨hxH,hxc⟩ := (h.mem_kernel_iff (zpowers_le.mpr huH)).mp hx
  let xH : D.H := ⟨x,hxH⟩
  let wK : (⁅D.UH,D.H⁆ : Subgroup G) := ⟨w,o.plane_le j hw⟩
  let y := ⁅D.UH,D.H⁆.normalizerMonoidHom
    ⟨xH,normalizer_commutator_ge_right D.UH D.H hxH⟩ wK
  have hshift := BinaryWreathPointStabilizer.fixed_no_shift
    ((o.mem_plane_iff i u).mp hu) hun (o.actor xH)
    ((o.fixed_iff_commutator_mem xH u).mpr (hxc u (mem_zpowers _)))
  have hs := (o.mem_plane_iff j wK).mp hw
  change (y : G) ∈ o.plane j
  apply (o.mem_plane_iff j y).mpr
  rw [show o.coordinates y = o.actor xH • o.coordinates wK from o.compatible xH wK]
  intro k hk
  change (o.actor xH).left k • o.coordinates wK ((o.actor xH).right⁻¹ * k) = 1
  rw [hshift,inv_one,one_mul,hs k hk,smul_one]

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] orthogonalAction
attribute [local instance] FourGroupMatrixCoordinates.naturalAction

/-- The actual actor shift transports the literal covering planes. -/
theorem SourceOrthogonalFourAction.plane_conjugate
    {H U Z Q : Subgroup G} (o : SourceOrthogonalFourAction H U Z Q)
    (hZ : Nat.card Z = 2) (i : OrthogonalPlaneIndex) (x : H) :
    (o.plane i).map (MulAut.conj (x : G)).toMonoidHom =
      o.plane ((o.actor x).right*i) := by
  apply eq_of_le_of_card_ge ?_ (by
    rw [card_map_of_injective (MulAut.conj (x : G)).injective,
      o.card_plane hZ,o.card_plane hZ])
  rintro _ ⟨v,hv,rfl⟩
  let w : (⁅U,H⁆ : Subgroup G) := ⟨v,o.plane_le i hv⟩
  let y := ⁅U,H⁆.normalizerMonoidHom
    ⟨x,normalizer_commutator_ge_right U H x.property⟩ w
  have hs := (o.mem_plane_iff i w).mp hv
  change (y : G) ∈ o.plane ((o.actor x).right*i)
  apply (o.mem_plane_iff _ y).mpr
  rw [show o.coordinates y = o.actor x • o.coordinates w from o.compatible x w]
  intro k hk
  change (o.actor x).left k • o.coordinates w ((o.actor x).right⁻¹*k) = 1
  have hi : (o.actor x).right⁻¹*k ≠ i := by
    intro he
    exact hk ((inv_mul_eq_iff_eq_mul).mp he)
  rw [hs _ hi,smul_one]

namespace OddCriticalPair
open OddNormalizer OrthogonalSource
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- The original exchanged second support is the other covering plane in the
same orthogonal coordinates. The actual T-element supplies the transport. -/
theorem original_second_support_eq
    (a : LocalQuotientAction H U Z) (T H0 H1 H2 : Subgroup G) (hTH : T ≤ H)
    (d : ExchangedFactorSetup a T 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2)) (hZ : Nat.card Z = 2)
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1) :
    o.plane j = firstSupport a H2 := by
  obtain ⟨x,hx,_,hex⟩ := d.exchanged
  let xH : H := ⟨x⁻¹,H.inv_mem (hTH hx)⟩
  have ht : (firstSupport a H1).map (MulAut.conj (x⁻¹)).toMonoidHom = firstSupport a H2 := by
    unfold firstSupport
    rw [supportPreimage_conjugate a _ xH,moved_map_conjugate,
      ←actorImage_conjugate H1 (d.first_le.trans d.zero_le) xH]
    change supportPreimage a (subspaceCommutator a.representation ⊤
      (actorImage H (H1.map (MulAut.conj x⁻¹).toMonoidHom))) = _
    rw [hex]
  have hp := o.plane_conjugate hZ i xH
  rw [hi,ht] at hp
  have hs : (o.actor xH).right*i ≠ i := by
    intro he
    rw [he,hi] at hp
    have hsep := supportPreimage_disjoint_modulo a _ _ d.disjoint
    change firstSupport a H1 ⊓ firstSupport a H2 ≤ Z at hsep
    rw [hp,inf_idem,←hi] at hsep
    have hc := card_le_of_le hsep
    rw [o.card_plane hZ,hZ] at hc
    omega
  have he : (o.actor xH).right*i = j := by
    have htwo : ∀ i j k : OrthogonalPlaneIndex, j ≠ i → k ≠ i → k = j := by decide
    exact htwo i j _ hji hs
  rw [he] at hp
  exact hp.symm

end OddCriticalPair
end CFSG.Quasithin.Chapter14.Section06

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
variable {G : Type*} [Group G] {U B F R : Subgroup G} [IsElementaryAbelian 2 U]

/-- A fixed supplement contributes no commutators, with all normality relative
to the actual normalized module. -/
theorem commutator_eq_of_fixed_cover (hcover : U = B ⊔ F)
    (hn : R ≤ normalizer (B : Set G)) (hf : R ≤ centralizer (F : Set G)) :
    ⁅U,R⁆ = ⁅B,R⁆ := by
  have hBU : B ≤ U := le_sup_left.trans hcover.ge
  have hFU : F ≤ U := le_sup_right.trans hcover.ge
  let J := ⁅B,R⁆
  have hJU : J ≤ U := (le_normalizer_iff_commutator_le_left.mp hn).trans hBU
  have hUN : U ≤ normalizer (J : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hJU)).trans (Subgroup.centralizer_le_normalizer _)
  have hBP : B ≤ commutatorPreimage U R J := le_commutatorPreimage hBU le_rfl
  have hFP : F ≤ commutatorPreimage U R J := by
    apply le_commutatorPreimage hFU
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hf)]
    exact bot_le
  have hUP : U ≤ commutatorPreimage U R J := hcover.le.trans (sup_le hBP hFP)
  exact le_antisymm
    ((commutator_mono hUP le_rfl).trans (commutator_commutatorPreimage_le U R J hUN))
    (commutator_mono hBU le_rfl)

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The actual support cover and the entire fixed seed factor for the same
full parabolic residual. No lift correction or fixed complement is assumed. -/
theorem source_orthogonal_fixed_factor_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1)
    (u : G) (hu : u ∈ o.plane i) (huz : u ∉ centralInvolutions T) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let P := h.kernel (zpowers u)
    let R := (pResidual 2 P).map P.subtype
    conjugateSpanBy (localModule T M) H = o.plane i ⊔ o.plane j ⊔ fixedSupport a ∧
      o.plane j = firstSupport a H2 ∧
      o.plane i ⊓ o.plane j = centralInvolutions T ∧
      o.plane i ⊓ (o.plane j ⊔ fixedSupport a) ≤ centralInvolutions T ∧
      IsElementaryAbelian 2 (o.plane j) ∧ Nat.card (o.plane j) = 8 ∧
      centralInvolutions T ≤ ⁅o.plane j,R⁆ ∧
      R ≤ normalizer (o.plane j : Set G) ∧
      R ≤ centralizer ((o.plane i ⊔ fixedSupport a : Subgroup G) : Set G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hd := source_rankTwo_span_decomposition hG T hempty hM hunique hmany hcard e hab H hH a
  rw [←source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a] at hd
  have hc := support_cover_of_moved_fixed a o.point_le hd
  rw [←o.planes_join_eq i j hji] at hc
  have huK := o.plane_le i hu
  have huU := (le_normalizer_iff_commutator_le_left.mp o.normalized) huK
  have hA := original_residual_centralizes_first_support (D := D) h a H0 H1 H2 d o i hi
    ⟨u,huK⟩ hu huz
  have hC := residual_centralizes_fixedSupport (D := D) h a u huU
  have hKU : ⁅D.UH,D.H⁆ ≤ D.UH := le_normalizer_iff_commutator_le_left.mp o.normalized
  have hPN := suitable_kernel_normalizes_planes (D := D) h o i j ⟨u,huK⟩ hu huz
  let R := (pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype
  have hnR : R ≤ normalizer (o.plane j : Set G) := (map_subtype_le _).trans hPN
  have hf : R ≤ centralizer ((o.plane i ⊔ fixedSupport a : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hA) (le_centralizer_iff.mp hC))
  have hcover : D.UH = o.plane j ⊔ (o.plane i ⊔ fixedSupport a) := by
    change conjugateSpanBy (localModule T M) H = _
    exact hc.trans (by ac_rfl)
  have hcomm := commutator_eq_of_fixed_cover hcover hnR hf
  have hres := (original_second_factor_residual (D := D) h a H0 H1 H2 d o i hi
    ⟨u,huK⟩ hu huz).2.2
  have hline : D.V₁ ≤ ⁅o.plane j,R⁆ := by
    rw [←hcomm]
    change D.V₁ ≤ ⁅D.UH,(pResidual 2 (h.kernel (zpowers u))).map
      (h.kernel (zpowers u)).subtype⁆
    rw [←hres]
    exact d.point_second
  exact ⟨hc,original_second_support_eq a (T : Subgroup G) H0 H1 H2 hH.1.2 d o
      h.point_card i j hji hi,o.planes_inf_eq i j hji,first_plane_separated_fixed a o i j hji,
    IsElementaryAbelian.of_le ((o.plane_le j).trans hKU),o.card_plane h.point_card j,
    hline,hnR,hf⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
