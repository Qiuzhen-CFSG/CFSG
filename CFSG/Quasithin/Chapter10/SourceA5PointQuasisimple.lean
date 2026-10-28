module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.CentralProductCenter
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The A5 local component inside a central quotient

In the quasisimple containing-component branch of source 10.2.9, the actual
embedding is the image of the original local component in `I / Z(I)`.
Its moved elementary subgroup remains noncentral after every central quotient.
The binary A5 degree bound therefore forces the center of its 2-core to have
at least sixteen elements. This excludes quasisimple, extraspecial-kernel and
cyclic-four central-product-kernel smaller groups, including their central lifts.

The proof transports the 2-core across a central quotient, uses full movement
to retain a nontrivial action, and applies the original A5 degree estimate.
The final theorem uses the literal restriction of the quotient by `center I`.
These are the small-row reductions used with A.3.12/A.3.14 on pp.750–751 of
Aschbacher–Smith, *The Classification of Quasithin Groups*, volume II,
1 March 2004 manuscript. They do not assert the surviving embedding-action
calculation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original moved module lies in the component's 2-core. -/
theorem source_full_moved_le_component_core : ⁅D.fullModule,L⁆ ≤ L.pCoreIn 2 := by
  let := source_original_full_moved_elementary D
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    (source_full_moved_le_component D) (normalizer_commutator_ge_right _ _)

include D in
/-- The original A5 action forces a large central elementary part of the 2-core. -/
theorem source_a5_component_core_center_card (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    16 ≤ Nat.card (center (pCore 2 L)) := by
  let W := ⁅D.fullModule,L⁆
  have hWL : W ≤ L := source_full_moved_le_component D
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  let f : W → center (pCore 2 L) := fun w =>
    ⟨⟨⟨w,hWL w.property⟩,(mem_map_iff_mem L.subtype_injective).mp (source_full_moved_le_component_core D w.property)⟩,
      mem_center_iff.mpr (fun q => Subtype.ext (Subtype.ext
        (source_component_core_centralizes_fullModule D
          (mem_map_of_mem L.subtype q.property) w (hWV w.property)).symm))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : center (pCore 2 L) => (((x : pCore 2 L) : L) : G)) h
  exact (source_a5_full_moved_card D e).trans (Nat.card_le_card_of_injective f hf)

private theorem extension_core {K : Type*} [Group K] [Finite K] (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (N : Subgroup K) [N.Normal] (hN : IsPGroup 2 N)
    (f : (K ⧸ N) ≃* alternatingGroup (Fin 5)) : N = pCore 2 K := by
  have hle : N ≤ pCore 2 K := le_sSup ⟨inferInstance,hN⟩
  apply eq_of_le_of_card_ge hle
  have hn := N.card_mul_index
  have hc := (pCore 2 K).card_mul_index
  have hf : N.index = 60 := by
    change Nat.card (K ⧸ N) = 60
    rw [Nat.card_congr f.toEquiv,nat_card_alternatingGroup]
    norm_num
  have he : (pCore 2 K).index = 60 := by
    change Nat.card (K ⧸ pCore 2 K) = 60
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  rw [hf] at hn
  rw [he] at hc
  omega

include D in
/-- The original component cannot have an extraspecial 2-kernel with A5 quotient. -/
theorem source_a5_component_not_extraspecial (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (n : ℕ) :
    ¬ HasExtension L (ExtraspecialModel 2 n) (fun X _ => IsAlternating X 5) := by
  rintro ⟨N,hNN,⟨hN,_⟩,⟨f⟩⟩
  let := hNN
  let := hN
  have he := extension_core e N (IsExtraspecial.isPGroup 2 N) f
  have hlow := source_a5_component_core_center_card D e
  rw [←he,IsExtraspecial.center_order_p 2 N] at hlow
  omega

private theorem cyclic_four_center {H : Type*} [Group H] [Finite H]
    (n : ℕ) (h : CyclicFourCentralProduct n H) :
    IsPGroup 2 H ∧ Nat.card (center H) = 4 := by
  obtain ⟨C,E,⟨eC⟩,⟨hE,_⟩,hgen,hcomm,hoverlap⟩ := h
  let := hE
  let : IsMulCommutative C := IsMulCommutative.of_comm (fun x y => eC.injective (by
    simp only [map_mul,mul_comm]))
  have hCE : C ≤ centralizer (E : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hC : C ≤ center H := by
    have hh : C ⊔ E ≤ centralizer (C : Set H) :=
      sup_le C.le_centralizer (le_centralizer_iff.mp hCE)
    rw [hgen] at hh
    intro c hc
    apply mem_center_iff.mpr
    intro g
    exact (hh (mem_top g) c hc).symm
  have hcent : center H = C :=
    center_eq_of_central_product C E hC hgen (hoverlap ▸ inf_le_left)
  have hcardC : Nat.card C = 4 := by
    rw [Nat.card_congr eC.toEquiv]
    exact Nat.card_zmod 4
  constructor
  · have hp : IsPGroup 2 (C ⊔ E : Subgroup H) :=
      (IsPGroup.of_card (n := 2) hcardC).to_sup_of_normal_right'
        (IsExtraspecial.isPGroup 2 E) (hCE.trans (Subgroup.centralizer_le_normalizer _))
    rw [hgen] at hp
    exact hp.of_equiv topEquiv
  · rw [hcent,hcardC]

include D in
/-- The cyclic-four central-product smaller-group row is impossible. -/
theorem source_a5_component_not_cyclic_four_product (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (n : ℕ) :
    ¬ HasExtension L (CyclicFourCentralProduct n) (fun X _ => IsAlternating X 5) := by
  rintro ⟨N,hNN,hN,⟨f⟩⟩
  let := hNN
  obtain ⟨hp,hc⟩ := cyclic_four_center n hN
  have he := extension_core e N hp f
  have hlow := source_a5_component_core_center_card D e
  rw [←he,hc] at hlow
  omega

include D in
/-- Full movement of the original nonzero module excludes a quasisimple component. -/
theorem source_component_not_quasisimple : ¬ IsQuasisimple L := by
  intro hq
  let := hq
  have hc : ⁅D.fullModule,L⁆ ≤ centralizer (L : Set G) := by
    rintro w hw l hl
    have hwL : w ∈ L := source_full_moved_le_component D hw
    have hwcore : (⟨w,hwL⟩ : L) ∈ pCore 2 L :=
      (mem_map_iff_mem L.subtype_injective).mp (source_full_moved_le_component_core D hw)
    exact congrArg Subtype.val (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 hwcore) ⟨l,hl⟩)
  have hz := commutator_eq_bot_iff_le_centralizer.mpr hc
  rw [source_full_moved_eq_commutator D] at hz
  exact source_full_moved_ne_bot D hz

omit [Finite G] in
private theorem center_le_core (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    center L ≤ pCore 2 L := by
  intro z hz
  apply (QuotientGroup.eq_one_iff z).mp
  apply e.injective
  rw [e.map_one]
  have hc : e (QuotientGroup.mk' (pCore 2 L) z) ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) a
    rw [←hl]
    simpa only [Function.comp_apply,map_mul] using
      congrArg (fun x : L => e (QuotientGroup.mk' (pCore 2 L) x))
        (mem_center_iff.mp hz l)
  rwa [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc

include D in
/-- The 2-core-center lower bound survives every central quotient of the component. -/
theorem source_a5_central_image_core_center_card (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H : Type*} [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center L) : 16 ≤ Nat.card (center (pCore 2 H)) := by
  let W := ⁅D.fullModule,L⁆
  let A := W.subgroupOf L
  have hWL : W ≤ L := source_full_moved_le_component D
  have hmapA : A.map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hA : A.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  let := hA
  let := source_original_full_moved_elementary D
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  have hmove : ⁅A,(⊤ : Subgroup L)⁆ = A := by
    apply map_injective L.subtype_injective
    rw [map_commutator,hmapA,←MonoidHom.range_eq_map,range_subtype]
    exact source_full_moved_eq_commutator D
  have hAne : A ≠ ⊥ := by
    intro h
    have hh := congrArg (map L.subtype) h
    rw [hmapA,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D hh
  have hkp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hker.trans (center_le_core e))
  have hcore : (pCore 2 L).map f = pCore 2 H := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hkp,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  let N := A.map f
  let : N.Normal := hA.map f hf
  have hNp : IsPGroup 2 N := hAp.map f
  have hNcore : N ≤ pCore 2 H := le_sSup ⟨inferInstance,hNp⟩
  have hNc : N ≤ centralizer (pCore 2 H : Set H) := by
    rintro _ ⟨w,hw,rfl⟩ q hq
    rw [←hcore] at hq
    obtain ⟨r,hr,rfl⟩ := hq
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    have hh : w*r=r*w := Subtype.ext
      (source_component_core_centralizes_fullModule D (mem_map_of_mem L.subtype hr)
        w (hWV hw))
    simpa only [map_mul] using congrArg f hh.symm
  have hNmove : ⁅N,(⊤ : Subgroup H)⁆ = N := by
    rw [show (⊤ : Subgroup H) = (⊤ : Subgroup L).map f from
      (map_top_of_surjective _ hf).symm,←map_commutator,hmove]
  have hNnoncentral : ¬ N ≤ center H := by
    intro hn
    have hNzero : N = ⊥ := hNmove.symm.trans
      (commutator_top_right_eq_bot_iff_le_center.mpr hn)
    have hak : A ≤ f.ker := (map_eq_bot_iff A).mp hNzero
    have haz : A ≤ center L := hak.trans hker
    exact hAne (hmove.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr haz))
  let rho : L →* MulAut N := (MulAut.conjNormal : H →* MulAut N).comp f
  have hrho : rho ≠ 1 := by
    intro he
    apply hNnoncentral
    intro n hn
    apply mem_center_iff.mpr
    intro h
    obtain ⟨l,rfl⟩ := hf h
    have hh := congrArg (fun a : MulAut N => (a ⟨n,hn⟩ : H))
      (congrArg (fun r : L →* MulAut N => r l) he)
    change f l*n*(f l)⁻¹=n at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have h16 := alternatingGroup.FiveChiefDegree.sixteen_le_card_of_nontrivial_action
    D.faithful.1.2.1 e rho hrho hNp
  let j : N → center (pCore 2 H) := fun n =>
    ⟨⟨n,hNcore n.property⟩,mem_center_iff.mpr (fun q => Subtype.ext (hNc n.property q q.property))⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : center (pCore 2 H) => ((z : pCore 2 H) : H)) h
  exact h16.trans (Nat.card_le_card_of_injective j hj)

include D in
/-- A central image of the original component cannot be quasisimple. -/
theorem source_central_image_not_quasisimple
    {H : Type*} [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center L) : ¬ IsQuasisimple H := by
  intro hq
  let := hq
  let := Chapter1.mem_L_isPerfect D.maximal.1
  have hcover : PerfectCentralCovering.Cover L H :=
    { toMonoidHom := f, surjective := hf, isPerfect := inferInstance, ker_le_center := hker }
  exact source_component_not_quasisimple D hcover.isQuasisimple

include D in
/-- Small-center 2-kernel extension rows remain impossible after a central quotient. -/
theorem source_a5_central_image_not_small_kernel
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H : Type*} [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center L) (n : ℕ) :
    ¬ (HasExtension H (ExtraspecialModel 2 n) (fun X _ => IsAlternating X 5) ∨
      HasExtension H (CyclicFourCentralProduct n) (fun X _ => IsAlternating X 5)) := by
  have hp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hker.trans (center_le_core e))
  let d : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5) :=
    (f.pCoreQuotientEquiv hf hp).symm.trans e
  have hlow := source_a5_central_image_core_center_card D e f hf hker
  rintro (⟨N,hNN,⟨hN,_⟩,⟨r⟩⟩ | ⟨N,hNN,hN,⟨r⟩⟩)
  · let := hNN
    let := hN
    have he := extension_core d N (IsExtraspecial.isPGroup 2 N) r
    rw [←he,IsExtraspecial.center_order_p 2 N] at hlow
    omega
  · let := hNN
    obtain ⟨hp,hc⟩ := cyclic_four_center n hN
    have he := extension_core d N hp r
    rw [←he,hc] at hlow
    omega

include D in
/-- Actual source consumer: the image of `L` in `I / Z(I)` satisfies all three
restrictions, with no injectivity assumption on the moved module. -/
theorem source_a5_containing_center_quotient_restrictions
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) :
    let B := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
    16 ≤ Nat.card (center (pCore 2 B)) ∧ ¬ IsQuasisimple B ∧
      ∀ n, ¬ (HasExtension B (ExtraspecialModel 2 n) (fun X _ => IsAlternating X 5) ∨
        HasExtension B (CyclicFourCentralProduct n) (fun X _ => IsAlternating X 5)) := by
  let A := L.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change q (inclusion hLI l) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp hh
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  exact ⟨source_a5_central_image_core_center_card D e f hf hk,source_central_image_not_quasisimple D f hf hk,
    source_a5_central_image_not_small_kernel D e f hf hk⟩

end CFSG.Quasithin.Chapter10
