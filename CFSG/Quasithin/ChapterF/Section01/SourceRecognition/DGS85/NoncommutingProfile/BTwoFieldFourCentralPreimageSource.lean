module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourComplementsSource
public import Theory.GroupTheory.GaschutzCentralPreimage
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The marked central preimage in the field-four beta enlargement

The original invariant four-groups give a Sylow supplement to the actual
beta core. Gaschütz splits the extension modulo its derived subgroup,
which is the original beta center of order two. Sylow conjugacy chooses
that quotient complement to contain the image of the original cubic
Cartan. Its inverse image has order 120, supplements the beta core, and
intersects it exactly in the original center.

The epimorphism to PSL₂(4) is the restriction of the original starred
quotient marking. The same Cartan and both original invariant four-groups
are retained. The actual intersection with the full Borel two-core is an
order-eight Sylow subgroup of the preimage, normalized by that Cartan.
The enlargement, full Borel two-core and enlargement's Borel have orders
1920, 128 and 384 respectively.

The remaining (5.15) four-group comparison must split this order-eight
Sylow over the central involution. A second Gaschütz application can then
split the central preimage. Full J₂ parabolic recognition and the original
Chapter 10 assembly still require their remaining source arguments.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.15)--(5.16), pp.116--117, and the field-four case of (10.9), p.163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance centralPreimageAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The first source splitting step, with the original Cartan, both invariant
four-groups, the literal order-eight Sylow, and the original quotient map. -/
theorem original_bTwo_field_four_central_preimage
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    let X := enlargedEndpoint L S 1
    let N := pCore 2 X
    let Z₁ := (Z F₀ β).map (G₀ L S).subtype
    Nat.card X = 1920 ∧ Nat.card ((commonBorel L S).pCoreIn 2) = 128 ∧
      Nat.card (X ⊓ commonBorel L S : Subgroup G) = 384 ∧
      ∃ eX : (X ⧸ N) ≃* PSL(2,K),
        (∀ x : L 1, eX (QuotientGroup.mk' N
          (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x)) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x)) ∧
        ∃ (a : commonBorel L S) (A B : Subgroup G) (H : Subgroup X),
          orderOf a = 3 ∧
          (a : G) ∈ centralizer ((Z F₀ α).map (G₀ L S).subtype : Set G) ∧
          Disjoint ((commonBorel L S).pCoreIn 2) (zpowers (a : G)) ∧
          (commonBorel L S).pCoreIn 2 ⊔ zpowers (a : G) = X ⊓ commonBorel L S ∧
          A ≠ B ∧
          (∀ D ∈ ({A,B} : Set (Subgroup G)),
            D ≤ (parabolic L S 0).pCoreIn 2 ∧ Nat.card D = 4 ∧
            IsElementaryAbelian 2 D ∧ Disjoint ((parabolic L S 1).pCoreIn 2) D ∧
            (parabolic L S 1).pCoreIn 2 ⊔ D = (commonBorel L S).pCoreIn 2 ∧
            (a : G) ∈ normalizer (D : Set G)) ∧
          Nat.card H = 120 ∧ (a : G) ∈ H.map X.subtype ∧
          (∃ R : Sylow 2 H, Nat.card R = 8 ∧
            ((R : Subgroup H).map H.subtype).map X.subtype =
              (commonBorel L S).pCoreIn 2 ⊓ H.map X.subtype) ∧
          (a : G) ∈ normalizer
            (((commonBorel L S).pCoreIn 2 ⊓ H.map X.subtype : Subgroup G) : Set G) ∧
          Z₁ ≤ centerIn (H.map X.subtype) ∧
          (parabolic L S 1).pCoreIn 2 ⊓ H.map X.subtype = Z₁ ∧
          (parabolic L S 1).pCoreIn 2 ⊔ H.map X.subtype = X ∧
          ∃ f : H →* PSL(2,K), Function.Surjective f ∧
            f.ker = (Z₁.subgroupOf X).subgroupOf H ∧
            ∀ x : H, f x = eX (QuotientGroup.mk' N (x : X)) := by
  let X := enlargedEndpoint L S 1
  let N := pCore 2 X
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₁ := (Z F₀ β).map (G₀ L S).subtype
  let T := (commonBorel L S).pCoreIn 2
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  have hXP : X ≤ parabolic L S 1 := sup_le (starredParabolic_le 1)
    ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have hX : X = starredParabolic L S 1 := reduced_enlargedEndpoint_eq_starred_of_linear h 1 e
  let j : X ≃* starredParabolic L S 1 := MulEquiv.subgroupCongr hX
  let eX : (X ⧸ N) ≃* PSL(2,K) :=
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans
      ((h.starredQuotientEquiv 1).symm.trans e)
  have heX (x : L 1) : eX (QuotientGroup.mk' N
      (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x)) =
        e (QuotientGroup.mk' (pCore 2 (L 1)) x) := by
    change e ((h.starredQuotientEquiv 1).symm
      (QuotientGroup.mk (inclusion (local_le_starredParabolic 1) x))) = _
    rw [←h.starredQuotientEquiv_mk, MulEquiv.symm_apply_apply]
    rfl
  have hNmap : N.map X.subtype = Q₁ := enlargedEndpoint_core h 1
  let eN : N ≃* Q₁ := (N.equivMapOfInjective X.subtype X.subtype_injective).trans
    (MulEquiv.subgroupCongr hNmap)
  obtain ⟨hExtra,_⟩ := original_bTwo_field_four_beta_recognition h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  let : IsExtraspecial 2 N := IsExtraspecial.of_mulEquiv eN.symm hExtra
  have hNcard : Nat.card N = 32 := by
    rw [Nat.card_congr eN.toEquiv]
    obtain ⟨_,hh⟩ := original_bTwo_exceptional_fields_and_orders h hb c hactor
      hcentral ht hne hcomm hnot e hD E
    rcases hh with ⟨hh,_,_⟩ | ⟨_,_,hh⟩
    · omega
    · exact hh
  have hPSL : Nat.card PSL(2,K) = 60 := by
    let : Fintype K := Fintype.ofFinite K
    have hh := BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1),mul_one,hK] at hh
    exact hh
  have hXcard : Nat.card X = 1920 := by
    have hh := N.index_mul_card
    change Nat.card (X ⧸ N) * Nat.card N = Nat.card X at hh
    rw [Nat.card_congr eX.toEquiv,hPSL,hNcard] at hh
    omega
  obtain ⟨a,ha,hac,haX,hd,hB,A,B,hAB,hABs⟩ :=
    original_bTwo_field_four_invariant_complements h hb c hactor hcentral
      ht hne hcomm hnot e hD E hK
  obtain ⟨hAQ,hAcard,hAe,hNA,hAT,haA⟩ := hABs A (by simp)
  let A₀ := A.subgroupOf X
  have hAX : A ≤ X := (le_sup_right.trans_eq hAT).trans le_sup_right
  let : IsElementaryAbelian 2 A₀ := hAe.subgroupOf hAX
  have hA₀card : Nat.card A₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv).trans hAcard
  have hmapT : (N ⊔ A₀).map X.subtype = T := by
    rw [Subgroup.map_sup,hNmap,map_subgroupOf_eq_of_le hAX,hAT]
  have hdis : Disjoint N A₀ := by
    apply Subgroup.disjoint_def.mpr
    intro x hxN hxA
    apply Subtype.ext
    have hxQ : (x : G) ∈ Q₁ := hNmap ▸ mem_map_of_mem X.subtype hxN
    exact Subgroup.disjoint_def.mp hNA hxQ hxA
  have hS : Nat.card (N ⊔ A₀ : Subgroup X) = 128 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint N A₀ le_normalizer_of_normal hdis,
      hNcard,hA₀card]
  have hScard : Nat.card T = 128 := by
    rw [←hmapT,card_map_of_injective X.subtype_injective,hS]
  have hSindex : (N ⊔ A₀).index = 15 := by
    have hh := (N ⊔ A₀).index_mul_card
    rw [hS,hXcard] at hh
    omega
  have hSp : IsPGroup 2 (N ⊔ A₀ : Subgroup X) := IsPGroup.of_card (n := 7) hS
  let P : Sylow 2 X := hSp.toSylow (by rw [hSindex]; decide)
  let Z₀ := ⁅N,N⁆
  have hZmap : Z₀.map X.subtype = Z₁ := by
    rw [map_commutator,hNmap]
    exact (original_bTwo_beta_core_frattini h hb c hactor hcentral ht hne hcomm).2
  have hZcard : Nat.card Z₀ = 2 := by
    change Nat.card (⁅N,N⁆ : Subgroup X) = 2
    rw [←map_subtype_commutator N,card_map_of_injective N.subtype_injective,
      IsExtraspecial.commutator_eq_center (p := 2),IsExtraspecial.center_order_p 2 N]
  have hZcentral : Z₀ ≤ center X := central_of_normal_card_two Z₀ hZcard
  obtain ⟨C₀,hC₀⟩ := quotient_split_of_elementary_sylow_supplement
    N Z₀ le_rfl (show IsPGroup 2 N from pCore_isPGroup) P A₀ rfl
  let qZ := QuotientGroup.mk' Z₀
  let aX : X := ⟨a,haX⟩
  have haXorder : orderOf aX = 3 :=
    (Subgroup.orderOf_coe aX).symm.trans ((Subgroup.orderOf_coe a).trans ha)
  have haXp : IsPGroup 3 (zpowers aX) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,haXorder]; rfl)
  have hnot3 : ¬ 3 ∣ Nat.card (N.map qZ) := by
    intro hh
    have hd := hh.trans (card_map_dvd N qZ)
    rw [hNcard] at hd
    norm_num at hd
  obtain ⟨C,hC,hCa⟩ := complement_containing_prime_subgroup
    (N.map qZ) C₀ ((zpowers aX).map qZ) hC₀ (haXp.map qZ) hnot3
  obtain ⟨H,hHC,hZH,hNH,hgen,f₀,hf₀,hker,hf₀eq⟩ :=
    exists_preimage_of_quotient_complement N Z₀ N.commutator_le_self C hC
  have haH : aX ∈ H := by
    rw [hHC]
    exact hCa (mem_map_of_mem qZ (mem_zpowers aX))
  let f : H →* PSL(2,K) := eX.toMonoidHom.comp f₀
  have hf : Function.Surjective f := eX.surjective.comp hf₀
  have hkerf : f.ker = Z₀.subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,hker]
  have hHcard : Nat.card H = 120 := by
    have hh := f.ker.index_mul_card
    rw [hkerf,Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv,hZcard] at hh
    have hi : f.ker.index = 60 :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).trans hPSL
    rw [hkerf] at hi
    rw [hi] at hh
    omega
  have hnormalT : commonBorel L S ≤ normalizer (T : Set G) :=
    (commonBorel L S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (commonBorel L S)
        (pCore 2 (commonBorel L S)))
  have hlocalB : Nat.card (X ⊓ commonBorel L S : Subgroup G) = 384 := by
    change Nat.card (enlargedEndpoint L S 1 ⊓ commonBorel L S : Subgroup G) = 384
    rw [←hB,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (zpowers_le.mpr (hnormalT a.property)) hd]
    rw [hScard,Nat.card_zpowers,Subgroup.orderOf_coe,ha]
  let T₀ := N ⊔ A₀
  have hgenI : N ⊔ (H ⊓ T₀) = T₀ := by
    apply le_antisymm (sup_le le_sup_left inf_le_right)
    intro x hxT
    have hx : x ∈ N ⊔ H := hgen ▸ mem_top x
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal] at hx
    obtain ⟨n,hn,y,hy,rfl⟩ := hx
    have hyT : y ∈ T₀ := by
      have hh := T₀.mul_mem (T₀.inv_mem (show n ∈ T₀ from mem_sup_left hn)) hxT
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem_sup hn ⟨hy,hyT⟩
  have hinfI : N ⊓ (H ⊓ T₀) = Z₀ := by
    rw [←inf_assoc,hNH,inf_eq_left.mpr (N.commutator_le_self.trans le_sup_left)]
  have hIcard : Nat.card (H ⊓ T₀ : Subgroup X) = 8 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes N (H ⊓ T₀)
      le_normalizer_of_normal
    rw [hNcard,hinfI,hZcard,hgenI,hS] at hh
    omega
  let R₀ := T₀.subgroupOf H
  have hRcard : Nat.card R₀ = 8 := by
    have hh := card_map_of_injective (f := H.subtype) (K := R₀) H.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm] at hh
    exact hh.symm.trans hIcard
  have hRindex : R₀.index = 15 := by
    have hh := R₀.index_mul_card
    rw [hRcard,hHcard] at hh
    omega
  let R : Sylow 2 H := (IsPGroup.of_card (p := 2) (n := 3) hRcard).toSylow
    (by rw [hRindex]; decide)
  have hRmap : ((R : Subgroup H).map H.subtype).map X.subtype = T ⊓ H.map X.subtype := by
    change (R₀.map H.subtype).map X.subtype = _
    rw [subgroupOf_map_subtype,map_inf _ _ _ X.subtype_injective,hmapT]
  have haHmap : (a : G) ∈ H.map X.subtype := mem_map_of_mem X.subtype haH
  have haR : (a : G) ∈ normalizer ((T ⊓ H.map X.subtype : Subgroup G) : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact and_congr (mem_normalizer_iff.mp (hnormalT a.property) x)
      (mem_normalizer_iff.mp ((H.map X.subtype).le_normalizer haHmap) x)
  have hZ₁sub : Z₁.subgroupOf X = Z₀ := by
    rw [←hZmap]
    exact comap_map_eq_self_of_injective X.subtype_injective Z₀
  refine ⟨hXcard,hScard,hlocalB,eX,heX,a,A,B,H,ha,hac,hd,hB,hAB,hABs,hHcard,
    haHmap,⟨R,hRcard,hRmap⟩,haR,?_,?_,?_,f,hf,?_,?_⟩
  · change Z₁ ≤ centerIn (H.map X.subtype)
    rw [←hZmap]
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨mem_map_of_mem X.subtype (hZH hz),?_⟩
    change (z : G) ∈ centralizer (H.map X.subtype : Set G)
    rw [mem_centralizer_iff]
    rintro _ ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp (hZcentral hz) y)
  · change Q₁ ⊓ H.map X.subtype = Z₁
    rw [←hNmap,←map_inf _ _ _ X.subtype_injective,hNH,hZmap]
  · change Q₁ ⊔ H.map X.subtype = X
    rw [←hNmap,←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map,range_subtype]
  · rw [hkerf,hZ₁sub]
  · intro x
    change eX (f₀ x) = _
    rw [hf₀eq]
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
