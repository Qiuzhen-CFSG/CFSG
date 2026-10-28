module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourCentralPreimageSource
public import Theory.SpecificGroups.PSL3Four.AnisotropicSquareFiber
public import Theory.SpecificGroups.AlternatingFiveInvolutionSplit

/-!
# Splitting the original field-four beta enlargement

The anisotropic adjacent-core intersection exhausts the nontrivial square
fiber of the beta central involution inside the actual UT₃(F₄) alpha core.
Consequently every element of the alpha core in the order-120 central
preimage has square one. The order formula gives at least four elements
in this intersection, so one lies outside the central kernel of order two.

The central A₅ double-cover theorem then shows that the derived subgroup
of that preimage complements its kernel. Mapping this subgroup into the
original beta enlargement gives an order-sixty complement to its actual
two-core. Its PSL₂(4) isomorphism is the restriction of the original quotient
marking. The same cubic Cartan lies in this complement, and both original
invariant four-groups and the full Borel markings are retained.

This proves the second splitting needed for the field-four instance of
DGS (5.16) directly from its already recognized alpha core, without a
general enumeration of the invariant four-groups in (5.15). Matching the
resulting conjugation action with the concrete J₂ endpoint, restoring the
full endpoints and Borel, and completing Chapter 10 remain obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.15)--(5.16), pp.116--117, and (10.9), p.163.
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
local instance splittingSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- All nontrivial square roots of the original beta central involution in
 the alpha core lie in the original beta core. -/
theorem original_bTwo_field_four_square_fiber
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
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let Z₁ := (Z F₀ β).map (G₀ L S).subtype
    ∀ x ∈ Q₀, x ^ 2 ∈ Z₁ → x ^ 2 = 1 ∨ x ∈ Q₁ := by
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₁ := (Z F₀ β).map (G₀ L S).subtype
  let A := Q₁.subgroupOf Q₀
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  obtain ⟨eroot⟩ := original_bTwo_field_four_alpha_root h hb c hactor hcentral
    ht hne hcomm hnot e hD E hK
  obtain ⟨hA,hZ,_,hZA,z,hz,hs⟩ := original_bTwo_field_four_anisotropic_intersection
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨hExtra,_⟩ := original_bTwo_field_four_beta_recognition h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  let : IsExtraspecial 2 Q₁ := hExtra
  have hZmap : (center Q₁).map Q₁.subtype = Z₁ := by
    rw [←IsExtraspecial.commutator_eq_center (p := 2),map_subtype_commutator]
    exact (original_bTwo_beta_core_frattini h hb c hactor hcentral ht hne hcomm).2
  have hZcard : Nat.card Z₁ = 2 := by
    rw [←hZmap,card_map_of_injective Q₁.subtype_injective,
      IsExtraspecial.center_order_p 2 Q₁]
  have hex : ∃ y : Q₀, y ∈ A ∧ y ∉ center Q₀ := by
    by_contra! hn
    have hh := card_le_of_le (show A ≤ center Q₀ from hn)
    rw [hA,hZ] at hh
    omega
  obtain ⟨y,hy,hyn⟩ := hex
  have hzmem : ((z : Q₀) : G) ∈ Z₁ := by
    rw [←hZmap]
    have hh := mem_map_of_mem Q₁.subtype (IsExtraspecial.square_mem_center (⟨y,hy⟩ : Q₁))
    have he : (y : G) ^ 2 = ((z : Q₀) : G) := congrArg Subtype.val (hs y hy hyn)
    exact he ▸ hh
  let z₁ : Z₁ := ⟨((z : Q₀) : G),hzmem⟩
  have hz₁ : z₁ ≠ 1 := by
    intro hh
    have he : ((z : Q₀) : G) = 1 := congrArg (fun v : Z₁ => (v : G)) hh
    exact hz (Subtype.ext (Subtype.ext he))
  obtain ⟨w,hw,hunique⟩ := (Nat.card_eq_two_iff' (1 : Z₁)).mp hZcard
  change ∀ x ∈ Q₀, x ^ 2 ∈ Z₁ → x ^ 2 = 1 ∨ x ∈ Q₁
  intro x hx hxs
  by_cases hxone : x ^ 2 = 1
  · exact Or.inl hxone
  · right
    have he : (⟨x ^ 2,hxs⟩ : Z₁) = z₁ := (hunique _ (by
      intro hh; exact hxone (congrArg Subtype.val hh))).trans (hunique _ hz₁).symm
    have hxsq : (⟨x,hx⟩ : Q₀) ^ 2 = (z : Q₀) :=
      Subtype.ext (congrArg (fun v : Z₁ => (v : G)) he)
    exact Theory.GroupTheory.HyperbolicRecognition.anisotropic_square_fiber_exhausted
      eroot A hA hZA z hz hs ⟨x,hx⟩ hxsq

/-- The actual field-four beta enlargement splits over its two-core.
The complement contains the original Cartan and is identified with PSL₂(4)
by restriction of the original quotient marking. -/
theorem original_bTwo_field_four_split_enlargement
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
    Nat.card X = 1920 ∧ Nat.card ((commonBorel L S).pCoreIn 2) = 128 ∧
      Nat.card (X ⊓ commonBorel L S : Subgroup G) = 384 ∧
      ∃ eX : (X ⧸ N) ≃* PSL(2,K),
        (∀ x : L 1, eX (QuotientGroup.mk' N
          (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x)) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x)) ∧
        ∃ (a : commonBorel L S) (A B : Subgroup G) (C : Subgroup X),
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
          N.IsComplement' C ∧ Nat.card C = 60 ∧ (a : G) ∈ C.map X.subtype ∧
          ∃ eC : C ≃* PSL(2,K),
            ∀ x : C, eC x = eX (QuotientGroup.mk' N (x : X)) := by
  let X := enlargedEndpoint L S 1
  let N := pCore 2 X
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₀ := (Z F₀ α).map (G₀ L S).subtype
  let Z₁ := (Z F₀ β).map (G₀ L S).subtype
  let T := (commonBorel L S).pCoreIn 2
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  have hXP : X ≤ parabolic L S 1 := sup_le (starredParabolic_le 1)
    ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  obtain ⟨hXcard,hTcard,hBcard,eX,heX,a,A,B,H,ha,hac,hd,hB,hAB,hABs,hHcard,
    haH,hR,haR,hZcentral,hNH,hgen,f,hf,hker,hfeq⟩ :=
    original_bTwo_field_four_central_preimage h hb c hactor hcentral
      ht hne hcomm hnot e hD E hK
  obtain ⟨hQcard,hZa,hder,hPhi,hsq⟩ := original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  change Nat.card Q₀ = 64 at hQcard
  change (frattini Q₀).map Q₀.subtype = Z₀ at hPhi
  change Q₁ ⊓ H.map X.subtype = Z₁ at hNH
  change Nat.card X = 1920 at hXcard
  change Nat.card H = 120 at hHcard
  obtain ⟨hExtra,⟨eN⟩⟩ := original_bTwo_field_four_beta_recognition
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let : IsExtraspecial 2 Q₁ := hExtra
  have hZmap : (center Q₁).map Q₁.subtype = Z₁ := by
    rw [←IsExtraspecial.commutator_eq_center (p := 2),map_subtype_commutator]
    exact (original_bTwo_beta_core_frattini h hb c hactor hcentral ht hne hcomm).2
  have hZcard : Nat.card Z₁ = 2 := by
    rw [←hZmap,card_map_of_injective Q₁.subtype_injective,
      IsExtraspecial.center_order_p 2 Q₁]
  have hZ₁H : Z₁ ≤ H.map X.subtype := hZcentral.trans inf_le_left
  have hZ₁X : Z₁ ≤ X := hZ₁H.trans (map_subtype_le H)
  have hZXH : Z₁.subgroupOf X ≤ H := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hZ₁H hx
    exact X.subtype_injective he ▸ hy
  have hkcard : Nat.card f.ker = 2 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hZXH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hZ₁X).toEquiv,hZcard]
  have hkcentral : f.ker ≤ center H := by
    intro x hx
    have hxZ : ((x : X) : G) ∈ Z₁ := by rw [hker] at hx; exact hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hZcentral hxZ).2 y
      (mem_map_of_mem X.subtype y.property)
  have hZQ₁ : Z₀ ≤ Q₁ := hD.symm.le.trans inf_le_left
  have hQ₀T : Q₀ ≤ T := by
    change Q₀ ≤ (commonBorel L S).pCoreIn 2
    rw [original_bTwo_borel_core_eq_product h c]
    exact le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hQ₀X : Q₀ ≤ X := hQ₀T.trans hTX
  let Q := Q₀.subgroupOf X
  let I := Q.subgroupOf H
  have hQ : Nat.card Q = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hQ₀X).toEquiv).trans hQcard
  have hiQ : Q.index = 30 := by
    have hh := Q.index_mul_card
    rw [hQ,hXcard] at hh
    omega
  have hiI : I.index ≤ 30 := by
    have hh := relIndex_le_of_le_right (H := Q) (K := H) (L := ⊤) le_top
      (by rw [relIndex_top_right,hiQ]; decide)
    change Q.relIndex H ≤ 30
    simpa only [relIndex_top_right,hiQ] using hh
  have hIcard : 4 ≤ Nat.card I := by
    have hh := I.card_mul_index
    rw [hHcard] at hh
    nlinarith
  have hIsq : ∀ x ∈ I, x ^ 2 = 1 := by
    intro x hx
    have hxQ : ((x : X) : G) ∈ Q₀ := hx
    let : Fact (IsPGroup 2 Q₀) := ⟨isPGroup_pCoreIn 2 _⟩
    have hxZ₀ : ((x : X) : G) ^ 2 ∈ Z₀ := by
      rw [←hPhi]
      exact mem_map_of_mem Q₀.subtype
        (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x,hxQ⟩ : Q₀))
    have hxZ₁ : ((x : X) : G) ^ 2 ∈ Z₁ := by
      rw [←hNH]
      exact ⟨hZQ₁ hxZ₀,mem_map_of_mem X.subtype (H.pow_mem x.property 2)⟩
    have hxx : ((x : X) : G) ^ 2 = 1 := by
      rcases original_bTwo_field_four_square_fiber h hb c hactor hcentral
        ht hne hcomm hnot e hD E hK x hxQ hxZ₁ with hh | hh
      · exact hh
      · have hxZ : ((x : X) : G) ∈ Z₁ := hNH ▸
          ⟨hh,mem_map_of_mem X.subtype x.property⟩
        exact congrArg Subtype.val (show (⟨((x : X) : G),hxZ⟩ : Z₁) ^ 2 = 1 from
          hZcard ▸ pow_card_eq_one' (x := (⟨((x : X) : G),hxZ⟩ : Z₁)))
    exact Subtype.ext (Subtype.ext hxx)
  have hnotker : ¬ I ≤ f.ker := by
    intro hh
    have hh' := card_le_of_le hh
    rw [hkcard] at hh'
    omega
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hnotker
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hK
  let fA := eA.toMonoidHom.comp f
  have hkerA : fA.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ eA.injective
  have hsplit : f.ker.IsComplement' (commutator H) := by
    have hh := alternatingGroup.central_two_complement_of_involution fA
      (eA.surjective.comp hf) (hkerA ▸ hkcentral) (hkerA ▸ hkcard)
      x (hIsq x hx) (by
        intro he
        exact hxn ((hkerA ▸ show x ∈ fA.ker from he)))
    rwa [hkerA] at hh
  let D := commutator H
  let C := D.map H.subtype
  have hDcard : Nat.card D = 60 := by
    have hh := hsplit.card_mul_card
    change Nat.card f.ker * Nat.card D = Nat.card H at hh
    rw [hkcard,hHcard] at hh
    omega
  have hCcard : Nat.card C = 60 := by
    rw [card_map_of_injective H.subtype_injective]
    exact hDcard
  have hNmap : N.map X.subtype = Q₁ := enlargedEndpoint_core h 1
  have hNcard : Nat.card N = 32 := by
    rw [←card_map_of_injective X.subtype_injective,hNmap]
    exact (Nat.card_congr eN.toEquiv).trans MinusExtraspecial.card_model
  have hdis : Disjoint N C := by
    apply disjoint_def.mpr
    rintro y hyN ⟨z,hz,rfl⟩
    have hzker : z ∈ f.ker := by
      change f z = 1
      rw [hfeq]
      have he : QuotientGroup.mk' N (z : X) = 1 := (QuotientGroup.eq_one_iff _).mpr hyN
      rw [he,map_one]
    exact congrArg Subtype.val (disjoint_def.mp hsplit.disjoint hzker hz)
  have hNC : N.IsComplement' C := isComplement'_of_card_mul_and_disjoint
    (by rw [hNcard,hCcard,hXcard]) hdis
  obtain ⟨aH,haHmem,haHeq⟩ := haH
  change (aH : G) = (a : G) at haHeq
  let a₀ : H := ⟨aH,haHmem⟩
  have ha₀ : a₀ ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((aH : X) : G) ^ 3 = 1
    rw [haHeq]
    exact congrArg (fun y : commonBorel L S => (y : G)) (ha ▸ pow_orderOf_eq_one a)
  have haD : a₀ ∈ D := by
    have hiD : D.index = 2 := hsplit.index_eq_card.trans hkcard
    have hsqD := D.pow_index_mem a₀
    rw [hiD] at hsqD
    have hh := D.pow_mem hsqD 2
    have hfour : (a₀ ^ 2) ^ 2 = a₀ := by
      rw [←pow_mul,show 2*2=3+1 from rfl,pow_succ,ha₀,one_mul]
    exact hfour ▸ hh
  have haC : (a : G) ∈ C.map X.subtype := by
    rw [←haHeq]
    exact mem_map_of_mem X.subtype (mem_map_of_mem H.subtype haD)
  let fC : C →* PSL(2,K) := eX.toMonoidHom.comp ((QuotientGroup.mk' N).comp C.subtype)
  have hfCi : Function.Injective fC := by
    apply (MonoidHom.ker_eq_bot_iff fC).mp
    apply bot_unique
    intro y hy
    have hqy : QuotientGroup.mk' N (y : X) = 1 := eX.injective (by simpa [fC] using hy)
    exact Subtype.ext (disjoint_def.mp hdis ((QuotientGroup.eq_one_iff _).mp hqy) y.property)
  have hPSL : Nat.card PSL(2,K) = 60 := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let eC := MulEquiv.ofBijective fC ((Nat.bijective_iff_injective_and_card fC).mpr
    ⟨hfCi,hCcard.trans hPSL.symm⟩)
  exact ⟨hXcard,hTcard,hBcard,eX,heX,a,A,B,C,ha,hac,hd,hB,hAB,hABs,
    hNC,hCcard,haC,eC,fun _ => rfl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
