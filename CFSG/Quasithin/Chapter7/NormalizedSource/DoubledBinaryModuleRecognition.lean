module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSmall
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFixedLineBlocks
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorCases

/-!
# Recognizing the full binary moved modules on the doubled branch

The residual four-space projects injectively through the literal B.5
central quotient and retains each Sylow-fixed element. The original
Sylow fixes at least four such elements. Every irreducible binary-three,
four or five source row has at most a fixed line, including the orthogonal
six-space and both exterior ten-spaces. Thus all these irreducible rows
are impossible without any prior recognition of the component as a block.

An embedding before the central projection excludes a single natural
copy in the repeated rows. The full moved space is therefore two equal
natural three-spaces in degree three, and natural--dual or at least two
equal natural copies in degrees four and five. The B.5 actor is the
component in each surviving row. The original central quotient remains
literal throughout; no assertion about all of O₂(K) is inferred.

The Chapter12 companion supplies the original residual, fixed subgroup,
component Sylow and source conclusion without additional hypotheses.
Source: Aschbacher--Smith, proof of 7.7.3 after 7.7.10, printed p.709,
B.4.2/B.5.1, pp.86,99--103, and I.1.6(7), p.408, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryModuleRecognition
open ChapterB.QuasisimpleSource SourceCompletion
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source

private theorem fixed_card_transport
    {D E V W : Type*} [Group D] [Finite D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ) (P : Sylow 2 D)
    (hb : ∀ S : Sylow 2 E, Nat.card (fixedSpace σ (S : Subgroup E)) ≤ 2) :
    Nat.card (fixedSpace ρ (P : Subgroup D)) ≤ 2 := by
  let S := P.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  let f : fixedSpace ρ (P : Subgroup D) → fixedSpace σ (S : Subgroup E) := fun v =>
    ⟨e.linearEquiv v,by
      intro g
      obtain ⟨x,hx,he⟩ := g.property
      change σ g.val (e.linearEquiv v) = e.linearEquiv v
      rw [←he]
      change σ (e.groupEquiv x) (e.linearEquiv v) = e.linearEquiv v
      rw [←e.intertwines]
      exact congrArg e.linearEquiv (v.property ⟨x,hx⟩)⟩
  exact (Nat.card_le_card_of_injective f (fun x y he =>
    Subtype.ext (e.linearEquiv.injective (congrArg Subtype.val he)))).trans (hb S)

/-- Every irreducible binary-four/five B.5 action has a Sylow fixed line at most. -/
theorem irreducible_binary_sylow_fixed_card
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}
    (hir : IsIrreducible (ρ.comp C.subtype)) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hc : BinaryActor.IrreducibleCase ρ C J n) (S : Sylow 2 C) :
    Nat.card (fixedSpace (ρ.comp C.subtype) (S : Subgroup C)) ≤ 2 := by
  cases hc with
  | natural _ a _ =>
    exact fixed_card_transport a S
      (DoubledBinaryFixedLineBlocks.binary_linear_sylow_fixed_card n (by omega))
  | orthogonal _ _ _ a _ _ =>
    exact fixed_card_transport a S DoubledBinaryFixedLineBlocks.eight_sylow_fixed_card
  | symmetricEight _ _ a _ =>
    exact fixed_card_transport (ExtensionConsequences.markedRestriction a) S
      DoubledBinaryFixedLineBlocks.eight_sylow_fixed_card
  | exterior _ _ _ a hd _ _ =>
    let := hir
    have hb := SL5ExteriorSquare.marked_sylow_fixed_finrank_le_one (ρ.comp C.subtype) a hd S
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb).trans_eq (by decide)

variable {G : Type*} [Group G] [Finite G] {K Q : Subgroup G}

omit [Finite G] in
/-- The original residual embeds in the full moved space, before its central quotient. -/
theorem star_moved_embedding_fixed_element
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆) [IsElementaryAbelian 2 X]
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J)) :
    ∃ f : Additive X →ₗ[ZMod 2] s.space.toSubmodule,
      Function.Injective f ∧ ∀ (k : K) (x : Additive X),
        (k : G) * (x.toMul : G) = (x.toMul : G) * k →
        (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype)
          ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k)) (f x) = f x := by
  let U := starV K Q
  let KJ := K.subgroupOf (K ⊔ Q)
  let XJ := ⁅U,KJ⁆
  have hXJ : X ≤ XJ.map (K ⊔ Q : Subgroup G).subtype := by
    rw [hX,map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ Q from le_sup_left)]
    exact commutator_mono hWX hAK
  let j : X →* XJ := {
    toFun x := ⟨⟨x,(map_subtype_le XJ) (hXJ x.property)⟩,by
      obtain ⟨y,hy,he⟩ := hXJ x.property
      exact (Subtype.ext he : y = ⟨x,_⟩) ▸ hy⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : IsElementaryAbelian 2 XJ := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U KJ)) (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel K Q)
  have hs : s.space.toSubmodule = subspaceCommutator (starRepresentation K Q) ⊤ (KJ.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation K Q).comp J.subtype) ⊤
      ((starImage K Q K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  let a := (NormalElementaryQuotient.movedEquiv U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) KJ).trans (LinearEquiv.ofEq _ _ hs.symm)
  let f : Additive X →ₗ[ZMod 2] s.space.toSubmodule :=
    a.toLinearMap.comp (j.toAdditive.toZModLinearMap 2)
  have hf (x : Additive X) : ((f x).val.toMul.val.val : G) = x.toMul.val := rfl
  refine ⟨f,?_,?_⟩
  · intro x y he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : s.space.toSubmodule => (z.val.toMul.val.val : G)) he
  · intro k x hk
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have hh := NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (inclusion (show K ≤ K ⊔ Q from le_sup_left) k) (f x).val
    exact (congrArg Subtype.val hh).trans (by
      change (k : G) * ((f x).val.toMul.val.val : G) * (k : G)⁻¹ = (x.toMul : G)
      rw [hf,hk,mul_inv_cancel_right])

omit [Finite G] in
/-- Transfer fixed elements to the full moved module with its actual action marking. -/
theorem star_moved_fixed_card
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆) [IsElementaryAbelian 2 X]
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J))
    {B V₁ : Type*} [Group B] [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    (σ : Representation (ZMod 2) B V₁)
    (a : ActionEquiv (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype) σ)
    (P : Subgroup K) (Z : Subgroup G) (hZX : Z ≤ X)
    (hZP : Z ≤ centralizer (P.map K.subtype : Set G)) :
    Nat.card Z ≤ Nat.card (fixedSpace σ (P.map (starMovedProjection hCJ a.groupEquiv))) := by
  obtain ⟨j,hj,hfix⟩ := star_moved_embedding_fixed_element W A X hWX hAK hX hCJ s
  let i : Z → Additive X := fun z => Additive.ofMul (inclusion hZX z)
  let u (k : K) := (subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k)
  let g := starMovedProjection hCJ a.groupEquiv
  let f : Z → fixedSpace σ (P.map g) := fun z => ⟨a.linearEquiv (j (i z)),by
    intro k
    obtain ⟨p,hp,he⟩ := k.property
    change σ k.val (a.linearEquiv (j (i z))) = a.linearEquiv (j (i z))
    rw [←he,starMovedProjection_apply,←a.intertwines]
    exact congrArg a.linearEquiv
      (hfix p (i z) (hZP z.property _ (mem_map_of_mem K.subtype hp)))⟩
  exact Nat.card_le_card_of_injective f (by
    intro x y he
    have hh := hj (a.linearEquiv.injective (congrArg Subtype.val he))
    exact Subtype.ext (congrArg (fun z : Additive X => (z.toMul : G)) hh))

private theorem repeated_fixed_card {B V : Type*} [Group B]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) B V) (P : Subgroup B) (r : ℕ) :
    Nat.card (fixedSpace (repeated ρ r) P) ≤ Nat.card (fixedSpace ρ P) ^ r := by
  let f : fixedSpace (repeated ρ r) P → (Fin r → fixedSpace ρ P) :=
    fun v i => ⟨v.val i,fun g => congrFun (v.property g) i⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Nat.card_fun,Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The actual moved module in a binary four/five row is natural--dual or
at least two equal natural copies. No block recognition is an input. -/
theorem binary_moved_module
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (S : Sylow 2 K) (Z : Subgroup G) (hZX : Z ≤ X) (hZcard : 4 ≤ Nat.card Z)
    (hZS : Z ≤ centralizer ((S : Subgroup K).map K.subtype : Set G))
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation K Q).comp J.subtype) ((starImage K Q K).subgroupOf J))
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : starImage K Q K ≃* SL(n,ZMod 2)) :
    (starImage K Q K).subgroupOf J = ⊤ ∧
      (IsNaturalPlusDual (c.sectionData.space.toRepresentation.comp
        ((starImage K Q K).subgroupOf J).subtype) n ∨
      ∃ r : ℕ, 2 ≤ r ∧ r ≤ n-1 ∧
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
          ((starImage K Q K).subgroupOf J).subtype) BinaryField.two n r) := by
  let C := (starImage K Q K).subgroupOf J
  let s := c.sectionData
  let : Finite s.space.toSubmodule := Finite.of_injective
    (fun v : s.space.toSubmodule => (v.val.toMul.val.val : G)) (by
      intro x y he
      exact Subtype.ext (Additive.toMul.injective (Subtype.ext (Subtype.ext he))))
  let : Finite (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
    Finite.of_surjective s.central.toSubmodule.mkQ s.central.toSubmodule.mkQ_surjective
  have hm := BinaryActor.actionCase _ hn ((subgroupOfEquivOfLe hCJ).trans e) c.clause_one
  cases hm with
  | irreducible hi hf hir hc he =>
    let σ := s.action.comp C.subtype
    let a : ActionEquiv σ σ := ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩
    let P := S.mapSurjective (starMovedProjection_surjective hCJ a.groupEquiv)
    have hb := DoubledBinaryStarSmall.star_section_fixed_card W A X hWX hAK hX hdis hCJ
      s σ a (S : Subgroup K) Z hZX hZS
    have hline := irreducible_binary_sylow_fixed_card s.action hir hn hc P
    have hh : Nat.card Z ≤ 2 := hb.trans hline
    omega
  | naturalDual hw hn => exact ⟨hw,Or.inl hn⟩
  | repeatedNatural r hp hr hw hn' =>
    refine ⟨hw,Or.inr ⟨r,?_,hr,hn'⟩⟩
    obtain ⟨a⟩ := hn'
    let P := S.mapSurjective (starMovedProjection_surjective hCJ a.groupEquiv)
    have hb := star_moved_fixed_card W A X hWX hAK hX hCJ s _ a (S : Subgroup K) Z hZX hZS
    have hrep := repeated_fixed_card (linearNatural BinaryField.two n) (P : Subgroup _) r
    have hline := DoubledBinaryFixedLineBlocks.binary_linear_sylow_fixed_card n (by omega) P
    have hh : Nat.card Z ≤ 2 ^ r := hb.trans (hrep.trans (Nat.pow_le_pow_left hline r))
    by_contra hl
    have he : r = 1 := by omega
    rw [he] at hh
    norm_num at hh
    omega

private theorem two_power_divides_binaryThree {n : ℕ} (h : 2 ^ n ∣ 168) : n ≤ 3 := by
  by_contra hn
  have hd : 16 ∣ 2 ^ n := pow_dvd_pow 2 (by omega : 4 ≤ n)
  have hh := hd.trans h
  norm_num at hh

private theorem binaryThree_field_degree (F : BinaryField)
    (hc : Nat.card SL(3,F.Carrier) = 168) : F.degree = 1 := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul,hc] at hd
  have hb := two_power_divides_binaryThree hd
  have hp := F.degree_pos
  omega

private theorem no_binaryThree_linearTwo (F : BinaryField)
    (hc : Nat.card SL(2,F.Carrier) = 168) : False := by
  rw [Atlas.card_sl_two,F.card_eq] at hc
  have hb := two_power_divides_binaryThree (hc ▸ dvd_mul_right (2 ^ F.degree) _)
  have hp := F.degree_pos
  interval_cases he : F.degree <;> norm_num [he] at hc

private theorem no_binaryThree_symplectic (F : BinaryField) (hn : 1 < F.degree)
    (hc : Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) = 168) : False := by
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,←pow_mul,hc] at hd
  have hb := two_power_divides_binaryThree hd
  omega

private theorem no_binaryThree_g2 (F : BinaryField)
    (hc : Nat.card (Atlas.G2.Model F.Carrier) = 168) : False := by
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,←pow_mul,hc] at hd
  have hb := two_power_divides_binaryThree hd
  have hp := F.degree_pos
  omega

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,Matrix.card_GL_field]
  simp

private theorem no_binaryThree_highLinear {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hc : Nat.card SL(n,ZMod 2) = 168) : False := by
  rw [binary_card] at hc
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hc

private theorem no_binaryThree_alternating {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (hc : Nat.card (alternatingGroup (Fin n)) = 168) : False := by
  rcases hn with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hc <;> norm_num [Nat.factorial] at hc

private theorem binaryThree_irreducible_model
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}
    (hc : Nat.card C = 168)
    (hs : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J) :
    ∃ F : BinaryField, F.degree = 1 ∧ IsLinearNatural (ρ.comp C.subtype) F 3 := by
  cases hs with
  | linearTwo F _ a _ _ =>
    exact (no_binaryThree_linearTwo F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
  | linearThree F _ a _ =>
    exact ⟨F,binaryThree_field_degree F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc),⟨a⟩⟩
  | symplectic F hn _ a _ =>
    exact (no_binaryThree_symplectic F hn ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
  | symplecticTwo a _ =>
    exact (no_binaryThree_alternating (Or.inr (Or.inl rfl))
      ((Nat.card_congr (ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv a).groupEquiv.toEquiv).symm.trans hc)).elim
  | g2 F _ _ a _ _ =>
    exact (no_binaryThree_g2 F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
  | g2Two a _ _ =>
    have he := (Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at he
    norm_num at he
  | symmetric n hn a _ _ =>
    exact (no_binaryThree_alternating (hn.imp_right (fun h => Or.inr (Or.inl h)))
      ((Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc)).elim
  | alternatingSix _ a _ _ =>
    exact (no_binaryThree_alternating (Or.inr (Or.inl rfl))
      ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
  | alternatingSeven _ _ a _ _ _ =>
    exact (no_binaryThree_alternating (Or.inr (Or.inr (Or.inl rfl)))
      ((Nat.card_congr a.toEquiv).symm.trans hc)).elim
  | tripleSix _ a _ =>
    rw [card_eq_card_quotient_mul_card_subgroup (center C),
      Nat.card_congr a.quotientEquiv.toEquiv,Nat.card_congr a.centerEquiv.toEquiv,
      nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial,Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear n hn _ a _ =>
    exact (no_binaryThree_highLinear hn ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
  | orthogonalSix _ _ a _ _ =>
    exact (no_binaryThree_alternating (Or.inr (Or.inr (Or.inr rfl)))
      ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
  | symmetricEight _ a _ =>
    exact (no_binaryThree_alternating (Or.inr (Or.inr (Or.inr rfl)))
      ((Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc)).elim
  | exteriorFive _ _ a _ _ _ =>
    exact (no_binaryThree_highLinear (Or.inr rfl) ((Nat.card_congr a.toEquiv).symm.trans hc)).elim

private def fieldCoordinates (F : BinaryField) (f : F.Carrier ≃+* ZMod 2) :
    (Fin 3 → F.Carrier) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v i := f (v i)
  invFun v i := f.symm (v i)
  left_inv v := funext (fun i => f.symm_apply_apply (v i))
  right_inv v := funext (fun i => f.apply_symm_apply (v i))
  map_add' v w := funext (fun i => f.map_add (v i) (w i))
  map_smul' c v := funext (fun i => ZMod.map_smul f.toAddMonoidHom c (v i))

private theorem field_binary_fixed_card (F : BinaryField) (hF : F.degree = 1)
    (P : Sylow 2 SL(3,F.Carrier)) :
    Nat.card (fixedSpace (linearNatural F 3) (P : Subgroup _)) ≤ 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  let f : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,F.card_eq,hF]
    simp)
  let a : ActionEquiv (linearNatural F 3) (linearNatural BinaryField.two 3) := {
    groupEquiv := Atlas.fieldEquivSL 3 f
    linearEquiv := fieldCoordinates F f
    intertwines g v := by
      ext i
      change f (∑ j, g.val i j * v j) = ∑ j, f (g.val i j) * f (v j)
      simp only [map_sum,map_mul] }
  exact fixed_card_transport a P
    (DoubledBinaryFixedLineBlocks.binary_linear_sylow_fixed_card 3 (by decide))

/-- In the binary-three row the full moved space is precisely two equal
natural modules; the one-chief-factor central extension is also excluded. -/
theorem binaryThree_moved_module
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (S : Sylow 2 K) (Z : Subgroup G) (hZX : Z ≤ X) (hZcard : 4 ≤ Nat.card Z)
    (hZS : Z ≤ centralizer ((S : Subgroup K).map K.subtype : Set G))
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation K Q).comp J.subtype) ((starImage K Q K).subgroupOf J))
    (e : starImage K Q K ≃* SL(3,ZMod 2)) :
    (starImage K Q K).subgroupOf J = ⊤ ∧
      ∃ F : BinaryField, F.degree = 1 ∧
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
          ((starImage K Q K).subgroupOf J).subtype) F 3 2 := by
  let C := (starImage K Q K).subgroupOf J
  let s := c.sectionData
  have hc : Nat.card C = 168 := by
    rw [Nat.card_congr ((subgroupOfEquivOfLe hCJ).trans e).toEquiv,binary_card]
    norm_num [Fin.prod_univ_succ]
  cases c.clause_one with
  | irreducible hi hf hir hs he =>
    obtain ⟨F,hF,⟨a⟩⟩ := binaryThree_irreducible_model s.action hc hs
    let P := S.mapSurjective (starMovedProjection_surjective hCJ a.groupEquiv)
    have hb := DoubledBinaryStarSmall.star_section_fixed_card W A X hWX hAK hX hdis hCJ
      s _ a (S : Subgroup K) Z hZX hZS
    have hh : Nat.card Z ≤ 2 := hb.trans (field_binary_fixed_card F hF P)
    omega
  | doubleThree F hw a ho hr =>
    exact ⟨hw,F,binaryThree_field_degree F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc),⟨a⟩⟩
  | naturalDual n hn _ ha =>
    exact (no_binaryThree_highLinear hn ((Nat.card_congr ha.some.groupEquiv.toEquiv).symm.trans hc)).elim
  | repeatedNatural n r hn _ _ _ ha =>
    exact (no_binaryThree_highLinear hn ((Nat.card_congr ha.some.groupEquiv.toEquiv).symm.trans hc)).elim

/-- The full moved-module alternatives, for one fixed B.5 section and actor.
The hypotheses identify the component group; the conclusions identify its
actual action before taking the central quotient. -/
@[expose] def BinaryMovedConclusion
    {J : Subgroup (StarQuotient K Q)}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation K Q).comp J.subtype) ((starImage K Q K).subgroupOf J)) : Prop :=
  (∀ (n : ℕ), (n = 4 ∨ n = 5) →
    (starImage K Q K ≃* SL(n,ZMod 2)) →
    (starImage K Q K).subgroupOf J = ⊤ ∧
      (IsNaturalPlusDual (c.sectionData.space.toRepresentation.comp
        ((starImage K Q K).subgroupOf J).subtype) n ∨
      ∃ r : ℕ, 2 ≤ r ∧ r ≤ n-1 ∧
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
          ((starImage K Q K).subgroupOf J).subtype) BinaryField.two n r)) ∧
  ((starImage K Q K ≃* SL(3,ZMod 2)) →
    (starImage K Q K).subgroupOf J = ⊤ ∧
      ∃ F : BinaryField, F.degree = 1 ∧
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp
          ((starImage K Q K).subgroupOf J).subtype) F 3 2)

/-- Recognize both binary-linear branches using the same residual embedding,
Sylow-fixed subgroup and B.5 section. -/
theorem binary_moved_conclusion
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (S : Sylow 2 K) (Z : Subgroup G) (hZX : Z ≤ X) (hZcard : 4 ≤ Nat.card Z)
    (hZS : Z ≤ centralizer ((S : Subgroup K).map K.subtype : Set G))
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation K Q).comp J.subtype) ((starImage K Q K).subgroupOf J)) :
    BinaryMovedConclusion c :=
  ⟨fun _ hn e => binary_moved_module W A X hWX hAK hX hdis S Z hZX hZcard hZS hCJ c hn e,
    fun e => binaryThree_moved_module W A X hWX hAK hX hdis S Z hZX hZcard hZS hCJ c e⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryModuleRecognition
