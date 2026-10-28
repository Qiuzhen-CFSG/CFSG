module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSix
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySixSpaceBlocks

/-!
# Small star components on the actual doubled orbit

The residual sixteen embeds in the literal B.5 moved section modulo its
central fixed space. The embedding preserves every individually fixed element,
so the original Sylow-fixed subgroup also embeds. An abstract action transport
keeps this argument independent of the nested star-quotient instances.

For an A₇ or G₂(2)′ star component, comparison with the full B.5 catalogue
leaves the natural A₇ six-space, exceptional A₇ four-space, or natural derived
G₂ six-space. Their fixed-space bounds contradict, respectively, the original
Q-fixed sixteen, faithfulness, or the original Sylow-fixed subgroup of order
at least four. The component Sylow is selected inside the original local Sylow.
No whole-component block recognition or vanishing quotient kernel is assumed.

The Chapter12 companion applies these exclusions to the same chosen seed and
paired plane. Source: Aschbacher--Smith, elimination after 7.7.10, printed p.709,
and B.4.2/B.5.1, printed pp.86 and99--103, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSmall
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterC.C27Source
private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem two_power_bound {k : ℕ} (h : 2 ^ k ∣ 2520 ∨ 2 ^ k ∣ 6048) : k ≤ 5 := by
  by_contra hk
  have hp : 64 ∣ 2 ^ k := pow_dvd_pow 2 (by omega : 6 ≤ k)
  rcases h with h | h
  · have := hp.trans h; norm_num at this
  · have := hp.trans h; norm_num at this

private theorem no_linearTwo {E : Type*} [Group E]
    (hE : Nat.card E = 2520 ∨ Nat.card E = 6048)
    (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : False := by
  have hc : Nat.card SL(2,F.Carrier) = 2520 ∨ Nat.card SL(2,F.Carrier) = 6048 := by
    rwa [Nat.card_congr e.toEquiv] at hE
  rw [GorensteinWalter.sl2_card_formula,F.card_eq] at hc
  have hd : F.degree ≤ 5 := two_power_bound (by
    rcases hc with hc | hc
    · exact Or.inl (hc ▸ dvd_mul_right (2 ^ F.degree) _)
    · exact Or.inr (hc ▸ dvd_mul_right (2 ^ F.degree) _))
  have hp := F.degree_pos
  interval_cases he : F.degree <;> norm_num [he] at hc

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq,h]
    simp)

private theorem no_linearThree {E : Type*} [Group E]
    (hE : Nat.card E = 2520 ∨ Nat.card E = 6048)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = 2520 ∨ Nat.card SL(3,F.Carrier) = 6048 := by
    rwa [Nat.card_congr e.toEquiv] at hE
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul] at hd
  have hb := two_power_bound (k := F.degree * 3) (by rcases hc with hc | hc <;> simp_all)
  have he : F.degree = 1 := by have := F.degree_pos; omega
  have hh := Nat.card_congr (Atlas.fieldEquivSL 3 (fieldTwoEquiv F he)).toEquiv
  rw [binary_card] at hh
  norm_num [Fin.prod_univ_succ] at hh
  rcases hc with hc | hc <;> omega

private theorem no_symplectic {E : Type*} [Group E]
    (hE : Nat.card E = 2520 ∨ Nat.card E = 6048)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hc : Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) = 2520 ∨
      Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) = 6048 := by
    rwa [Nat.card_congr e.toEquiv] at hE
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,← pow_mul] at hd
  have hb := two_power_bound (k := F.degree * 4) (by rcases hc with hc | hc <;> simp_all)
  omega

private theorem no_g2 {E : Type*} [Group E]
    (hE : Nat.card E = 2520 ∨ Nat.card E = 6048)
    (F : BinaryField) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hc : Nat.card (Atlas.G2.Model F.Carrier) = 2520 ∨
      Nat.card (Atlas.G2.Model F.Carrier) = 6048 := by
    rwa [Nat.card_congr e.toEquiv] at hE
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,← pow_mul] at hd
  have hb := two_power_bound (k := F.degree * 6) (by rcases hc with hc | hc <;> simp_all)
  have := F.degree_pos
  omega

private theorem no_binaryLinear {E : Type*} [Group E]
    (hE : Nat.card E = 2520 ∨ Nat.card E = 6048)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  rw [Nat.card_congr e.toEquiv,binary_card] at hE
  rcases hd with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hE

private theorem no_other_alternating {E : Type*} [Group E]
    (hE : Nat.card E = 2520 ∨ Nat.card E = 6048)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) (e : E ≃* alternatingGroup (Fin n)) : False := by
  rw [Nat.card_congr e.toEquiv] at hE
  rcases hn with rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hE <;> norm_num [Nat.factorial] at hE

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

private theorem irreducible_models
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (hc : Nat.card C = 2520 ∨ Nat.card C = 6048) :
    Nonempty (ActionEquiv (ρ.comp C.subtype) (alternatingNatural 7)) ∨
    Module.finrank (ZMod 2) V = 4 ∨
    Nonempty (ActionEquiv (ρ.comp C.subtype) (g2DerivedNatural (ZMod 2))) := by
  cases h with
  | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
  | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
  | symplectic F hn _ a _ => exact (no_symplectic hc F hn a.groupEquiv).elim
  | symplecticTwo a _ =>
    exact (no_other_alternating hc (Or.inr (Or.inl rfl))
      (ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv a).groupEquiv).elim
  | g2 F _ _ a _ _ => exact (no_g2 hc F a.groupEquiv).elim
  | g2Two a _ _ => exact Or.inr (Or.inr ⟨ExtensionConsequences.markedRestriction a⟩)
  | symmetric n hn a _ _ =>
    rcases hn with rfl | rfl
    · exact (no_other_alternating hc (Or.inl rfl) a.subgroupEquiv).elim
    · exact Or.inl ⟨ExtensionConsequences.markedRestriction a⟩
  | alternatingSix _ a _ _ =>
    exact (no_other_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ _ hd _ _ => exact Or.inr (Or.inl hd)
  | tripleSix _ a _ =>
    rw [card_eq_card_quotient_mul_card_subgroup (center C),
      Nat.card_congr a.quotientEquiv.toEquiv,Nat.card_congr a.centerEquiv.toEquiv,
      nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.groupEquiv).elim
  | symmetricEight _ a _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim

private theorem source_models
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hc : Nat.card C = 2520 ∨ Nat.card C = 6048) :
    Function.Injective c.sectionData.action ∧
      (Nonempty (ActionEquiv (c.sectionData.action.comp C.subtype) (alternatingNatural 7)) ∨
      Module.finrank (ZMod 2) (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 4 ∨
      Nonempty (ActionEquiv (c.sectionData.action.comp C.subtype) (g2DerivedNatural (ZMod 2)))) := by
  cases c.clause_one with
  | irreducible _ hf _ hs _ => exact ⟨hf,irreducible_models _ hs hc⟩
  | doubleThree F _ a _ _ => exact (no_linearThree hc F a.groupEquiv).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear hc hd a.groupEquiv).elim

section Star
variable {G : Type*} [Group G] [Finite G] {H K Q M : Subgroup G}

omit [Finite G] in
/-- The residual four-space projects injectively into the actual central
quotient of the B.5 moved section, preserving every individually fixed element. -/
theorem star_section_embedding_fixed_element
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J)) :
    ∃ f : Additive X →ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule),
      Function.Injective f ∧ ∀ (k : K) (x : Additive X),
        (k : G) * (x.toMul : G) = (x.toMul : G) * k → (s.action.comp ((starImage K Q K).subgroupOf J).subtype)
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
  let f0 : Additive X →ₗ[ZMod 2] s.space.toSubmodule :=
    a.toLinearMap.comp (j.toAdditive.toZModLinearMap 2)
  have hf0 (x : Additive X) : ((f0 x).val.toMul.val.val : G) = x.toMul.val := rfl
  let f := s.central.toSubmodule.mkQ.comp f0
  have hfix (k : K) (x : Additive X) :
      (((s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm
        (toStarImage K Q k)) : J) (f0 x)).val).toMul.val.val : G) =
        (k : G) * (x.toMul : G) * (k : G)⁻¹ := by
    have hh := NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (inclusion (show K ≤ K ⊔ Q from le_sup_left) k) (f0 x).val
    exact congrArg Subtype.val hh
  refine ⟨f,?_,?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    have hc : f0 x ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hx
    rw [s.central_eq] at hc
    have hxC : (x.toMul : G) ∈ centralizer (A : Set G) := by
      intro b hb
      have hh := congrArg (fun v : s.space.toSubmodule => (v.val.toMul.val.val : G))
        (hc ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q ⟨b,hAK hb⟩)))
      change (((s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm
        (toStarImage K Q ⟨b,hAK hb⟩)) : J) (f0 x)).val).toMul.val.val : G) =
        ((f0 x).val.toMul.val.val : G) at hh
      rw [hfix,hf0] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hh := (disjoint_iff.mp hdis).le ⟨x.toMul.property,hxC⟩
    apply Additive.toMul.injective
    exact Subtype.ext (mem_bot.mp hh)
  · intro k x hk
    have he : s.space.toRepresentation (((subgroupOfEquivOfLe hCJ).symm
        (toStarImage K Q k)) : J) (f0 x) = f0 x := by
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (hfix k x).trans (by rw [hk,mul_inv_cancel_right]; rfl)
    exact congrArg s.central.toSubmodule.mkQ he

/-- The half-Sylow index on H restricts to the original full component. -/
theorem component_sylow_inside
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (P : Sylow 2 H) (hi : (Q.subgroupOf H).relIndex (P : Subgroup H) ≤ 2) :
    ∃ S : Sylow 2 K, (Q.subgroupOf K).relIndex (S : Subgroup K) ≤ 2 ∧
    (S : Subgroup K).map K.subtype ≤ (P : Subgroup H).map H.subtype := by
  let C := K.subgroupOf H
  let e : C ≃* K := subgroupOfEquivOfLe h.component.1
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C h.component.2.subnormal
  have he : ((Q.subgroupOf H).subgroupOf C).map e.toMonoidHom = Q.subgroupOf K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x,h.component.1 x.property⟩,x.property⟩,hx,rfl⟩
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_,?_⟩
  · change (Q.subgroupOf K).relIndex ((S : Subgroup C).map e.toMonoidHom) ≤ 2
    rw [←he,relIndex_map_map_of_injective _ _ e.injective,hS,
      ←inf_subgroupOf_right (P : Subgroup H) C,
      relIndex_subgroupOf (show (P : Subgroup H) ⊓ C ≤ C from inf_le_right)]
    exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hi

  · rintro _ ⟨k,⟨c,hc,rfl⟩,rfl⟩
    refine ⟨(c : H),?_,rfl⟩
    change c ∈ (S : Subgroup C) at hc
    rw [hS] at hc
    exact hc

private theorem fixed_card_of_embedding
    {D E V X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) E V) (g : D →* E) (f : X → V)
    (hf : Function.Injective f) (P : Subgroup D)
    (hfix : ∀ p ∈ P, ∀ x, σ (g p) (f x) = f x) :
    Nat.card X ≤ Nat.card (fixedSpace σ (P.map g)) := by
  let j : X → fixedSpace σ (P.map g) := fun x => ⟨f x,by
    intro k
    obtain ⟨p,hp,he⟩ := k.property
    change σ k.val (f x) = f x
    rw [←he]
    exact hfix p hp x⟩
  exact Nat.card_le_card_of_injective j (fun x y he => hf (congrArg Subtype.val he))

private theorem fixed_card_of_model_embedding
    {D E B X V W : Type*} [Group D] [Group E] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E V) (σ : Representation (ZMod 2) B W)
    (a : ActionEquiv ρ σ) (g : D →* B) (u : D → E)
    (hu : ∀ k, g k = a.groupEquiv (u k))
    (j : X → V) (hj : Function.Injective j) (P : Subgroup D)
    (hfix : ∀ k ∈ P, ∀ x, ρ (u k) (j x) = j x) :
    Nat.card X ≤ Nat.card (fixedSpace σ (P.map g)) := by
  apply fixed_card_of_embedding σ g (a.linearEquiv ∘ j) (a.linearEquiv.injective.comp hj) P
  intro k hk x
  dsimp only [Function.comp_apply]
  rw [hu,←a.intertwines,hfix k hk]

omit [Finite G] in
/-- Fixed elements of any subgroup of the original residual retain their
fixedness in the literal central quotient, with its actual model marking. -/
theorem star_section_fixed_card
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J))
    {B V₁ : Type*} [Group B] [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    (σ : Representation (ZMod 2) B V₁)
    (a : ActionEquiv (s.action.comp ((starImage K Q K).subgroupOf J).subtype) σ)
    (P : Subgroup K) (Z : Subgroup G) (hZX : Z ≤ X)
    (hZP : Z ≤ centralizer (P.map K.subtype : Set G)) :
    Nat.card Z ≤ Nat.card (fixedSpace σ (P.map (starMovedProjection hCJ a.groupEquiv))) := by
  obtain ⟨j,hj,hfix⟩ := star_section_embedding_fixed_element
    (K := K) (Q := Q) (J := J) W A X hWX hAK hX hdis hCJ s
  let i : Z → Additive X := fun z => Additive.ofMul (inclusion hZX z)
  have hi : Function.Injective i := fun x y he =>
    Subtype.ext (congrArg (fun z : Additive X => (z.toMul : G)) he)
  exact fixed_card_of_model_embedding
    (s.action.comp ((starImage K Q K).subgroupOf J).subtype) σ a
    (starMovedProjection hCJ a.groupEquiv)
    (fun k => (subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k))
    (starMovedProjection_apply hCJ a.groupEquiv) (j ∘ i) (hj.comp hi) P
    (fun k hk z => hfix k (i z) (hZP z.property _ (mem_map_of_mem K.subtype hk)))

private theorem eq_one_of_fixes_surjection
    {D E V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (j : E → V) (hj : Function.Surjective j) (k : D)
    (hk : ∀ x, ρ k (j x) = j x) : k = 1 := by
  apply hf
  apply LinearMap.ext
  intro v
  obtain ⟨x,hx⟩ := hj v
  rw [←hx,hk,map_one]
  rfl

private theorem small_section_contradiction
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 16) (hQfix : X ≤ centralizer (Q : Set G))
    (S : Sylow 2 K) (hindex : (Q.subgroupOf K).relIndex (S : Subgroup K) ≤ 2)
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J))
    (hf : Function.Injective s.action)
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
    (heven : Even (Nat.card (starImage K Q K))) : False := by
  obtain ⟨j,hj,hfix⟩ := DoubledBinaryStarSix.star_section_embedding
    (K := K) (Q := Q) (J := J) W A X hWX hAK hX hdis hCJ s
  have hc : Nat.card (s.space.toSubmodule ⧸ s.central.toSubmodule) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  let : Finite (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  have hjs : Function.Surjective j :=
    (hj.bijective_of_nat_card_le (by rw [hc,Nat.card_congr Additive.toMul,hcard])).surjective
  let g := toStarImage K Q
  have hQker : Q.subgroupOf K ≤ g.ker := by
    intro k hk
    have hh : (((subgroupOfEquivOfLe hCJ).symm (g k)) : J) = 1 := by
      exact eq_one_of_fixes_surjection s.action hf j hjs _
        (hfix k (le_centralizer_iff.mp hQfix hk))
    have hz : (subgroupOfEquivOfLe hCJ).symm (g k) = 1 := Subtype.ext hh
    change g k = 1
    simpa only [MulEquiv.apply_symm_apply,map_one] using congrArg (subgroupOfEquivOfLe hCJ) hz
  let P := S.mapSurjective (toStarImage_surjective K Q)
  have hsmall : Nat.card P ≤ 2 := by
    change Nat.card ((S : Subgroup K).map g) ≤ 2
    rw [←relIndex_ker]
    exact (relIndex_le_of_le_left hQker index_ne_zero_of_finite).trans hindex
  let : (K.subgroupOf (K ⊔ Q)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let : IsQuasisimple (starImage K Q K) := (star_fitting_quasisimple (source_join_input h)).2
  exact (not_lt_of_ge hsmall) (perfect_sylow_two_card_gt_two P heven)

private theorem seven_natural_fixed_card (P : Sylow 2 (alternatingGroup (Fin 7)))
    (B : Subgroup (alternatingGroup (Fin 7))) (hi : B.relIndex (P : Subgroup _) ≤ 2) :
    Nat.card (fixedSpace (alternatingNatural 7) B) ≤ 8 := by
  let a : ActionEquiv (BinaryPermutation.alternatingCoreRepresentation (Fin 7))
      (alternatingNatural 7) := {
    groupEquiv := MulEquiv.refl _
    linearEquiv := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
    intertwines := fun g v => BinaryPermutation.coreEquivNatural_equivariant (Fin 7) (by decide) g v }
  let f : fixedSpace (alternatingNatural 7) B →
      fixedSpace (BinaryPermutation.alternatingCoreRepresentation (Fin 7)) B := fun v =>
    ⟨a.linearEquiv.symm v,by
      intro g
      apply a.linearEquiv.injective
      change a.linearEquiv (BinaryPermutation.alternatingCoreRepresentation (Fin 7) g.val _) = _
      rw [a.intertwines,a.linearEquiv.apply_symm_apply]
      exact v.property g⟩
  exact (Nat.card_le_card_of_injective f (fun x y he =>
    Subtype.ext (a.linearEquiv.symm.injective (congrArg Subtype.val he)))).trans
      (DoubledBinarySixSpaceBlocks.seven_half_sylow_fixed_card P B hi)

/-- Neither A₇ nor G₂(2)′ can be the actual star component: the original
residual sixteen and its Sylow-fixed four contradict every B.5 action row. -/
theorem no_small_star
    (h : Input KnownSimple.IsKnownSimple H Q M K)
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 16) (hQfix : X ≤ centralizer (Q : Set G))
    (S : Sylow 2 K) (hindex : (Q.subgroupOf K).relIndex (S : Subgroup K) ≤ 2)
    (Z : Subgroup G) (hZX : Z ≤ X) (hZcard : 4 ≤ Nat.card Z)
    (hZS : Z ≤ centralizer ((S : Subgroup K).map K.subtype : Set G))
    (hmodel : Nonempty (starImage K Q K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (starImage K Q K ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  have hc : Nat.card (starImage K Q K) = 2520 ∨ Nat.card (starImage K Q K) = 6048 := by
    rcases hmodel with h7 | hg2
    · obtain ⟨e⟩ := h7
      left
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · obtain ⟨e⟩ := hg2
      right
      rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  obtain ⟨hf,hm⟩ := source_models _ c (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCJ).toEquiv]; exact hc)
  rcases hm with hm | hd | hm
  · obtain ⟨a⟩ := hm
    let g := starMovedProjection hCJ a.groupEquiv
    let P := S.mapSurjective (starMovedProjection_surjective hCJ a.groupEquiv)
    have hi : ((Q.subgroupOf K).map g).relIndex (P : Subgroup _) ≤ 2 := by
      change ((Q.subgroupOf K).map g).relIndex ((S : Subgroup K).map g) ≤ 2
      rw [←relIndex_comap]
      exact (relIndex_le_of_le_left (le_comap_map g _) index_ne_zero_of_finite).trans hindex
    have hb := star_section_fixed_card (K := K) (Q := Q) W A X hWX hAK hX hdis hCJ
      c.sectionData _ a (Q.subgroupOf K) X le_rfl
      (hQfix.trans (centralizer_le (by
        rw [subgroupOf_map_subtype]; exact inf_le_left)))
    have hh := hb.trans (seven_natural_fixed_card P _ hi)
    rw [hcard] at hh
    omega
  · apply small_section_contradiction h W A X hWX hAK hX hdis hcard hQfix S hindex hCJ c.sectionData hf hd
    rcases hc with hc | hc <;> rw [hc] <;> decide
  · obtain ⟨a⟩ := hm
    let : Finite (Atlas.G2.Natural.Space (ZMod 2)) := Finite.of_injective
      (Atlas.G2.Natural.binaryCoordinates (ZMod 2))
      (Atlas.G2.Natural.binaryCoordinates_injective (ZMod 2))
    let P := S.mapSurjective (starMovedProjection_surjective hCJ a.groupEquiv)
    have hb := star_section_fixed_card (K := K) (Q := Q) W A X hWX hAK hX hdis hCJ
      c.sectionData _ a (S : Subgroup K) Z hZX hZS
    have hh := hb.trans (Atlas.G2.Natural.BinarySylowFixedSpace.card_derived_sylow_fixed_le_two P)
    omega
end Star

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSmall
