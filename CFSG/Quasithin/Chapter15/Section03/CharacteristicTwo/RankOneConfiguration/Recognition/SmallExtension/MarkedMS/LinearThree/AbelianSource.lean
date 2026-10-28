module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Block
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Literal abelian source sections for C.1.34

The genuine small MS input supplies one or two natural copies after dividing
its actual commutator core by its component-fixed subgroup. Transport along
the inclusion of L ∨ R preserves the projection kernel and conjugation formula.
The fixed-kernel bounds distinguish orders eight, sixteen and sixty-four.
Consequently a single quotient marking realizes the natural section in each
case; the two-copy branch uses the product of that same natural representation.

The order-eight branch proves all of C.1.34(1). The order-sixteen branch keeps
the fixed line and proves its group model and natural quotient, without
identifying it with the order-eight case. The final conditional assembly shows
exactly which source clauses remain: the doubled-natural radical inequality,
and the fixed-line omega-center and literal index-seven stabilizer geometry.
Those geometric implications are not asserted by this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; Meierfrankenfeld–Stellmacher, “Pushing up weak BN-pairs
of rank two”, Communications in Algebra 21 (1993), Main Theorem (4),(5),(8).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- Natural coordinates on the literal quotient of the original MS core by its
fixed subgroup, with one marking for all the natural copies. -/
structure AbelianSourceQuotient (L R : Subgroup G) (m : ℕ) where
  marking : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  projection : msQ L R →* Multiplicative (Fin m → Fin 3 → ZMod 2)
  surjective : Function.Surjective projection
  kernel : projection.ker = (msQ L R ⊓ centralizer (L : Set G)).subgroupOf (msQ L R)
  normalized : L ≤ normalizer (msQ L R)
  equivariant : ∀ (l : L) (x y : msQ L R), (y : G) = l * (x : G) * (l : G)⁻¹ →
    ∀ i, (projection y).toAdd i = specialLinearNatural 3
      (marking (QuotientGroup.mk' (pCore 2 L) l)) ((projection x).toAdd i)

private noncomputable def sourceCoreEquiv (L R : Subgroup G) :
    BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R)) ≃* msQ L R :=
  ((BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))).equivMapOfInjective
    (L ⊔ R).subtype (L ⊔ R).subtype_injective).trans
      (MulEquiv.subgroupCongr (binaryCore_map L R))

private theorem sourceCoreEquiv_val
    (x : BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) :
    (sourceCoreEquiv L R x : G) = ((x : (L ⊔ R : Subgroup G)) : G) := rfl

private theorem sourceCoreEquiv_symm_val (x : msQ L R) :
    (((sourceCoreEquiv L R).symm x : (L ⊔ R : Subgroup G)) : G) = (x : G) := by
  rw [← sourceCoreEquiv_val, MulEquiv.apply_symm_apply]

private noncomputable def binaryFixedEquiv :
    BinaryMS.coreFixed (L.subgroupOf (L ⊔ R)) ≃*
      ↥(msQ L R ⊓ centralizer (L : Set G)) where
  toFun x := ⟨sourceCoreEquiv L R x.val, (sourceCoreEquiv L R x.val).property, by
    intro l hl
    have hx := x.property ⟨l,(show L ≤ L ⊔ R from le_sup_left) hl⟩ hl
    exact congrArg Subtype.val hx⟩
  invFun x := ⟨(sourceCoreEquiv L R).symm ⟨x.val,x.property.1⟩, by
    intro l hl
    apply Subtype.ext
    change (l : G) * (((sourceCoreEquiv L R).symm ⟨x.val, x.property.1⟩ :
      (L ⊔ R : Subgroup G)) : G) =
      (((sourceCoreEquiv L R).symm ⟨x.val, x.property.1⟩ :
      (L ⊔ R : Subgroup G)) : G) * (l : G)
    rw [sourceCoreEquiv_symm_val]
    exact x.property.2 l hl⟩
  left_inv x := by apply Subtype.ext; exact (sourceCoreEquiv L R).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    change (sourceCoreEquiv L R ((sourceCoreEquiv L R).symm ⟨x.val,x.property.1⟩) : G) = x.val
    exact congrArg (fun z : msQ L R => (z : G))
      ((sourceCoreEquiv L R).apply_symm_apply ⟨x.val,x.property.1⟩)
  map_mul' x y := by
    apply Subtype.ext
    change (sourceCoreEquiv L R (x.val * y.val) : G) =
      (sourceCoreEquiv L R x.val : G) * (sourceCoreEquiv L R y.val : G)
    exact congrArg (fun z : msQ L R => (z : G))
      ((sourceCoreEquiv L R).map_mul x.val y.val)

private theorem fixed_normalized : L ≤ normalizer (msQ L R ⊓ centralizer (L : Set G)) := by
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  intro l hl x hx
  exact (hx.2 l hl).symm

variable [Finite G]

private noncomputable def sourceQuotient (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {m : ℕ} (q : BinaryMS.AbelianCore.NaturalQuotient (h.binaryInput e) m) :
    AbelianSourceQuotient L R m where
  marking := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)).symm
    (pCore_map_iso 2 _)).trans q.quotientEquiv
  projection := q.projection.comp (sourceCoreEquiv L R).symm.toMonoidHom
  surjective := q.surjective.comp (sourceCoreEquiv L R).symm.surjective
  kernel := by
    ext x
    change q.projection ((sourceCoreEquiv L R).symm x) = 1 ↔ _
    change (sourceCoreEquiv L R).symm x ∈ q.projection.ker ↔ _
    rw [q.kernel]
    constructor
    · intro hx
      refine ⟨x.property, ?_⟩
      intro l hl
      have hh := congrArg Subtype.val (hx ⟨l,(show L ≤ L ⊔ R from le_sup_left) hl⟩ hl)
      change l * (((sourceCoreEquiv L R).symm x : (L ⊔ R : Subgroup G)) : G) =
        (((sourceCoreEquiv L R).symm x : (L ⊔ R : Subgroup G)) : G) * l at hh
      change l * (x : G) = (x : G) * l
      rwa [sourceCoreEquiv_symm_val] at hh
    · intro hx l hl
      apply Subtype.ext
      change (l : G) * (((sourceCoreEquiv L R).symm x : (L ⊔ R : Subgroup G)) : G) =
        (((sourceCoreEquiv L R).symm x : (L ⊔ R : Subgroup G)) : G) * (l : G)
      rw [sourceCoreEquiv_symm_val]
      exact hx.2 l hl
  normalized := by
    let J := L ⊔ R
    let K := L.subgroupOf J
    let := (h.binaryInput e).component_normal
    have hn : (BinaryMS.commutatorCore K).Normal := inferInstance
    rw [← binaryCore_map L R]
    apply le_trans _ (le_normalizer_map J.subtype)
    intro l hl
    exact ⟨⟨l,(show L ≤ L ⊔ R from le_sup_left) hl⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  equivariant := by
    intro l x y he i
    let l' : L.subgroupOf (L ⊔ R) := (subgroupOfEquivOfLe le_sup_left).symm l
    have hy : (sourceCoreEquiv L R).symm y =
        (h.binaryInput e).coreConjugate l' ((sourceCoreEquiv L R).symm x) := by
      apply Subtype.ext
      rw [(h.binaryInput e).coreConjugate_val]
      apply Subtype.ext
      change (((sourceCoreEquiv L R).symm y : (L ⊔ R : Subgroup G)) : G) =
        (l : G) * (((sourceCoreEquiv L R).symm x : (L ⊔ R : Subgroup G)) : G) * (l : G)⁻¹
      rw [sourceCoreEquiv_symm_val,sourceCoreEquiv_symm_val]
      exact he
    change (q.projection ((sourceCoreEquiv L R).symm y)).toAdd i = _
    rw [hy]
    exact q.equivariant l' _ i

/-- The abelian source provides actual quotient coordinates, exact orders and
block structure in the one-copy branch. The fixed line is not discarded. -/
theorem SmallMSPair.abelian_source_quotient (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) :
    ∃ (m : ℕ) (_q : AbelianSourceQuotient L R m), (m = 1 ∨ m = 2) ∧
      IsElementaryAbelian 2 (msQ L R) ∧
      Nat.card ↥(msQ L R ⊓ centralizer (L : Set G)) ≤ 2 ∧
      (m = 2 → Nat.card ↥(msQ L R ⊓ centralizer (L : Set G)) = 1) ∧
      Nat.card (msQ L R) = 2 ^ (3 * m) * Nat.card ↥(msQ L R ⊓ centralizer (L : Set G)) ∧
      (m = 1 → IsBlock (L.subgroupOf (L ⊔ R)) ∧ IsSL3EvenBlock L 1) := by
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) :=
    ⟨⟨fun a b => (sourceCoreEquiv L R).injective (by simp only [map_mul,mul_comm])⟩⟩
  obtain ⟨m,hm,⟨q⟩⟩ := BinaryMS.AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h.binaryInput e) hc'
  have hk := (h.binaryInput e).abelianCore_fixedKernel_bounds hc' hm q
  have hcK := Nat.card_congr (binaryFixedEquiv (L := L) (R := R)).toEquiv
  have hD := Nat.card_congr (sourceCoreEquiv L R).toEquiv
  refine ⟨m,sourceQuotient h e q,hm,?_,hcK ▸ hk.1,fun h2 => hcK ▸ hk.2 h2,?_,?_⟩
  · let := (h.binaryInput e).abelianCore_elementary_of_naturalQuotient hc' q
    exact IsElementaryAbelian.of_surjective (sourceCoreEquiv L R).toMonoidHom (sourceCoreEquiv L R).surjective
  · rw [← hD,← hcK]
    exact q.card
  · rintro rfl
    have hb := q.block_type hc'
    refine ⟨⟨inferInstance,hb.2.1,h.component.subnormal⟩,?_⟩
    obtain ⟨hp,hs,F,hF,hfin,hcard,hmodel⟩ := hb
    let a : L.subgroupOf (L ⊔ R) ≃* L := subgroupOfEquivOfLe le_sup_left
    exact ⟨hp,hs.of_mulEquiv a,F,hF,hfin,hcard,hmodel.of_mulEquiv a⟩

omit [Finite G] in
private theorem section_of_projection {A V F : Type*} [Group A] [AddCommGroup V]
    [Field F] [Module F V] {K D E : Subgroup G} {a : K →* A}
    {ρ : Representation F A V} (hED : E ≤ D) (hKD : K ≤ normalizer D)
    (hKE : K ≤ normalizer E) (f : D →* Multiplicative V)
    (hf : Function.Surjective f) (hk : f.ker = E.subgroupOf D)
    (ha : ∀ (k : K) (x y : D), (y : G) = k * (x : G) * (k : G)⁻¹ →
      (f y).toAdd = ρ (a k) (f x).toAdd) : HasSectionModel K D E a ρ := by
  have hn : (E.subgroupOf D).Normal := hk ▸ inferInstance
  let := hn
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨hED,hKD,hKE,hn,e,ha⟩

private def singleCoordinates : (Fin 1 → Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := v 0
  invFun v := fun _ => v
  left_inv v := by funext i; exact congrArg v (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def pairCoordinates : (Fin 2 → Fin 3 → ZMod 2) ≃ₗ[ZMod 2]
    ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) where
  toFun v := (v 0,v 1)
  invFun v := ![v.1,v.2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Finite G] in
/-- One natural copy is the actual quotient by the fixed subgroup. -/
theorem AbelianSourceQuotient.single_section (q : AbelianSourceQuotient L R 1) :
    HasSectionModel L (msQ L R) (msQ L R ⊓ centralizer (L : Set G))
      (linearThreeActor q.marking) (specialLinearNatural (k := ZMod 2) 3) := by
  let e := singleCoordinates.toAddEquiv.toMultiplicative
  let f := e.toMonoidHom.comp q.projection
  apply section_of_projection inf_le_left q.normalized fixed_normalized f
    (e.surjective.comp q.surjective)
  · exact (MonoidHom.ker_comp_of_injective q.projection e.toMonoidHom e.injective).trans q.kernel
  · intro l x y hxy
    exact q.equivariant l x y hxy 0

omit [Finite G] in
/-- Trivial fixed subgroup makes the one-copy section the whole natural core. -/
theorem AbelianSourceQuotient.single_whole (q : AbelianSourceQuotient L R 1)
    (hC : msQ L R ⊓ centralizer (L : Set G) = ⊥) :
    HasSectionModel L (msQ L R) ⊥
      (linearThreeActor q.marking) (specialLinearNatural (k := ZMod 2) 3) := by
  simpa only [hC] using q.single_section

omit [Finite G] in
/-- The two coordinates use the same marking, giving the literal product representation. -/
theorem AbelianSourceQuotient.double_whole (q : AbelianSourceQuotient L R 2)
    (hC : msQ L R ⊓ centralizer (L : Set G) = ⊥) :
    HasSectionModel L (msQ L R) ⊥ (linearThreeActor q.marking)
      ((specialLinearNatural (k := ZMod 2) 3).prod (specialLinearNatural 3)) := by
  let e := pairCoordinates.toAddEquiv.toMultiplicative
  let f := e.toMonoidHom.comp q.projection
  apply section_of_projection bot_le q.normalized (by rw [normalizer_eq_top]; exact le_top) f
    (e.surjective.comp q.surjective)
  · rw [MonoidHom.ker_comp_of_injective q.projection e.toMonoidHom e.injective,q.kernel,hC]
  · intro l x y hxy
    exact Prod.ext (q.equivariant l x y hxy 0) (q.equivariant l x y hxy 1)

/-- The three abelian module rows, distinguished by their actual core orders.
The radical inequality and the fixed-line Sylow/stabilizer clauses are separate
source obligations, not consequences of the block assertion alone. -/
theorem SmallMSPair.abelian_source_sections (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      let v := specialLinearNatural (k := ZMod 2) 3
      let a := linearThreeActor e'
      let C := msQ L R ⊓ centralizer (L : Set G)
      (Nat.card (msQ L R) = 8 ∧ IsBlock (L.subgroupOf (L ⊔ R)) ∧
        IsSL3EvenBlock L 1 ∧ HasSectionModel L (msQ L R) ⊥ a v) ∨
      (Nat.card (msQ L R) = 64 ∧ HasSectionModel L (msQ L R) ⊥ a (v.prod v)) ∨
      (Nat.card (msQ L R) = 16 ∧ Nonempty (C ≃* Multiplicative (ZMod 2)) ∧
        HasSectionModel L (msQ L R) C a v) := by
  obtain ⟨m,q,hm,_,hC,hC2,hcard,hblock⟩ := h.abelian_source_quotient e hc
  have hpos : 0 < Nat.card ↥(msQ L R ⊓ centralizer (L : Set G)) := Nat.card_pos
  rcases hm with rfl | rfl
  · refine ⟨q.marking,?_⟩
    by_cases h1 : Nat.card ↥(msQ L R ⊓ centralizer (L : Set G)) = 1
    · exact Or.inl ⟨hcard.trans (by rw [h1]; norm_num), (hblock rfl).1,
        (hblock rfl).2, q.single_whole (Subgroup.card_eq_one.mp h1)⟩
    · have h2 : Nat.card ↥(msQ L R ⊓ centralizer (L : Set G)) = 2 := by omega
      exact Or.inr (Or.inr ⟨hcard.trans (by rw [h2]; norm_num),
        ⟨mulEquivOfPrimeCardEq h2 (Nat.card_zmod 2)⟩, q.single_section⟩)
  · refine ⟨q.marking,Or.inr (Or.inl ⟨?_,q.double_whole (Subgroup.card_eq_one.mp (hC2 rfl))⟩)⟩
    exact hcard.trans (by rw [hC2 rfl]; norm_num)

/-- The order-eight abelian branch satisfies the full source alternative (1). -/
theorem SmallMSPair.abelian_source_of_card_eight (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 8)
    (S : Subgroup G) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e',h8 | h64 | h16⟩ := h.abelian_source_sections e hc
  · exact ⟨e',Or.inl h8.2⟩
  · omega
  · omega

/-- Assembly of all the abelian clauses from the two outstanding geometric
source inputs. These inputs must be discharged before invoking full C.1.34. -/
theorem SmallMSPair.abelian_source_of_geometry (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (S : Subgroup G)
    (h64 : Nat.card (msQ L R) = 64 → MSNotCentralizerCore L R S)
    (h16 : Nat.card (msQ L R) = 16 →
      omegaCenterIn S ≤
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ R) ∧
        MSPointStabilizer L R S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e',h8 | hd | hf⟩ := h.abelian_source_sections e hc
  · exact ⟨e',Or.inl h8.2⟩
  · exact ⟨e',Or.inr (Or.inl ⟨hd.2,h64 hd.1⟩)⟩
  · exact ⟨e',Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨e.trans Matrix.PSL3Two.equiv⟩,hf.2.1,hf.2.2,(h16 hf.1).1,(h16 hf.1).2⟩)))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
