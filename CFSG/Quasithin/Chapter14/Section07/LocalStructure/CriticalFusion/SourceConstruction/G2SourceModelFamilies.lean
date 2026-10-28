module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceModels
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceFamilies
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The model family on the original critical actors

The octonion family calculation is transported through the actual equivariant
marking of the original binary conjugation section. Cyclic subgroup images
are the corresponding one-dimensional vector spans. This proves the linear
family premise of `source_common_family` rather than postulating that premise.

The derived actor is lifted inside the same critical partner and the polar
space is lifted inside the original U. Their images are proved to be exactly
the model subgroups and subspace. Under the critical-actor identification and
the point noncontainment, the resulting ambient families coincide. Nonzero
members have order four, and their extensions by the flag point are actual
lines on the literal U/V₁ quotient.

The critical-actor identification and noncontainment remain explicit here;
they are the still-unfinished 14.7.61–62 obligations of this source branch.
These lemmas do not assert the complete G₂ residual exclusion.

Source: Aschbacher–Smith 14.7.55(4),(8), 14.7.62 and formulas (a)–(d),
printed pp.1066,1068–1069. Concrete model calculations retain the ATLAS
attribution in LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
open MarkedPencil MarkedPencil.Actors

universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)

/-- The original coordinate image of a cyclic subgroup is its vector span. -/
theorem imageSpace_zpowers (w : F.U) :
    c.imageSpace (zpowers (w : G)) = (ZMod 2) ∙ (c.coordinates w).toAdd := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := (c.mem_imageSpace_iff _ _).mp hx
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hv
    have he : w ^ n = v := Subtype.ext hn
    rw [← he,map_zpow]
    change n • (c.coordinates w).toAdd ∈ _
    exact AddSubgroup.zsmul_mem ((ZMod 2) ∙ (c.coordinates w).toAdd).toAddSubgroup
      (Submodule.mem_span_singleton_self _) _
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (c.mem_imageSpace_iff _ _).mpr ⟨w,mem_zpowers _,rfl⟩

private theorem subgroupOf_zpowers (b : F.H) :
    (zpowers (b : G)).subgroupOf F.H = zpowers b := by
  apply Subgroup.map_injective F.H.subtype_injective
  rw [map_subgroupOf_eq_of_le (zpowers_le.mpr b.property),MonoidHom.map_zpowers]
  rfl

/-- The two recognized models satisfy the same pencil-family identity. -/
theorem model_commutator_families (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) :
    {S | ∃ b ∈ derivedCentralizer m.singularMap m.action p,
      S = subspaceCommutator m.action ⊤ (zpowers b)} =
    {S | ∃ w ∈ perpendicular m.singularMap p,
      S = subspaceCommutator m.action ((ZMod 2) ∙ w)
        (fullCentralizer m.singularMap m.action p)} := by
  cases m with
  | natural => exact Families.natural_commutator_families p
  | weyl => exact Families.weyl_commutator_families p

theorem cyclic_commutator_model_image
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (θ : F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (θ a) v) = ρ a (E v)) (b : F.H) :
    subspaceCommutator ρ ⊤ ((zpowers (b : G)).subgroupOf F.H) =
      (subspaceCommutator m.action ⊤ (zpowers (θ b))).map E.toLinearMap := by
  have hh := subspaceCommutator_map_embedding ρ m.action θ E.toLinearMap
    (fun a v => (he a v).symm) (zpowers b) ⊤
  rw [Submodule.map_top,LinearEquiv.range,MonoidHom.map_zpowers] at hh
  rw [subgroupOf_zpowers]
  exact hh

theorem linear_families_of_model
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (θ : F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (θ a) v) = ρ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (A B R : Subgroup G) (hBH : B ≤ F.H) (hRU : R ≤ F.U)
    (hA : (A.subgroupOf F.H).map θ = fullCentralizer m.singularMap m.action p)
    (hB : (B.subgroupOf F.H).map θ = derivedCentralizer m.singularMap m.action p)
    (hR : c.imageSpace R = (perpendicular m.singularMap p).map E.toLinearMap) :
    {P | ∃ b ∈ B, P = subspaceCommutator ρ ⊤ ((zpowers b).subgroupOf F.H)} =
    {P | ∃ w ∈ R, P = subspaceCommutator ρ (c.imageSpace (zpowers w))
      (A.subgroupOf F.H)} := by
  have left (b : F.H) : subspaceCommutator ρ ⊤ ((zpowers (b : G)).subgroupOf F.H) =
      (subspaceCommutator m.action ⊤ (zpowers (θ b))).map E.toLinearMap := by
    exact cyclic_commutator_model_image m E θ he b
  have right (w : F.U) (v : m.Space) (hv : E v = (c.coordinates w).toAdd) :
      subspaceCommutator ρ (c.imageSpace (zpowers (w : G))) (A.subgroupOf F.H) =
      (subspaceCommutator m.action ((ZMod 2) ∙ v)
        (fullCentralizer m.singularMap m.action p)).map E.toLinearMap := by
    have hh := subspaceCommutator_map_embedding ρ m.action θ E.toLinearMap
      (fun a v => (he a v).symm) (A.subgroupOf F.H) ((ZMod 2) ∙ v)
    rw [Submodule.map_span,Set.image_singleton,hA] at hh
    rw [imageSpace_zpowers c w,← hv]
    exact hh
  have hm := model_commutator_families m p
  ext P
  constructor
  · rintro ⟨b,hb,rfl⟩
    let bH : F.H := ⟨b,hBH hb⟩
    have hb' : θ bH ∈ derivedCentralizer m.singularMap m.action p :=
      hB ▸ mem_map_of_mem θ (show bH ∈ B.subgroupOf F.H from hb)
    have hmem : subspaceCommutator m.action ⊤ (zpowers (θ bH)) ∈
        {S | ∃ b ∈ derivedCentralizer m.singularMap m.action p,
          S = subspaceCommutator m.action ⊤ (zpowers b)} := ⟨_,hb',rfl⟩
    rw [hm] at hmem
    obtain ⟨v,hv,hd⟩ := hmem
    have hvR : E v ∈ c.imageSpace R := hR ▸ Submodule.mem_map_of_mem hv
    obtain ⟨w,hw,hwv⟩ := (c.mem_imageSpace_iff R _).mp hvR
    exact ⟨w,hw,(left bH).trans ((congrArg (Submodule.map E.toLinearMap) hd).trans
      (right w v hwv.symm).symm)⟩
  · rintro ⟨w,hw,rfl⟩
    let wU : F.U := ⟨w,hRU hw⟩
    have hwR : (c.coordinates wU).toAdd ∈ c.imageSpace R :=
      (c.mem_imageSpace_iff R _).mpr ⟨wU,hw,rfl⟩
    rw [hR] at hwR
    obtain ⟨v,hv,hvw⟩ := hwR
    have hmem : subspaceCommutator m.action ((ZMod 2) ∙ v)
        (fullCentralizer m.singularMap m.action p) ∈
        {S | ∃ w ∈ perpendicular m.singularMap p,
          S = subspaceCommutator m.action ((ZMod 2) ∙ w)
            (fullCentralizer m.singularMap m.action p)} := ⟨v,hv,rfl⟩
    rw [← hm] at hmem
    obtain ⟨b,hb,hd⟩ := hmem
    rw [← hB] at hb
    obtain ⟨b,hb,rfl⟩ := hb
    exact ⟨b,hb,(right wU v hvw).trans ((congrArg (Submodule.map E.toLinearMap) hd).trans
      (left b).symm)⟩

/-- Apply the model identity to the original critical path; no family identity is assumed. -/
theorem source_common_family_from_model [Finite G] {L : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (θ : F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (θ a) v) = ρ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (B R : Subgroup G) (hBA : B ≤ path.Uα) (hRU : R ≤ F.U)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα)
    (hA : (path.Uα.subgroupOf F.H).map θ = fullCentralizer m.singularMap m.action p)
    (hB : (B.subgroupOf F.H).map θ = derivedCentralizer m.singularMap m.action p)
    (hR : c.imageSpace R = (perpendicular m.singularMap p).map E.toLinearMap) :
    ({C | C ≠ ⊥ ∧ ∃ b ∈ B, C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ w ∈ R, C = ⁅path.Uα,zpowers w⁆}) ∧
    (∀ b ∈ B, path.Uα ⊓ (⁅F.U,zpowers b⁆ ⊔ F.Vi 1) = ⁅F.U,zpowers b⁆) ∧
    fixedSpace ρ (path.Uα.subgroupOf F.H) =
      c.imageSpace (F.U ⊓ centralizer (path.Uα : Set G)) := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  exact source_common_family c h path hplace B R hBA hRU hpoint
    (linear_families_of_model c m E θ he p path.Uα B R (hBA.trans hAH) hRU hA hB hR)

/-- The preimage of the derived model actor inside the specified original partner. -/
def derivedActorLift (θ : F.H →* Atlas.G2.Model (ZMod 2)) (A : Subgroup G) :
    Subgroup G :=
  ((A.subgroupOf F.H) ⊓ (commutator (Atlas.G2.Model (ZMod 2))).comap θ).map F.H.subtype

/-- The derived actor lift stays inside the original partner. -/
theorem derivedActorLift_le (θ : F.H →* Atlas.G2.Model (ZMod 2)) (A : Subgroup G) :
    derivedActorLift θ A ≤ A := by
  rintro _ ⟨a,ha,rfl⟩
  exact ha.1

/-- The derived lift has exactly the derived pencil centralizer as its image. -/
theorem derivedActorLift_image (θ : F.H →* Atlas.G2.Model (ZMod 2))
    (m : BinaryG2Module) (p : Atlas.G2.SingularPoints (ZMod 2)) (A : Subgroup G)
    (hA : (A.subgroupOf F.H).map θ = fullCentralizer m.singularMap m.action p) :
    ((derivedActorLift θ A).subgroupOf F.H).map θ =
      derivedCentralizer m.singularMap m.action p := by
  have hm (a : F.H) : (a : G) ∈ derivedActorLift θ A ↔
      (a : G) ∈ A ∧ θ a ∈ commutator (Atlas.G2.Model (ZMod 2)) := by
    constructor
    · rintro ⟨b,hb,he⟩
      have he' : b = a := Subtype.ext he
      exact he' ▸ hb
    · intro ha
      exact ⟨a,ha,rfl⟩
  change _ = fullCentralizer m.singularMap m.action p ⊓
    commutator (Atlas.G2.Model (ZMod 2))
  rw [← hA]
  ext g
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hh := (hm a).mp ha
    exact ⟨⟨a,hh.1,rfl⟩,hh.2⟩
  · rintro ⟨⟨a,ha,rfl⟩,hd⟩
    exact ⟨a,(hm a).mpr ⟨ha,hd⟩,rfl⟩

/-- The full preimage in the original U of the marked model polar hyperplane. -/
def polarLift (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (p : Atlas.G2.SingularPoints (ZMod 2)) : Subgroup G :=
  ((((perpendicular m.singularMap p).map E.toLinearMap).toAddSubgroup.toSubgroup).comap
    c.coordinates).map F.U.subtype

/-- The polar lift lies in the original section group. -/
theorem polarLift_le (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (p : Atlas.G2.SingularPoints (ZMod 2)) : polarLift c m E p ≤ F.U := map_subtype_le _

/-- The polar lift has precisely the prescribed subspace image. -/
theorem polarLift_image (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (p : Atlas.G2.SingularPoints (ZMod 2)) :
    c.imageSpace (polarLift c m E p) = (perpendicular m.singularMap p).map E.toLinearMap := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (c.mem_imageSpace_iff _ _).mp hv
    obtain ⟨z,hz,he⟩ := hw
    have he' : z = w := Subtype.ext he
    exact he' ▸ hz
  · intro hv
    obtain ⟨w,hw⟩ := c.onto (Multiplicative.ofAdd v)
    apply (c.mem_imageSpace_iff _ _).mpr
    have hm : (c.coordinates w).toAdd ∈ (perpendicular m.singularMap p).map E.toLinearMap := by
      rw [hw]
      exact hv
    exact ⟨w,⟨w,hm,rfl⟩,congrArg Multiplicative.toAdd hw⟩

/-- The critical star marking constructs both ambient indexing subgroups and proves their common family. -/
theorem source_common_family_of_critical_marking [Finite G] {L : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (i (starMap F a)) v) = ρ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hpoint : ¬ F.Vi 1 ≤ path.Uα)
    (hA : (star F path.Uα).map i = fullCentralizer m.singularMap m.action p) :
    let B := derivedActorLift (i.comp (starMap F)) path.Uα
    let R := polarLift c m E p
    ({C | C ≠ ⊥ ∧ ∃ b ∈ B, C = ⁅F.U,zpowers b⁆} =
      {C | C ≠ ⊥ ∧ ∃ w ∈ R, C = ⁅path.Uα,zpowers w⁆}) ∧
    (∀ b ∈ B, path.Uα ⊓ (⁅F.U,zpowers b⁆ ⊔ F.Vi 1) = ⁅F.U,zpowers b⁆) ∧
    fixedSpace ρ (path.Uα.subgroupOf F.H) =
      c.imageSpace (F.U ⊓ centralizer (path.Uα : Set G)) := by
  have hA' : (path.Uα.subgroupOf F.H).map (i.comp (starMap F)) =
      fullCentralizer m.singularMap m.action p := by
    rw [← map_map]
    exact hA
  exact source_common_family_from_model c h path hplace m E (i.comp (starMap F)) he p
    _ _ (derivedActorLift_le _ _) (polarLift_le c m E p) hpoint hA'
    (derivedActorLift_image _ m p _ hA') (polarLift_image c m E p)

/-- A nonidentity derived actor moves an actual line through the marked point. -/
theorem model_nonidentity_moved (m : BinaryG2Module)
    (p : Atlas.G2.SingularPoints (ZMod 2)) (b : Atlas.G2.Model (ZMod 2))
    (hb : b ∈ derivedCentralizer m.singularMap m.action p) (hne : b ≠ 1) :
    ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
      Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l ∧
      subspaceCommutator m.action ⊤ (zpowers b) = m.singularMap.line l := by
  cases m with
  | natural => exact natural_nonidentity_moved p b hb hne
  | weyl => exact weyl_nonidentity_moved p b hb hne

/-- A nonzero original commutator is a four-group with the marked line as its module image. -/
theorem source_commutator_line [Finite G] {L : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (θ : F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (θ a) v) = ρ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (B : Subgroup G) (hBA : B ≤ path.Uα)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα)
    (hB : (B.subgroupOf F.H).map θ = derivedCentralizer m.singularMap m.action p)
    (b : G) (hb : b ∈ B) (hne : ⁅F.U,zpowers b⁆ ≠ ⊥) :
    ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
      Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l ∧
      c.imageSpace ⁅F.U,zpowers b⁆ = (m.singularMap.line l).map E.toLinearMap ∧
      Nat.card (⁅F.U,zpowers b⁆ : Subgroup G) = 4 := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  let bH : F.H := ⟨b,hAH (hBA hb)⟩
  have hcyc : zpowers b ≤ path.Uα := zpowers_le.mpr (hBA hb)
  have hCU : ⁅F.U,zpowers b⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((hcyc.trans hAH).trans c.normalized)
  have hCA : ⁅F.U,zpowers b⁆ ≤ path.Uα :=
    (commutator_mono le_rfl hcyc).trans
      (le_normalizer_iff_commutator_le_right.mp (normalizes_partner h path))
  have himage : c.imageSpace ⁅F.U,zpowers b⁆ =
      (subspaceCommutator m.action ⊤ (zpowers (θ bH))).map E.toLinearMap := by
    rw [commutator_comm,c.imageSpace_commutator _ _ (hcyc.trans hAH) le_rfl,imageSpace_U c]
    exact cyclic_commutator_model_image m E θ he bH
  have hb' : θ bH ∈ derivedCentralizer m.singularMap m.action p :=
    hB ▸ mem_map_of_mem θ (show bH ∈ B.subgroupOf F.H from hb)
  have hbne : θ bH ≠ 1 := by
    intro ht
    have hz : subspaceCommutator m.action ⊤ (zpowers (θ bH)) = ⊥ := by
      rw [ht,zpowers_one_eq_bot]
      apply (subspaceCommutator_eq_bot_iff _ _ _).mpr
      intro v _ a
      have ha : (a : Atlas.G2.Model (ZMod 2)) = 1 := a.property
      simp [ha]
    rw [hz,Submodule.map_bot] at himage
    apply hne
    apply (imageSpace_eq_iff c path.Uα _ ⊥ hpoint hCU bot_le hCA bot_le).mp
    simpa [BinaryConjugationSection.imageSpace] using himage
  obtain ⟨l,hl,heq⟩ := model_nonidentity_moved m p (θ bH) hb' hbne
  rw [heq] at himage
  refine ⟨l,hl,himage,?_⟩
  rw [← imageSpace_card c path.Uα _ hpoint hCU hCA,himage]
  rw [← Nat.card_congr (E.submoduleMap (m.singularMap.line l)).toEquiv]
  exact m.singularMap.line_card l

theorem quotient_image_of_model_image
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (B : Subgroup G) (P : Submodule (ZMod 2) m.Space)
    (hB : c.imageSpace B = P.map E.toLinearMap) :
    letI := c.kernel_normal
    P.toAddSubgroup.toSubgroup.map
      (E.toAddEquiv.toMultiplicative.trans c.quotientEquiv.symm).toMonoidHom =
      (B.subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) := by
  let := c.kernel_normal
  apply Subgroup.map_injective (f := c.quotientEquiv.toMonoidHom) c.quotientEquiv.injective
  rw [map_map,map_map]
  have hq : c.quotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) = c.coordinates := by
    ext u
    exact c.quotientEquiv_mk u
  have hm : c.quotientEquiv.toMonoidHom.comp
      (E.toAddEquiv.toMultiplicative.trans c.quotientEquiv.symm).toMonoidHom =
      E.toAddEquiv.toMultiplicative.toMonoidHom := by
    ext v
    exact c.quotientEquiv.apply_symm_apply _
  rw [hm,hq]
  have he : (P.map E.toLinearMap).toAddSubgroup.toSubgroup =
      P.toAddSubgroup.toSubgroup.map E.toAddEquiv.toMultiplicative.toMonoidHom := by
    ext x
    rfl
  rw [← he,← hB]
  rfl

/-- Formulas (a) and the individual lines in (c), with the original quotient map and partner intersection. -/
theorem source_commutator_quotient_line [Finite G] {L : Subgroup G}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (θ : F.H →* Atlas.G2.Model (ZMod 2))
    (he : ∀ a v, E (m.action (θ a) v) = ρ a (E v))
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (B : Subgroup G) (hBA : B ≤ path.Uα)
    (hpoint : ¬ F.Vi 1 ≤ path.Uα)
    (hB : (B.subgroupOf F.H).map θ = derivedCentralizer m.singularMap m.action p)
    (b : G) (hb : b ∈ B) (hne : ⁅F.U,zpowers b⁆ ≠ ⊥) :
    letI := c.kernel_normal
    ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
      Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l ∧
      (transportGeometry m.singularMap.geometry
        (E.toAddEquiv.toMultiplicative.trans c.quotientEquiv.symm)).line l =
        ((⁅F.U,zpowers b⁆ ⊔ F.Vi 1).subgroupOf F.U).map
          (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) ∧
      path.Uα ⊓ (⁅F.U,zpowers b⁆ ⊔ F.Vi 1) = ⁅F.U,zpowers b⁆ ∧
      Nat.card (⁅F.U,zpowers b⁆ : Subgroup G) = 4 := by
  let := c.kernel_normal
  obtain ⟨l,hl,himage,hcard⟩ := source_commutator_line c h path hplace m E θ he p
    B hBA hpoint hB b hb hne
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hcyc : zpowers b ≤ path.Uα := zpowers_le.mpr (hBA hb)
  have hCU : ⁅F.U,zpowers b⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((hcyc.trans hAH).trans c.normalized)
  have hCA : ⁅F.U,zpowers b⁆ ≤ path.Uα :=
    (commutator_mono le_rfl hcyc).trans
      (le_normalizer_iff_commutator_le_right.mp (normalizes_partner h path))
  refine ⟨l,hl,?_,partner_inf_sup_point c _ _ hpoint hCU hCA,hcard⟩
  exact quotient_image_of_model_image c m E _ _
    ((imageSpace_sup_point c _ hCU).trans himage)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
