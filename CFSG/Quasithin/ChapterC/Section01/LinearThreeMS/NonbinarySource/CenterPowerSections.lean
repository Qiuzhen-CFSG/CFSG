module
public import Theory.GroupTheory.PGroup.IrreducibleOmegaPowerBridge
public import Theory.GroupTheory.PGroup.HomocyclicFourRecognition
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.OmegaSplitFour

/-!
# Natural omega and the whole center's Frattini quotient

A natural first omega is irreducible under the original marked component.
The last power map of the whole abelian subgroup therefore has image all of
that omega and kernel its Frattini subgroup. This gives the natural module
on the whole subgroup modulo its own Frattini subgroup, with the same actor
marking and literal conjugation as on the omega section.

Apply this to Z(Q) in the nonbinary linear-three MS-pair. At field four,
the existing whole-omega dichotomy now gives simultaneous natural models
on Ω₁(Z(Q)) and Z(Q)/Φ(Z(Q)), or the full doubled-natural omega alternative.
If the center is not elementary in the natural-omega branch, every involution
has a square root in its canonical Ω₂. This subgroup is an actual C₄^(3n),
and its quotient by Ω₁ is natural at the same marking. The source reduction
retains this possible lift and the doubled-omega branch.

The exponent of Z(Q) is not assumed to be two. This does not identify the
whole center, Φ(Q), or Q/Z(Q); those remain part of C.1.34 reconstruction.

The original nonblock configuration supplies the genuine MS-pair and its
fixed-factor exclusion in NonblockCenterPowerSections. No ambient Hypothesis1223
or new classification premise is used.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original
4.3.8–10, pp.616–617; the power-map proof is elementary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CenterPowerSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K Z : Subgroup G}
variable {F : Type} [Field F]

omit [Finite G] in
private theorem natural_omega_irreducible [IsMulCommutative Z]
    (hKZ : K ≤ normalizer (Z : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ((omega₁ Z (p := 2)).map Z.subtype) ⊥
      (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    let ρ : K →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hKZ)
    (omega₁ Z (p := 2) ≠ ⊥) ∧
      ∀ B : Subgroup Z, B ≤ omega₁ Z (p := 2) →
        (∀ k x, x ∈ B → ρ k x ∈ B) → B = ⊥ ∨ B = omega₁ Z (p := 2) := by
  let O := omega₁ Z (p := 2)
  let E := O.map Z.subtype
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,a,ha⟩ := hm
  let := hn
  let c : O ≃* E := O.equivMapOfInjective Z.subtype Z.subtype_injective
  let b : O ≃* Multiplicative (Fin 3 → F) := c.trans (QuotientGroup.quotientBot.symm.trans a)
  let ρ : K →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hKZ)
  have hb (k : K) (x : O) :
      (b (OmegaAction.omegaRestriction Z 2 1 (ρ k) x)).toAdd =
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd := by
    exact ha k (c x) (c (OmegaAction.omegaRestriction Z 2 1 (ρ k) x)) rfl
  have hne : O ≠ ⊥ := by
    let : Nontrivial O := Function.Injective.nontrivial b.symm.injective
    exact (nontrivial_iff_ne_bot O).mp inferInstance
  have hirr (B : Subgroup Z) (hBO : B ≤ O)
      (hinv : ∀ k x, x ∈ B → ρ k x ∈ B) : B = ⊥ ∨ B = O := by
    by_cases hB : B = ⊥
    · exact Or.inl hB
    right
    apply le_antisymm hBO
    obtain ⟨u,hu,hune⟩ := B.bot_or_exists_ne_one.resolve_left hB
    let uu : O := ⟨u,hBO hu⟩
    have hu0 : (b uu).toAdd ≠ 0 := by
      intro hh
      exact hune (congrArg Subtype.val (b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)))
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ B.one_mem
    let yy : O := ⟨y,hy⟩
    have hy0 : (b yy).toAdd ≠ 0 := by
      intro hh
      exact hy1 (congrArg Subtype.val (b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)))
    obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hu0 hy0
    obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
    have hbxy : OmegaAction.omegaRestriction Z 2 1 (ρ k) uu = yy := by
      apply b.injective
      apply Multiplicative.toAdd.injective
      rw [hb]
      change specialLinearNatural 3 (e (QuotientGroup.mk' _ k)) (b uu).toAdd = _
      rw [show e (QuotientGroup.mk' _ k) = g from hk]
      exact hg
    have hxy : ρ k u = y := congrArg Subtype.val hbxy
    exact hxy ▸ hinv k u hu
  exact ⟨hne,hirr⟩

/-- Natural first omega gives a natural Frattini quotient of the whole abelian
subgroup, with exactly the same actor marking. Higher exponent is retained. -/
theorem natural_frattini_of_natural_omega [IsMulCommutative Z]
    (hZ : IsPGroup 2 Z) (hKZ : K ≤ normalizer (Z : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ((omega₁ Z (p := 2)).map Z.subtype) ⊥
      (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    HasSectionModel K Z (frattiniIn Z) (linearThreeActor e) (specialLinearNatural 3) := by
  have hi := natural_omega_irreducible hKZ e hm
  let O := omega₁ Z (p := 2)
  let E := O.map Z.subtype
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,a,ha⟩ := hm
  let := hn
  let c : O ≃* E := O.equivMapOfInjective Z.subtype Z.subtype_injective
  let b : O ≃* Multiplicative (Fin 3 → F) := c.trans (QuotientGroup.quotientBot.symm.trans a)
  let ρ : K →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hKZ)
  have hb (k : K) (x : O) :
      (b (OmegaAction.omegaRestriction Z 2 1 (ρ k) x)).toAdd =
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd := by
    exact ha k (c x) (c (OmegaAction.omegaRestriction Z 2 1 (ρ k) x)) rfl
  obtain ⟨hne,hirr⟩ := hi
  obtain ⟨m,hmpos,hexp,d,hd,hdaut⟩ :=
    OmegaPowerBridge.exists_equivariant_equiv hZ hne ρ hirr
  have hPhi : (frattiniIn Z).subgroupOf Z = frattini Z :=
    (frattini Z).comap_map_eq_self_of_injective Z.subtype_injective
  rw [HasSectionModel,hPhi]
  refine ⟨map_subtype_le _,hKZ,hKZ.trans
    (normalizer_le_normalizer_characteristic_image Z (frattini Z)),inferInstance,d.trans b,?_⟩
  intro k x y hxy
  have hy : y = ρ k x := Subtype.ext hxy
  rw [hy]
  change (b (d (QuotientGroup.mk' _ (ρ k x)))).toAdd =
    specialLinearNatural 3 (linearThreeActor e k) (b (d (QuotientGroup.mk' _ x))).toAdd
  rw [← quotientAut_apply_mk,hdaut]
  exact hb k _


/-- A non-elementary abelian group with natural omega has a canonical
lift of exponent four, with its square quotient natural at the original marking. -/
theorem natural_four_layer_of_not_elementary [IsMulCommutative Z]
    (hZ : IsPGroup 2 Z) (hKZ : K ≤ normalizer (Z : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ((omega₁ Z (p := 2)).map Z.subtype) ⊥
      (linearThreeActor e) (specialLinearNatural (k := F) 3))
    (hnot : ¬ ∀ x : Z, x^2=1) :
    let Y := (omega Z (p := 2) 2).map Z.subtype
    let E := (omega₁ Z (p := 2)).map Z.subtype
    (∀ x ∈ Y, x^4=1) ∧
      HasSectionModel K Y E (linearThreeActor e) (specialLinearNatural 3) ∧
      Nat.card Y = Nat.card E ^ 2 ∧
      ∀ x : Y, x^2=1 → ∃ y : Y, y^2=x := by
  let O := omega₁ Z (p := 2)
  let P := omega Z (p := 2) 2
  let Y := P.map Z.subtype
  let E := O.map Z.subtype
  let : O.Characteristic := omega₁_characteristic Z
  let : P.Characteristic := omega_characteristic Z 2
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative Z
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map Z.subtype
  let : IsMulCommutative Y := inferInstance
  let ρ : K →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hKZ)
  obtain ⟨hne,hirr⟩ := natural_omega_irreducible hKZ e hm
  have hroots := OmegaPowerBridge.square_roots_of_not_elementary hZ hne ρ hirr hnot
  have hOP : O ≤ P := by
    intro x hx
    apply Subgroup.subset_closure
    have hs : x^2=1 := elemPow_eq_one_of_isElementaryAbelian _ hx
    change x^4=1
    calc
      x^4=(x^2)^2 := pow_mul x 2 2
      _=1 := by rw [hs,one_pow]
  have hEY : E ≤ Y := map_mono hOP
  have hYZ : Y ≤ Z := map_subtype_le _
  have hfour : ∀ x ∈ Y, x^4=1 := by
    rintro x ⟨z,hz,rfl⟩
    have hz4 : z^4=1 := by
      have hh := (OmegaAction.omega_eq_pow_ker (G := Z) 2 2).le hz
      exact hh
    exact congrArg Z.subtype hz4
  let f : Y →* E := {
    toFun x := ⟨(x:G)^2,by
      let z : Z := ⟨x,hYZ x.property⟩
      refine ⟨z^2,Subgroup.subset_closure ?_,rfl⟩
      apply Subtype.ext
      change ((x:G)^2)^2=1
      rw [←pow_mul]
      exact hfour x x.property⟩
    map_one' := Subtype.ext (one_pow 2)
    map_mul' x y := Subtype.ext (congrArg Y.subtype (mul_pow x y 2)) }
  have hfs : Function.Surjective f := by
    rintro ⟨x,z,hz,rfl⟩
    obtain ⟨y,hy⟩ := hroots ⟨z,hz⟩
    refine ⟨⟨y,mem_map_of_mem Z.subtype y.property⟩,?_⟩
    apply Subtype.ext
    exact congrArg Z.subtype hy
  have hfk : f.ker = E.subgroupOf Y := by
    ext x
    change f x = 1 ↔ (x:G) ∈ E
    constructor
    · intro hx
      have hx2 : (x:G)^2=1 := congrArg E.subtype hx
      let z : Z := ⟨x,hYZ x.property⟩
      refine ⟨z,Subgroup.subset_closure ?_,rfl⟩
      exact Subtype.ext hx2
    · intro hx
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian _ hx
  have hc : Nat.card Y = Nat.card E ^ 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr hfs,card_top,hfk,
      Nat.card_congr (subgroupOfEquivOfLe hEY).toEquiv] at hh
    simpa only [pow_two] using hh.symm
  have hroot (x : Y) (hx : x^2=1) : ∃ y : Y, y^2=x := by
    have hxk : x ∈ f.ker := by
      apply Subtype.ext
      exact congrArg Y.subtype hx
    obtain ⟨y,hy⟩ := hfs ⟨x,hfk.le hxk⟩
    exact ⟨y,Subtype.ext (congrArg E.subtype hy)⟩
  let d : (Y ⧸ E.subgroupOf Y) ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,a,ha⟩ := hm
  let := hn
  let b : E ≃* Multiplicative (Fin 3 → F) := QuotientGroup.quotientBot.symm.trans a
  refine ⟨hfour,⟨hEY,hKZ.trans (normalizer_le_normalizer_characteristic_image Z P),
    hKZ.trans (normalizer_le_normalizer_characteristic_image Z O),inferInstance,d.trans b,?_⟩,hc,hroot⟩
  intro k x y hxy
  change (b (f y)).toAdd = specialLinearNatural 3 (linearThreeActor e k) (b (f x)).toAdd
  apply ha k (f x) (f y)
  change (y:G)^2=(k:G)*(x:G)^2*(k:G)⁻¹
  rw [hxy]
  exact (map_pow (MulAut.conj (k:G)) (x:G) 2).symm

variable {R : Subgroup G} {n : ℕ} [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
include h hn
local notation "Q" => msQ K R
local notation "ZQ" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "OQ" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn Q

omit [CharP F 2] in
/-- The whole center's Frattini quotient has the same natural marking as its
first omega. This uses Φ(Z(Q)), and makes no assertion that Φ(Q) equals Z(Q). -/
theorem center_frattini_of_natural_omega
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K OQ ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    HasSectionModel K ZQ (frattiniIn ZQ) (linearThreeActor e) (specialLinearNatural 3) := by
  let : IsMulCommutative ZQ := by
    exact map_isMulCommutative (center Q) (Q).subtype
  have hp : IsPGroup 2 ZQ := (isPGroup_pCoreIn 2 (K ⊔ R)).to_le
    ((map_subtype_le _).trans msQ_le_joinCore)
  have he : OQ = (omega₁ ZQ (p := 2)).map (ZQ).subtype :=
    Subgroup.omegaCenterIn_eq_omegaOneAmbient Q
  have hnZ : K ≤ normalizer (ZQ : Set G) :=
    (le_sup_left : K ≤ K ⊔ R).trans (CentralSections.join_normalizes_center h hn)
  exact natural_frattini_of_natural_omega hp hnZ e (he ▸ hm)

omit [CharP F 2] in
/-- A natural central omega gives either the whole natural center or a
canonical homocyclic lift of exponent four, with its square quotient marked naturally. -/
theorem center_natural_or_four_lift
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K OQ ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    HasSectionModel K ZQ ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      let Y := (omega ZQ (p := 2) 2).map (ZQ).subtype
      (K ⊔ R) ≤ normalizer (Y : Set G) ∧
        Nonempty (Y ≃* StandardHomocyclicCover (Fin (3*n)) 4) ∧
        HasSectionModel K Y OQ (linearThreeActor e) (specialLinearNatural 3) := by
  let : IsMulCommutative ZQ := by
    exact map_isMulCommutative (center Q) (Q).subtype
  have hp : IsPGroup 2 ZQ := (isPGroup_pCoreIn 2 (K ⊔ R)).to_le
    ((map_subtype_le _).trans msQ_le_joinCore)
  have he : OQ = (omega₁ ZQ (p := 2)).map (ZQ).subtype :=
    Subgroup.omegaCenterIn_eq_omegaOneAmbient Q
  by_cases hsq : ∀ x : ZQ, x^2=1
  · left
    have hO : OQ = ZQ := by
      rw [he]
      apply le_antisymm (map_subtype_le _)
      intro x hx
      exact ⟨⟨x,hx⟩,Subgroup.subset_closure (by
        change (⟨x,hx⟩ : ZQ)^2=1
        exact hsq ⟨x,hx⟩),rfl⟩
    exact hO ▸ hm
  right
  have hnZ := CentralSections.join_normalizes_center h hn
  obtain ⟨hfour,hmodel,hcard,hroot⟩ := natural_four_layer_of_not_elementary hp
    ((le_sup_left : K ≤ K ⊔ R).trans hnZ) e (he ▸ hm) hsq
  let Y := (omega ZQ (p := 2) 2).map (ZQ).subtype
  have hOcard : Nat.card OQ = 2^(3*n) := by
    rw [HasSectionModel,bot_subgroupOf] at hm
    obtain ⟨_,_,_,hi,b,_⟩ := hm
    let := hi
    rw [Nat.card_congr (QuotientGroup.quotientBot.symm.trans b).toEquiv]
    change Nat.card (Fin 3 → F) = _
    rw [Nat.card_fun,Nat.card_fin,h.field_card,←pow_mul,Nat.mul_comm n 3]
  have hYcard : Nat.card Y = 4^(3*n) := by
    rw [←he,hOcard,←pow_mul] at hcard
    calc
      Nat.card Y = 2^(3*n*2) := hcard
      _ = (2^2)^(3*n) := by rw [←pow_mul,Nat.mul_comm (3*n) 2]
      _ = 4^(3*n) := rfl
  let : IsMulCommutative Y := by dsimp [Y]; infer_instance
  have hYe := homocyclicFour_of_square_roots
    (fun x : Y => Subtype.ext (hfour x x.property)) hroot hYcard
  let : (omega ZQ (p := 2) 2).Characteristic := omega_characteristic ZQ 2
  exact ⟨hnZ.trans (normalizer_le_normalizer_characteristic_image ZQ
    (omega ZQ (p := 2) 2)),hYe,he.symm ▸ hmodel⟩

/-- At field four the natural branch simultaneously marks both elementary
ends of the whole center. The doubled-omega branch is retained in full. -/
theorem center_section_alternatives
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥) (hfour : Nat.card F = 4) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      (HasSectionModel K OQ ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
        HasSectionModel K ZQ (frattiniIn ZQ) (linearThreeActor e) (specialLinearNatural 3)) ∨
      HasSectionModel K OQ ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  obtain ⟨e,hm | hm⟩ := OmegaSplitFour.omega_section_models h hn hfixed hfour
  · exact ⟨e,Or.inl ⟨hm,center_frattini_of_natural_omega h hn e hm⟩⟩
  · exact ⟨e,Or.inr hm⟩

/-- Whole-center reconstruction at field four reduces to the natural center,
doubled omega, or an explicit canonical C₄^(3n) lift at the same marking. -/
theorem center_reconstruction_alternatives
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥) (hfour : Nat.card F = 4) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K ZQ ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K OQ ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∨
      (HasSectionModel K OQ ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
        let Y := (omega ZQ (p := 2) 2).map (ZQ).subtype
        (K ⊔ R) ≤ normalizer (Y : Set G) ∧
          Nonempty (Y ≃* StandardHomocyclicCover (Fin (3*n)) 4) ∧
          HasSectionModel K Y OQ (linearThreeActor e) (specialLinearNatural 3)) := by
  obtain ⟨e,hm | hm⟩ := OmegaSplitFour.omega_section_models h hn hfixed hfour
  · rcases center_natural_or_four_lift h hn e hm with hc | hc
    · exact ⟨e,Or.inl hc⟩
    · exact ⟨e,Or.inr (Or.inr ⟨hm,hc⟩)⟩
  · exact ⟨e,Or.inr (Or.inl hm)⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CenterPowerSections
