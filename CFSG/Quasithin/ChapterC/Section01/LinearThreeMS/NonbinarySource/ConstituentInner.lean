module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.OmegaRecognitionBounds
public import Theory.Representation.SL3OddNaturalNormalizer.Index
public import Theory.Representation.QuadraticSemilinear
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Inner action of the selected central-omega offender

A quadratic offender in a faithful natural SL₃ normalizer is field-linear:
a nontrivial coefficient twist would inject the whole offender into the
field automorphism group, whose order is n, whereas its displacement on
the natural three-space has binary dimension at least 3n/2. Its square-one
operators then have determinant one, placing the offender in the actual
natural component. This includes field four.

Apply this to the literal central section of an Irr⁺ constituent preserved
by the original minimal offender. The section kernel centralizes the full
covering component, so the original offender induces inner automorphisms
on that component. Its literal initial image therefore lies in the initial
full SL₃ component. Upstairs the offender lies in the component times the
whole-action two-core, retaining its weight, injectivity and order bounds.

NonblockConstituentInner applies this result to original 4.3.8--10 and its
actual Sylow intersection. Containment in the component alone, elimination
of the whole-action kernel and common-marked whole sections remain open;
no field-four kernel is discarded in this reduction.
Source: Aschbacher--Smith B.1.5, B.7.2, K.3.2 and C.1.34, printed
pp.69--70,119,454--456,136--137. The semilinear displacement argument is
the scalar calculation used in Meierfrankenfeld--Stellmacher (1993), (3.4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentInner

private theorem natural_quadratic_offender_linear
    {F X : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group X]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (B : Subgroup X) [B.Normal] (e : B ≃* SL(3,F))
    (ρ : Representation (ZMod 2) X (Fin 3 → F)) (hf : Function.Injective ρ)
    (hb : ∀ (b : B) v, ρ b v = (e b).val.mulVec v)
    (A : Subgroup X) (hA : IsOffender ρ A) (hq : IsQuadratic ρ A) :
    ∀ a ∈ A, ∀ (c : F) v, ρ a (c • v) = c • ρ a v := by
  have hsemi := SL3OddNaturalNormalizer.normalizer_semilinear B e ρ hb
  intro a ha
  obtain ⟨σ,hσ⟩ := hsemi a
  have hs : σ = RingEquiv.refl F := by
    by_contra hs
    have hc := quadratic_card_le_ringAut_of_nontrivial_twist ρ A hq hf
      (fun a _ => hsemi a) ha hs hσ
    rw [SL3OddNaturalNormalizer.binaryFieldAut_card hF] at hc
    have hr : rank A ≤ n := (Nat.log_le_self 2 (Nat.card A)).trans hc
    have htwist : ∃ c, σ.toRingHom c ≠ c := by
      by_contra! hz
      exact hs (RingEquiv.ext hz)
    have hd := NaturalTensor.finrank_le_twice_operatorFixedCodim (ρ a) σ.toRingHom htwist hσ
    have hdegree : Module.finrank (ZMod 2) F = n := by
      apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
    have hv : Module.finrank (ZMod 2) (Fin 3 → F) = 3*n := by
      simp [Module.finrank_pi_fintype,hdegree]
    have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) :=
      (ρ).invariants_comp_subtype_antitone (zpowers_le.mpr ha)
    have hm := Submodule.finrank_mono hle
    have h1 := fixedCodim_add_finrank ρ A
    have h2 := fixedCodim_add_finrank ρ (zpowers a)
    have ho := hA.2
    change Module.finrank (ZMod 2) (Fin 3 → F) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) at hd
    rw [←fixedCodim_zpowers_eq_displacement_rank,hv] at hd
    omega
  simpa only [hs,RingEquiv.refl_apply] using hσ

private theorem natural_quadratic_offender_le
    {F X : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] [Group X]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (B : Subgroup X) [B.Normal] (e : B ≃* SL(3,F))
    (ρ : Representation (ZMod 2) X (Fin 3 → F)) (hf : Function.Injective ρ)
    (hb : ∀ (b : B) v, ρ b v = (e b).val.mulVec v)
    (A : Subgroup X) (hA : IsOffender ρ A) (hq : IsQuadratic ρ A) : A ≤ B := by
  have hlin := natural_quadratic_offender_linear hn hF B e ρ hf hb A hA hq
  let := hA.1.2
  intro a ha
  let t : Module.End F (Fin 3 → F) := {
    toFun := ρ a
    map_add' := (ρ a).map_add
    map_smul' := hlin a ha }
  have ha2 : a^2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have ht : t^2 = 1 := by
    apply LinearMap.ext
    intro v
    change ρ a (ρ a v) = v
    rw [←Module.End.mul_apply,←map_mul,←pow_two,ha2,map_one]
    rfl
  have hd : (LinearMap.toMatrix' t).det = 1 := by
    have hm : LinearMap.toMatrix' t * LinearMap.toMatrix' t = 1 := by
      rw [←LinearMap.toMatrix'_mul,←pow_two,ht,LinearMap.toMatrix'_one]
    have hd2 : (LinearMap.toMatrix' t).det^2 = 1 := by
      rw [pow_two,←Matrix.det_mul,hm,Matrix.det_one]
    rcases sq_eq_one_iff.mp hd2 with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  let s : SL(3,F) := ⟨LinearMap.toMatrix' t,hd⟩
  have heq : a = (e.symm s : B) := by
    apply hf
    apply LinearMap.ext
    intro v
    rw [hb,e.apply_symm_apply]
    exact (LinearMap.toMatrix'_mulVec t v).symm
  rw [heq]
  exact (e.symm s).property

private theorem natural_quadratic_offender_le_of_coordinates
    {F X W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (B : Subgroup X) [B.Normal] (e : B ≃* SL(3,F))
    (ρ : Representation (ZMod 2) X W) (hf : Function.Injective ρ)
    (l : W ≃ₗ[ZMod 2] (Fin 3 → F))
    (hl : ∀ (b : B) v, l (ρ b v) = specialLinearNatural 3 (e b) (l v))
    (A : Subgroup X) (hA : IsOffender ρ A) (hq : IsQuadratic ρ A) : A ≤ B := by
  let τ : Representation (ZMod 2) X (Fin 3 → F) := l.conjRingEquiv.toMonoidHom.comp ρ
  have he (a : X) (v : W) : l (ρ a v) = τ a (l v) := by
    change l (ρ a v) = l (ρ a (l.symm (l v)))
    rw [l.symm_apply_apply]
  have ho : IsOffender τ A := by
    simpa only [Subgroup.map_id] using
      hA.map_equivariant ρ τ (MonoidHom.id X) Function.injective_id l he
  have hqt : IsQuadratic τ A := by
    simpa only [Subgroup.map_id] using
      quadratic_map_equivariant ρ τ (MonoidHom.id X) l he hq
  apply natural_quadratic_offender_le hn hF B e τ (l.conjRingEquiv.injective.comp hf) _ A ho hqt
  intro b v
  change l (ρ b (l.symm v)) = _
  rw [hl,l.apply_symm_apply]
  rfl


open ChapterB.QuasisimpleSource

private theorem offender_le_component_centralizer_of_natural_section
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (B D : Subgroup X) [B.Normal] [IsQuasisimple B]
    (hD : IsBestOffender ρ D) (hq : IsQuadratic ρ D)
    (hd : D ⊓ centralizer (B : Set X) = ⊥)
    (I : Submodule (ZMod 2) W) (hI : IsIrrPlus ρ B I) (F : BinaryField)
    (hnat : ConstituentRecognition.HasNaturalCentralSection ρ B D I F) :
    D ≤ B ⊔ centralizer (B : Set X) := by
  obtain ⟨hs,hn,⟨a⟩⟩ := hnat
  let H := B ⊔ D
  let C := B.subgroupOf H
  let τ := ρ.comp H.subtype
  let U : Subrepresentation τ := ⟨fixedSpace ρ B,fun g _ hv =>
    (fixedSpace_stable_of_normalizes ρ hn g.property _).2 hv⟩
  let V := invariantSubspace ρ H I hs
  let σ := centralSectionRepresentation ρ B H I hs hn
  let π := KernelQuotient.projection σ
  let C' := SourceCompletion.ChiefImage.component σ C
  let δ := KernelQuotient.action σ
  let := SourceCompletion.ChiefImage.component_normal σ C
  have hk := centralSection_kernel_le_centralizer ρ B H le_sup_left I hI hs hn
  have hfaith : ∀ d ∈ D.subgroupOf H,
      (∀ v, sectionRepresentation τ U V d v = v) → d = 1 := by
    intro d hdD hdv
    have hdker : d ∈ σ.ker := by
      apply LinearMap.ext
      exact hdv
    apply Subtype.ext
    exact hd.le ⟨hdD,(hk (mem_map_of_mem H.subtype hdker)).2⟩
  have hoImg := ((hD.subgroupOf ρ le_sup_right).isOffender τ).on_faithful_section τ U V hfaith
  have hE (g : actionImage σ) (v : centralQuotient ρ B I) :
      (LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) (imageRepresentation σ g v) =
        δ ((KernelQuotient.equiv σ).symm g) v := by
    change _ = imageRepresentation σ ((KernelQuotient.equiv σ) ((KernelQuotient.equiv σ).symm g)) v
    rw [(KernelQuotient.equiv σ).apply_symm_apply]
    rfl
  have ho : IsOffender δ ((D.subgroupOf H).map π) := by
    have ht := hoImg.map_equivariant (imageRepresentation σ) δ
      (KernelQuotient.equiv σ).symm.toMonoidHom (KernelQuotient.equiv σ).symm.injective
      (LinearEquiv.refl (ZMod 2) _) hE
    change IsOffender δ ((actionSubgroup σ (D.subgroupOf H)).map
      (KernelQuotient.equiv σ).symm.toMonoidHom) at ht
    rwa [KernelQuotient.actionSubgroup_transport] at ht
  have hqτ : IsQuadratic τ (D.subgroupOf H) :=
    fun x hx y hy v => hq x hx y hy v
  have hqσ : IsQuadratic σ (D.subgroupOf H) := quadratic_section τ U V hqτ
  have hqδ : IsQuadratic δ ((D.subgroupOf H).map π) :=
    quadratic_map_equivariant σ δ π (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) hqσ
  have hle : (D.subgroupOf H).map π ≤ C' :=
    natural_quadratic_offender_le_of_coordinates F.degree_pos F.card_eq C' a.groupEquiv
      δ (KernelQuotient.faithful σ) a.linearEquiv a.intertwines _ ho hqδ
  intro d hdD
  have hp : π (⟨d,mem_sup_right hdD⟩ : H) ∈ C' :=
    hle (mem_map_of_mem π hdD)
  obtain ⟨b,hb,hbd⟩ := hp
  have he : b⁻¹ * (⟨d,mem_sup_right hdD⟩ : H) ∈ σ.ker := by
    have hpker : π (b⁻¹ * (⟨d,mem_sup_right hdD⟩ : H)) = 1 := by
      rw [map_mul,map_inv,hbd,inv_mul_cancel]
    have hh := congrArg (fun x => δ x) hpker
    change σ (b⁻¹ * (⟨d,mem_sup_right hdD⟩ : H)) = δ 1 at hh
    rw [map_one] at hh
    exact hh
  have hc := (hk (mem_map_of_mem H.subtype he)).2
  have hm := (B ⊔ centralizer (B : Set X)).mul_mem
    (mem_sup_left hb) (mem_sup_right hc)
  change (b : X) * ((b : X)⁻¹ * d) ∈ B ⊔ centralizer (B : Set X) at hm
  simpa only [mul_inv_cancel_left] using hm

variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E := CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)

include h hn

/-- The original radical overgroup supplies a minimal quadratic offender
whose conjugation on the full covering component is inner. The entire
centralizer is retained, including the whole-action two-core. -/
theorem exists_minimal_inner_offender
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho D = weight rho (A.map q) ∧ ⁅B,D⁆ = B ∧
      D ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((f).comp D.subtype) ∧
      D ≤ B ⊔ centralizer (B : Set H) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  obtain ⟨A,hA,D,hDA,hD,hqD,hw,hm,hd,hfD,hs⟩ :=
    ConstituentOffenders.exists_minimal_section_offender h hn hfixed S hRS
  obtain ⟨I,hI⟩ := ConstituentRecognition.exists_irrPlus h hn
  have hDI := sup_le hI.choose (hs I hI)
  have hDN : B ⊔ D ≤ normalizer (B : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hff := centralSection_isFFModule_of_offender rho B D (B ⊔ D) hD.1
    le_sup_left le_sup_right (disjoint_iff.mpr hd) I hI hDI hDN
  have hsq : IsSQTK KnownSimple.IsKnownSimple B :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) (h.sqtk.subgroup L)
      (ChapterA.Section02.IsSectionOf.of_surjective ((q).comp (L).subtype).rangeRestrict
        ((q).comp (L).subtype).rangeRestrict_surjective)
  have hnat : ConstituentRecognition.HasNaturalCentralSection rho B D I
      (ConstituentRecognition.coefficientField h hn) :=
    ⟨hDI,hDN,ConstituentRecognition.centralSection_natural rho B D hD.1.1 I hI hDI hDN
      hff hsq (ConstituentRecognition.coefficientField h hn)
      (KernelOffenders.omegaCover h hn (Classical.choice h.model)).quotientCenterEquiv⟩
  exact ⟨A,hA,D,hDA,hD,hqD,hw,hm,hd,hfD,
    offender_le_component_centralizer_of_natural_section rho B D hD.1 hqD hd I hI
      (ConstituentRecognition.coefficientField h hn) hnat⟩


/-- Inner action on the full covering component places the literal initial
image inside its original full SL₃ component. No projective quotient is used. -/
theorem initial_image_le_component (D : Subgroup H)
    (hD : D ≤ B ⊔ centralizer (B : Set H)) :
    D.map f ≤ centralOmegaComponent K R := by
  let := centralOmegaComponent_normal h hn
  let := centralOmegaComponent_quasisimple h hn
  have hfit : generalizedFitting (CentralOmegaActor K R) = (B).map f := by
    rw [MonoidHom.range_comp,range_subtype,NoncoreOffenders.toInitial_component]
    exact generalizedFitting_eq_of_quasisimple_two_quotient _
      (centralOmega_outer_isTwoGroup h hn) (centralOmega_quotient_core_eq_bot h hn)
  have hc : (centralizer (B : Set H)).map f ≤
      centralizer ((B).map f : Set (CentralOmegaActor K R)) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    simpa only [map_mul] using congrArg f (ha b hb)
  have hc' : (centralizer (B : Set H)).map f ≤ (B).map f :=
    hc.trans (hfit ▸ centralizer_generalizedFitting_le (CentralOmegaActor K R))
  have hd : D.map f ≤ (B).map f := by
    apply (map_mono hD).trans
    rw [Subgroup.map_sup]
    exact sup_le le_rfl hc'
  simpa only [MonoidHom.range_comp,range_subtype,NoncoreOffenders.toInitial_component] using hd

/-- The only possible discrepancy from component containment lies in the
whole-action two-core, identified with the exact initial-projection kernel. -/
theorem le_component_sup_core (D : Subgroup H)
    (hD : D ≤ B ⊔ centralizer (B : Set H)) : D ≤ B ⊔ pCore 2 H := by
  have he : (B).map f = centralOmegaComponent K R := by
    rw [MonoidHom.range_comp,range_subtype,NoncoreOffenders.toInitial_component]
  have hd := initial_image_le_component h hn D hD
  rw [←he] at hd
  have hl := map_le_iff_le_comap.mp hd
  rwa [comap_map_eq,NoncoreOffenders.toInitial_kernel] at hl

/-- One source offender simultaneously retains its maximum elementary
origin, weight, movement, bounds and faithful
initial projection, whose image now lies in the actual initial component. -/
theorem exists_minimal_component_mod_core_offender
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho D = weight rho (A.map q) ∧ ⁅B,D⁆ = B ∧
      D ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((f).comp D.subtype) ∧
      D ≤ B ⊔ pCore 2 H ∧ D.map f ≤ centralOmegaComponent K R ∧
      Nat.card D ≤ 2^(2*n) ∧ rank D ≤ 2*n ∧ fixedCodim rho D ≤ 2*n := by
  obtain ⟨A,hA,D,hDA,hD,hqD,hw,hm,hd,hfD,hi⟩ :=
    exists_minimal_inner_offender h hn hfixed S hRS
  have hb := MovingBounds.elementary_card_le_of_disjoint h hn D hD.1.1 hd
  have hr : rank D ≤ 2*n := by
    rw [hD.1.1.card_eq_two_pow_rank] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hb
  exact ⟨A,hA,D,hDA,hD,hqD,hw,hm,hd,hfD,le_component_sup_core h hn D hi,
    initial_image_le_component h hn D hi,hb,hr,(hD.1.isOffender rho).2.trans hr⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentInner
