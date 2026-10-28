module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingBranch
public import Theory.Representation.SL2FourQuadraticRecognition.QuotientMap
public import Theory.Representation.SL2FourNaturalExtensions.SylowElements
public import Theory.Representation.AlternatingFiveInvolutionDisplacement
public import Theory.Representation.BinaryOffender.QuadraticFixedDimension
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Natural recognition from the original residual Sylow index

The faithful S₅ action descended from the literal section U/V₁ restricts
faithfully to A₅. Every residual involution moves at least two dimensions.
Consequently, fixed codimension at most two on a residual Sylow forces its
whole action to be quadratic. Quadratic SL₂(4) recognition then identifies
the quotient by the K-fixed space with the natural four-space. Transporting
the full S₅ action through these coordinates supplies the required outer
action as well, with exactly the original fixed kernel.

The fixed-space index calculation uses relative normalization of V₁ in H;
it does not impose ambient normality in G. The actual residual Sylow maps
onto a Sylow of A₅ through the same star marking. This gives both the lower
index bound four and an application constructing Data from the upper bound.

This is a conditional reduction of the module conclusion, not a proof of
14.7.40 or 14.7.52. The upper index bound and residual classification remain
source obligations; the independent G₂ exclusion is retained explicitly.

Source: Aschbacher–Smith, the final module argument in 14.7.40, printed
p.1063, and the application in 14.7.63, printed p.1069.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
local notation "A5" => alternatingGroup (Fin 5)

/-- On a faithful symmetric action, a residual Sylow of fixed codimension at
most two is automatically quadratic. Every nonidentity element already moves
two dimensions, so its fixed space equals the common Sylow fixed space. -/
theorem symmetric_sylow_quadratic
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) ChapterJ.S5 W) (hf : Function.Injective σ)
    (S : Sylow 2 A5)
    (hd : fixedCodim σ ((S : Subgroup A5).map (A5).subtype) ≤ 2) :
    IsQuadratic σ ((S : Subgroup A5).map (A5).subtype) := by
  let τ : Representation (ZMod 2) A5 W := σ.comp (A5).subtype
  have hτ : Function.Injective τ := hf.comp (A5).subtype_injective
  let e := SL2FourNatural.alternatingFiveEquiv.symm
  let P : Sylow 2 SL2FourNatural.SL := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hsq (a : A5) (ha : a ∈ S) : a ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact (SL2FourNaturalExtensions.sylow_element_natural P (mem_map_of_mem _ ha)).1
  have hdim : fixedCodim τ (S : Subgroup A5) ≤ 2 := by
    change fixedCodim (σ.comp (A5).subtype) (S : Subgroup A5) ≤ 2
    rw [fixedCodim, fixedSpace_comp_map]
    exact hd
  have hquad : IsQuadratic τ (S : Subgroup A5) := by
    apply isQuadratic_of_fixedDimension_bound τ S hsq
      (Module.finrank (ZMod 2) W - 2)
    · intro a ha hn
      have ho : orderOf a = 2 := orderOf_eq_prime (hsq a ha) hn
      have hlo := AlternatingFiveInvolutionDisplacement.displacement_lower τ hτ a ho
      rw [← fixedCodim_zpowers_eq_displacement_rank] at hlo
      have he := fixedCodim_add_finrank τ (zpowers a)
      omega
    · have he := fixedCodim_add_finrank τ (S : Subgroup A5)
      omega
  exact quadratic_map_equivariant τ σ (A5).subtype (LinearEquiv.refl _ _)
    (fun _ _ => rfl) hquad

/-- Extend natural coordinates on the alternating fixed quotient to the entire
symmetric action, preserving the literal fixed kernel. -/
theorem symmetric_natural_quotient
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) ChapterJ.S5 W)
    (hn : σ.comp (A5).subtype ≠ 1) (S : Sylow 2 A5)
    (hq : IsQuadratic σ ((S : Subgroup A5).map (A5).subtype))
    (hd : fixedCodim σ ((S : Subgroup A5).map (A5).subtype) ≤ 2) :
    ∃ (a : ChapterJ.L2FourAction) (p : σ.IntertwiningMap a.action),
      Function.Surjective p ∧ p.toLinearMap.ker = fixedSpace σ A5 := by
  let τ : Representation (ZMod 2) A5 W := σ.comp (A5).subtype
  let q := SL2FourNatural.alternatingFiveEquiv.symm.toMonoidHom
  have hquad : IsQuadratic τ (S : Subgroup A5) := by
    intro a ha b hb w
    exact hq a (mem_map_of_mem (A5).subtype ha) b (mem_map_of_mem (A5).subtype hb) w
  have hdim : fixedCodim τ (S : Subgroup A5) ≤ 2 := by
    change fixedCodim (σ.comp (A5).subtype) (S : Subgroup A5) ≤ 2
    rw [fixedCodim, fixedSpace_comp_map]
    exact hd
  have hk : q.ker ≤ τ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff q).mpr SL2FourNatural.alternatingFiveEquiv.symm.injective]
    exact bot_le
  obtain ⟨E, hE⟩ := SL2FourQuadraticRecognition.natural_fixed_quotient_of_sylow
    τ q SL2FourNatural.alternatingFiveEquiv.symm.surjective hk hn S hquad hdim
  have hfixed : fixedSpace σ A5 = fixedSpace τ ⊤ := by
    change fixedSpace σ A5 = fixedSpace (σ.comp (A5).subtype) ⊤
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, range_subtype]
  let C := fixedSpace σ A5
  let Q := fixedQuotient σ A5
  let e : (W ⧸ C) ≃ₗ[ZMod 2] ChapterJ.FourSpace :=
    (Submodule.quotEquivOfEq _ _ hfixed).trans E
  let a : ChapterJ.L2FourAction := {
    action := e.conjRingEquiv.toMonoidHom.comp Q
    marking := SL2FourNatural.alternatingFiveEquiv
    restriction := by
      intro g v
      obtain ⟨x, rfl⟩ := e.surjective v
      obtain ⟨w, rfl⟩ := C.mkQ_surjective x
      change e (Q (SL2FourNatural.alternatingFiveEquiv g) (e.symm (e (C.mkQ w)))) = _
      rw [e.symm_apply_apply]
      change E ((fixedSpace τ ⊤).mkQ (τ (SL2FourNatural.alternatingFiveEquiv g) w)) = _
      have hh := hE (SL2FourNatural.alternatingFiveEquiv g) ((fixedSpace τ ⊤).mkQ w)
      change E ((fixedSpace τ ⊤).mkQ (τ (SL2FourNatural.alternatingFiveEquiv g) w)) =
        SL2FourNatural.action (SL2FourNatural.alternatingFiveEquiv.symm
          (SL2FourNatural.alternatingFiveEquiv g)) (E ((fixedSpace τ ⊤).mkQ w)) at hh
      simpa only [MulEquiv.symm_apply_apply, e, LinearEquiv.trans_apply,
        Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk] using hh }
  let p : σ.IntertwiningMap a.action := {
    toLinearMap := e.toLinearMap.comp C.mkQ
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro w
      change e (C.mkQ (σ g w)) = e (Q g (e.symm (e (C.mkQ w))))
      rw [e.symm_apply_apply]
      rfl }
  refine ⟨a, p, e.surjective.comp C.mkQ_surjective, ?_⟩
  ext w
  change e (C.mkQ w) = 0 ↔ w ∈ C
  rw [map_eq_zero_iff e e.injective]
  exact Submodule.Quotient.mk_eq_zero C

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The fixed index on U/V₁ only needs relative normalization of V₁.
In particular, the flag point is not assumed normal in the original G. -/
theorem section_fixed_index
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A : Subgroup G) (hAH : A ≤ F.H) :
    (commutatorPreimage F.U A (F.Vi 1)).relIndex F.U =
      2 ^ fixedCodim ρ (A.subgroupOf F.H) := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let C := commutatorPreimage F.U A (F.Vi 1)
  let D : Subgroup (Multiplicative W) :=
    AddSubgroup.toSubgroup' (fixedSpace ρ (A.subgroupOf F.H)).toAddSubgroup
  have hm : (C.subgroupOf F.U).map c.coordinates = D := by
    ext v
    change v.toAdd ∈ c.imageSpace C ↔ v.toAdd ∈ fixedSpace ρ (A.subgroupOf F.H)
    rw [c.fixed_image_eq A hAH c.section_le]
  have hz : F.Vi 1 ≤ C := by
    apply le_commutatorPreimage c.kernel_le
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp hAH
  have hk : c.coordinates.ker ≤ C.subgroupOf F.U := by
    rw [c.kernel_eq]
    exact comap_mono hz
  have hi : D.index = C.relIndex F.U := by
    rw [← hm, index_map_eq _ c.onto hk]
    rfl
  have hc := D.card_mul_index
  have hD : Nat.card D = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ (A.subgroupOf F.H)) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (A.subgroupOf F.H))).trans (by rw [Nat.card_zmod])
  have hW : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).trans
      (by rw [Nat.card_zmod])
  rw [hD, hW, ← fixedCodim_add_finrank ρ (A.subgroupOf F.H), add_comm, pow_add] at hc
  exact hi.symm.trans (Nat.eq_of_mul_eq_mul_left (by positivity) hc)

/-- The original residual maps onto A₅ through the same star marking. -/
def alternatingResidualMap (e : HStar F.H ≃* ChapterJ.S5) : K F →* A5 :=
  ((quotientMarking e).comp (inclusion (show K F ≤ F.H from map_subtype_le _))).codRestrict
    A5 (fun k => by
      rw [← residual_image e]
      exact mem_map_of_mem (quotientMarking e) k.property)

/-- The residual map uses the same star marking as the original H-action. -/
theorem alternatingResidualMap_coe (e : HStar F.H ≃* ChapterJ.S5) (k : K F) :
    (alternatingResidualMap e k : ChapterJ.S5) =
      quotientMarking e ⟨k, (show K F ≤ F.H from map_subtype_le _) k.property⟩ := by rfl

theorem alternatingResidualMap_surjective (e : HStar F.H ≃* ChapterJ.S5) :
    Function.Surjective (alternatingResidualMap e) := by
  intro a
  have ha : (a : ChapterJ.S5) ∈ ((K F).subgroupOf F.H).map (quotientMarking e) := by
    rw [residual_image]
    exact a.property
  obtain ⟨k, hk, he⟩ := ha
  exact ⟨⟨k.val, hk⟩, Subtype.ext he⟩

/-- Mapping a residual Sylow retains the literal original ambient subgroup. -/
theorem residual_sylow_image (e : HStar F.H ≃* ChapterJ.S5)
    (S : Sylow 2 (K F)) :
    (((S.mapSurjective (alternatingResidualMap_surjective e) : Sylow 2 A5) : Subgroup A5).map
      (A5).subtype) =
    ((((S : Subgroup (K F)).map (K F).subtype).subgroupOf F.H).map (quotientMarking e)) := by
  ext a
  constructor
  · rintro ⟨b, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k.val, (show K F ≤ F.H from map_subtype_le _) k.property⟩,
      ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨k, hk, he⟩, rfl⟩
    refine ⟨alternatingResidualMap e k, ⟨k, hk, rfl⟩, ?_⟩
    apply congrArg (quotientMarking e)
    exact Subtype.ext he

/-- The original residual Sylow always has fixed index at least four in
the alternating branch. This uses faithful involution displacement before
natural recognition. -/
theorem residual_sylow_index_lower
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) (S : Sylow 2 (K F)) :
    4 ≤ (commutatorPreimage F.U ((S : Subgroup (K F)).map (K F).subtype)
      (F.Vi 1)).relIndex F.U := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ, ⟨c⟩⟩ := exists_section F
  obtain ⟨e⟩ := exists_symmetric_star h structural hAlt
  obtain ⟨σ, hσ, hinj⟩ := exists_faithful_symmetric_representation h e c
  let τ : Representation (ZMod 2) A5 _ := σ.comp (A5).subtype
  let P : Sylow 2 A5 := S.mapSurjective (alternatingResidualMap_surjective e)
  have hcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (by rw [hcard]; decide)
  have ho : orderOf a.val = 2 := (orderOf_coe a).trans ha
  have hlo := AlternatingFiveInvolutionDisplacement.displacement_lower τ
    (hinj.comp (A5).subtype_injective) a.val ho
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hlo
  have hle : fixedSpace τ (P : Subgroup A5) ≤ fixedSpace τ (zpowers a.val) :=
    fixedSpace_antitone τ (zpowers_le.mpr a.property)
  have hr := Submodule.finrank_mono hle
  have hp := fixedCodim_add_finrank τ (P : Subgroup A5)
  have ha' := fixedCodim_add_finrank τ (zpowers a.val)
  have hd : 2 ≤ fixedCodim τ (P : Subgroup A5) := by omega
  have hx := section_fixed_index c ((S : Subgroup (K F)).map (K F).subtype)
    ((map_subtype_le _).trans (map_subtype_le _))
  rw [← hσ, fixedCodim, fixedSpace_comp_map] at hx
  rw [← residual_sylow_image e S] at hx
  have hfix : fixedCodim τ (P : Subgroup A5) =
      fixedCodim σ ((P : Subgroup A5).map (A5).subtype) := by
    exact fixedCodim_map_equivariant τ σ (A5).subtype (LinearEquiv.refl _ _)
      (fun _ _ => rfl) (P : Subgroup A5)
  change _ = 2 ^ fixedCodim σ ((P : Subgroup A5).map (A5).subtype) at hx
  rw [hx, ← hfix]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hd

/-- Fixed index at most four on an actual residual Sylow
constructs the source's full natural-module quotient, in arbitrary coordinates. -/
theorem naturalRecognition_of_sylow_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) (S : Sylow 2 (K F))
    (hi : (commutatorPreimage F.U ((S : Subgroup (K F)).map (K F).subtype)
      (F.Vi 1)).relIndex F.U ≤ 4) : NaturalRecognition F := by
  intro W _ _ ρ c
  let : Finite W := Finite.of_surjective (fun u : F.U => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨e⟩ := exists_symmetric_star h structural hAlt
  obtain ⟨σ, hσ, hinj⟩ := exists_faithful_symmetric_representation h e c
  let c' : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (quotientMarking e)) :=
    hσ.symm ▸ c
  let A := (S : Subgroup (K F)).map (K F).subtype
  have hAH : A ≤ F.H := (map_subtype_le _).trans (map_subtype_le _)
  let P : Sylow 2 A5 := S.mapSurjective (alternatingResidualMap_surjective e)
  have hP := residual_sylow_image e S
  have hdim : fixedCodim σ ((P : Subgroup A5).map (A5).subtype) ≤ 2 := by
    have hx := section_fixed_index c' A hAH
    rw [fixedCodim, fixedSpace_comp_map] at hx
    rw [hP]
    have hp : 2 ^ fixedCodim σ ((A.subgroupOf F.H).map (quotientMarking e)) ≤ 2 ^ 2 :=
      hx ▸ hi
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  have hquad := symmetric_sylow_quadratic σ hinj P hdim
  have hn : σ.comp (A5).subtype ≠ 1 := by
    intro he
    have htriv : (A5).subtype = (1 : A5 →* ChapterJ.S5) := by
      apply MonoidHom.ext
      intro a
      apply hinj
      have hx := congrArg (fun τ : Representation (ZMod 2) A5 W => τ a) he
      exact hx.trans (map_one σ).symm
    have hbot : A5 = ⊥ := by
      rw [← range_subtype A5, htriv]
      simp
    have hc : Nat.card A5 = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hbot] at hc
    simp at hc
  obtain ⟨a, p, hp, hk⟩ := symmetric_natural_quotient σ hn P hquad hdim
  let p' : ρ.IntertwiningMap (a.action.comp (quotientMarking e)) := {
    toLinearMap := p.toLinearMap
    isIntertwining' := by
      intro g
      rw [← hσ]
      exact p.isIntertwining' (quotientMarking e g) }
  refine ⟨e, a, p', hp, ?_⟩
  change p.toLinearMap.ker = fixedSpace ρ ((K F).subgroupOf F.H)
  rw [hk, ← hσ, fixedSpace_comp_map, residual_image]

/-- Application to the original source constructor. The natural-recognition
callback is replaced by an explicit index bound on the literal
residual Sylow. The source classification and G₂ exclusion remain separate. -/
theorem exists_data_of_sylow_index
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (h52 : AlternatingResidual F ∨ G2Residual F) (h53 : ¬ G2Residual F)
    (S : Sylow 2 (K F))
    (hi : (commutatorPreimage F.U ((S : Subgroup (K F)).map (K F).subtype)
      (F.Vi 1)).relIndex F.U ≤ 4) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact exists_data_of_recognition_branches d h hab structural h52 h53
    (fun ha => naturalRecognition_of_sylow_index h structural ha S hi)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
