module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Actions

/-!
# Covers and marked root parameters for nonbinary exceptional point pairs

Offenders in the full ambient action lie in its marked component. The
nonbinary orthogonal-cover theorem then identifies the embedded central
kernel by its non-single-commutator property. The same component marking
parametrizes the offender by all three root curves, with the exact quotient
kernel retained. G2Critical and G2Exclusion use these two conclusions.

This extends the corresponding LineAction/G2 moving-cover and root-coordinate
arguments to every nonbinary field. Source: MS93 (1.5)(iv), p.843, and (3.2),
pp.865--866; Aschbacher--Smith 11.1.5, p.765. The reused octonion model is
attributed in LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
variable {n : ℕ}
open Atlas.G2
/-- The kernel criterion on the actual ambient moved-section action. The
critical actor's containment in the component is deduced from offending. -/
theorem moved_cover_offender_kernel
    {J V : Type*} [Group J] [Finite J] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (E : BinaryField) (hE : 1 < E.degree)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryG2 E))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hf : Function.Injective (MovedSection.ambientAction s e))
    (A : Subgroup J) (hA : IsOffender (MovedSection.ambientAction s e) A) :
    (MovedSection.coverProjection s e).toLinearMap.ker ≤
      Coinvariants.ker (s.space.toRepresentation.comp A.subtype) ∧
    ∀ w : s.space.toSubmodule,
      w ∈ Coinvariants.ker (s.space.toRepresentation.comp A.subtype) → w ≠ 0 →
      (MovedSection.coverProjection s e w = 0 ↔
        ¬ ∃ a ∈ A, ∃ v, s.space.toRepresentation a v - v = w) := by
  have hAB := (ambient_offender_rank E hE (MovedSection.ambientAction s e) B
    e.groupEquiv (MovedSection.ambientAction_component s e) hf A hA).1
  let C := (A.subgroupOf B).map e.groupEquiv.toMonoidHom
  have hC : IsOffender (NaturalOffenders.binaryNatural (F := E.Carrier)) C :=
    (hA.subgroupOf _ hAB).map_equivariant ((MovedSection.ambientAction s e).comp B.subtype)
      (NaturalOffenders.binaryNatural (F := E.Carrier)) e.groupEquiv.toMonoidHom
      e.groupEquiv.injective (LinearEquiv.refl (ZMod 2) _)
      (fun b v => MovedSection.ambientAction_component s e b v)
  have hc (a : C) : (e.groupEquiv.symm a.val : J) ∈ A := by
    obtain ⟨b,hb,hb'⟩ := a.property
    rw [←hb']
    change (e.groupEquiv.symm (e.groupEquiv b)).val ∈ A
    rw [e.groupEquiv.symm_apply_apply]
    exact hb
  have ha (a : A) : e.groupEquiv ⟨a.val,hAB a.property⟩ ∈ C :=
    mem_map_of_mem e.groupEquiv.toMonoidHom a.property
  have hm : Coinvariants.ker ((MovedSection.coverAction s e).comp C.subtype) =
      Coinvariants.ker (s.space.toRepresentation.comp A.subtype) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := s.space.toRepresentation.comp A.subtype)
        ⟨(e.groupEquiv.symm a.val : J),hc a⟩ v
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩,rfl⟩
      have hh := Coinvariants.sub_mem_ker
        (ρ := (MovedSection.coverAction s e).comp C.subtype)
        ⟨e.groupEquiv ⟨a.val,hAB a.property⟩,ha a⟩ v
      change s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv ⟨a.val,hAB a.property⟩)) v - v ∈ _ at hh
      rw [e.groupEquiv.symm_apply_apply] at hh
      exact hh
  have hcard : Nat.card E.Carrier = 2^E.degree := E.card_eq
  refine ⟨?_,?_⟩
  · rw [←hm]
    exact full_cover_offender_kernel_le_moved (MovedSection.coverAction s e)
      hcard hE (MovedSection.coverProjection s e) hp C hC
  · intro w hw hne
    rw [full_cover_offender_kernel (MovedSection.coverAction s e) hcard hE
      (MovedSection.coverProjection s e) hp C hC w (hm.symm ▸ hw) hne]
    apply not_congr
    constructor
    · rintro ⟨c,hc',v,he⟩
      exact ⟨(e.groupEquiv.symm c : J),hc ⟨c,hc'⟩,v,he⟩
    · rintro ⟨a,ha',v,he⟩
      refine ⟨e.groupEquiv ⟨a,hAB ha'⟩,ha ⟨a,ha'⟩,v,?_⟩
      change s.space.toRepresentation (e.groupEquiv.symm (e.groupEquiv ⟨a,hAB ha'⟩)) v - v = w
      rwa [e.groupEquiv.symm_apply_apply]

private theorem embedded_displacement
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (A : Subgroup G) (σ : Representation (ZMod 2) J W)
    (j : Multiplicative W →* G) (δ : A →* J)
    (hc : ∀ (a : A) w, j (Multiplicative.ofAdd (σ (δ a) w)) =
      a.val * j (Multiplicative.ofAdd w) * a.val⁻¹)
    (a : A) (w : W) :
    j (Multiplicative.ofAdd (σ (δ a) w - w)) =
      ⁅a.val,j (Multiplicative.ofAdd w)⁆ := by
  rw [ofAdd_sub,map_div,div_eq_mul_inv,hc]
  rfl

private theorem embedded_moved_group
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (A U : Subgroup G) (σ : Representation (ZMod 2) J W)
    (j : Multiplicative W →* G) (hjr : j.range = U) (δ : A →* J)
    (hc : ∀ (a : A) w, j (Multiplicative.ofAdd (σ (δ a) w)) =
      a.val * j (Multiplicative.ofAdd w) * a.val⁻¹) :
    (Coinvariants.ker (σ.comp δ.range.subtype)).toAddSubgroup.toSubgroup.map j = ⁅A,U⁆ := by
  let P := AddSubgroup.toZModSubmodule 2 ((⁅A,U⁆).comap j).toAddSubgroup'
  have hle : Coinvariants.ker (σ.comp δ.range.subtype) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨a,ha⟩,w⟩,rfl⟩
    obtain ⟨b,rfl⟩ := ha
    change j (Multiplicative.ofAdd (σ (δ b) w - w)) ∈ ⁅A,U⁆
    rw [embedded_displacement A σ j δ hc]
    exact commutator_mem_commutator b.property (hjr ▸ ⟨_,rfl⟩)
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact hle hw
  · apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨w,rfl⟩ := show u ∈ j.range from hjr.symm ▸ hu
    refine ⟨Multiplicative.ofAdd (σ (δ ⟨a,ha⟩) w.toAdd - w.toAdd),?_,?_⟩
    · exact Coinvariants.sub_mem_ker (ρ := σ.comp δ.range.subtype) ⟨δ ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ w.toAdd
    · exact embedded_displacement A σ j δ hc ⟨a,ha⟩ w.toAdd

/-- Transport the central-kernel criterion through an original conjugation
embedding, with the original actor and subgroup commutator retained. -/
theorem embedded_offender_kernel
    {G J V : Type*} [Group G] [Group J] [Finite J]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (F : BinaryField) (hF : 1 < F.degree)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryG2 F))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hf : Function.Injective (MovedSection.ambientAction s e))
    (A U K : Subgroup G) (j : Multiplicative s.space.toSubmodule →* G)
    (hj : Function.Injective j) (hjr : j.range = U) (δ : A →* J)
    (hconj : ∀ (a : A) w, j (Multiplicative.ofAdd (s.space.toRepresentation (δ a) w)) =
      a.val * j (Multiplicative.ofAdd w) * a.val⁻¹)
    (hK : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j = K)
    (hA : BinaryOffender.IsOffender (MovedSection.ambientAction s e) δ.range) :
    K ≤ ⁅A,U⁆ ∧ ∀ x ∈ ⁅A,U⁆, x ≠ 1 →
      (x ∈ K ↔ ¬ ∃ a ∈ A, ∃ u ∈ U, ⁅a,u⁆ = x) := by
  obtain ⟨hle,hcrit⟩ := moved_cover_offender_kernel F hF s e hp hf δ.range hA
  have hm := embedded_moved_group A U s.space.toRepresentation j hjr δ hconj
  refine ⟨?_,?_⟩
  · rw [←hK,←hm]
    exact map_mono hle
  · intro x hx hne
    obtain ⟨w,hw,rfl⟩ := hm.symm ▸ hx
    have hwne : w.toAdd ≠ 0 := by
      intro hz
      apply hne
      have he : w = 1 := congrArg Multiplicative.ofAdd hz
      rw [he,map_one]
    have hmem : j w ∈ K ↔ MovedSection.coverProjection s e w.toAdd = 0 := by
      rw [←hK]
      constructor
      · rintro ⟨v,hv,he⟩
        exact hj he ▸ hv
      · intro hv
        exact ⟨w,hv,rfl⟩
    rw [hmem,hcrit w.toAdd hw hwne]
    apply not_congr
    constructor
    · rintro ⟨d,⟨a,rfl⟩,v,hv⟩
      refine ⟨a,a.property,j (Multiplicative.ofAdd v),hjr ▸ ⟨_,rfl⟩,?_⟩
      rw [←embedded_displacement A s.space.toRepresentation j δ hconj,hv]
      rfl
    · rintro ⟨a,ha,u,hu,he⟩
      obtain ⟨v,rfl⟩ := show u ∈ j.range from hjr.symm ▸ hu
      refine ⟨δ ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,v.toAdd,?_⟩
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [embedded_displacement A s.space.toRepresentation j δ hconj]
      exact he


open Atlas.G2

/-- An actual offender is parametrized by all three marked root curves, with
one common conjugator and the original component inclusion. -/
theorem inner_offender_parameters
    {A J : Type*} [Group A] [Group J] [Finite J]
    (F : BinaryField) (hF : 1 < F.degree)
    (ρ : Representation (ZMod 2) J (Natural.Space F.Carrier))
    (B : Subgroup J) [B.Normal] (e : B ≃* Model F.Carrier)
    (he : ∀ (b : B) v, ρ (b : J) v = Natural.action F.Carrier (e b) v)
    (hf : Function.Injective ρ) (δ : A →* J) (hδ : IsOffender ρ δ.range) :
    ∃ g : Model F.Carrier, ∃ p : A →* Multiplicative (Fin 3 → F.Carrier),
      Function.Surjective p ∧ p.ker = δ.ker ∧
      ∀ x, δ x = (e.symm (g * EvenTwoRank.elementaryEmbedding F.Carrier (p x) * g⁻¹) : J) := by
  obtain ⟨hin,_,_⟩ := ambient_offender_rank F hF ρ B e he hf δ.range hδ
  let β : A →* Model F.Carrier := e.toMonoidHom.comp (δ.codRestrict B (fun x => hin ⟨x,rfl⟩))
  have hβrange : β.range = (δ.range.subgroupOf B).map e.toMonoidHom := by
    rw [MonoidHom.subgroupOf_range_eq_of_le δ hin]
    exact MonoidHom.range_comp _ _
  have hβoff : IsOffender (NaturalOffenders.binaryNatural (F := F.Carrier)) β.range := by
    rw [hβrange]
    exact (hδ.subgroupOf ρ hin).map_equivariant (ρ.comp B.subtype)
      (NaturalOffenders.binaryNatural (F := F.Carrier)) e.toMonoidHom e.injective
      (LinearEquiv.refl (ZMod 2) _) (fun b v => he b v)
  have hc : Nat.card F.Carrier = 2^F.degree := F.card_eq
  obtain ⟨g,hg⟩ := NaturalOffenders.natural_offender_conjugate_elementary hc (by omega) β.range hβoff
  let γ := (MulAut.conj g⁻¹).toMonoidHom.comp β
  have hγrange : γ.range = EvenTwoRank.elementary F.Carrier := by
    apply le_antisymm
    · rintro x ⟨a,rfl⟩
      have hb : β a ∈ (EvenTwoRank.elementary F.Carrier).map (MulAut.conj g).toMonoidHom :=
        hg ▸ (show β a ∈ β.range from ⟨a,rfl⟩)
      obtain ⟨b,hb,heq⟩ := hb
      change g⁻¹ * β a * (g⁻¹)⁻¹ ∈ _
      rw [←heq]
      simpa [MulAut.conj_apply,mul_assoc] using hb
    · intro x hx
      have hm : g*x*g⁻¹ ∈ β.range := by
        rw [hg]
        exact mem_map_of_mem (MulAut.conj g).toMonoidHom hx
      obtain ⟨a,ha⟩ := hm
      exact ⟨a,by simp [γ,ha,mul_assoc]⟩
  let r := γ.codRestrict (EvenTwoRank.elementary F.Carrier) (fun x => hγrange ▸ ⟨x,rfl⟩)
  let p := (EvenTwoRank.elementaryEquiv F.Carrier).symm.toMonoidHom.comp r
  have hp (x : A) : EvenTwoRank.elementaryEmbedding F.Carrier (p x) = γ x :=
    MonoidHom.apply_ofInjective_symm (EvenTwoRank.elementaryEmbedding_injective F.Carrier) (r x)
  refine ⟨g,p,?_,?_,?_⟩
  · apply (EvenTwoRank.elementaryEquiv F.Carrier).symm.surjective.comp
    intro x
    obtain ⟨a,ha⟩ := (show x.val ∈ γ.range from hγrange.symm ▸ x.property)
    exact ⟨a,Subtype.ext ha⟩
  · ext x
    change p x = 1 ↔ δ x = 1
    rw [←(EvenTwoRank.elementaryEmbedding_injective F.Carrier).eq_iff,map_one,hp]
    change g⁻¹ * e ⟨δ x,hin ⟨x,rfl⟩⟩ * (g⁻¹)⁻¹ = 1 ↔ _
    change (MulAut.conj g⁻¹) (e ⟨δ x,hin ⟨x,rfl⟩⟩) = 1 ↔ _
    rw [(MulAut.conj g⁻¹).map_eq_one_iff,e.map_eq_one_iff]
    exact Subtype.ext_iff
  · intro x
    change (⟨δ x,hin ⟨x,rfl⟩⟩ : B).val = _
    apply congrArg Subtype.val
    apply e.injective
    change β x = e (e.symm _)
    rw [e.apply_symm_apply,hp]
    simp [γ,mul_assoc]

open Atlas.G2.Restricted.NaturalCoordinates

private theorem elementary_action_displacement {F : Type*} [Field F] [CharP F 2]
    (p : Multiplicative (Fin 3 → F)) (v : Fin 6 → F) :
    action F (EvenTwoRank.elementaryEmbedding F p) v - v =
      ![rootDisplacement p.toAdd ![v 3,v 4,v 5] 0,
        rootDisplacement p.toAdd ![v 3,v 4,v 5] 1,
        rootDisplacement p.toAdd ![v 3,v 4,v 5] 2,0,0,0] := by
  have he : EvenTwoRank.elementaryEmbedding F p =
      rootA (p.toAdd 0) * (rootB (p.toAdd 1) * rootC (p.toAdd 2)) := by
    simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,
      unipotentProduct,mul_assoc]
  rw [he,map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply]
  ext i
  fin_cases i <;> simp [rootDisplacement] <;> ring

/-- Coordinates use the same conjugator on all root parameters. -/
theorem inner_offender_displacement_coordinates
    {A J : Type*} [Group A] [Group J] [Finite J]
    (F : BinaryField) (hF : 1 < F.degree)
    (ρ : Representation (ZMod 2) J (Natural.Space F.Carrier))
    (B : Subgroup J) [B.Normal] (e : B ≃* Model F.Carrier)
    (he : ∀ (b : B) v, ρ (b : J) v = Natural.action F.Carrier (e b) v)
    (hf : Function.Injective ρ) (δ : A →* J) (hδ : IsOffender ρ δ.range) :
    ∃ p : A →* Multiplicative (Fin 3 → F.Carrier), Function.Surjective p ∧
      p.ker = δ.ker ∧ ∃ η : Natural.Space F.Carrier ≃ₗ[F.Carrier] (Fin 6 → F.Carrier),
      ∀ x v, η (ρ (δ x) v) - η v =
        ![rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 0,
          rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 1,
          rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 2,0,0,0] := by
  obtain ⟨g,p,hp,hk,hmark⟩ := inner_offender_parameters F hF ρ B e he hf δ hδ
  let η := (LinearMap.GeneralLinearGroup.toLinearEquiv ((Natural.action F.Carrier).asGroupHom g⁻¹)).trans (equiv F.Carrier)
  refine ⟨p,hp,hk,η,?_⟩
  intro x v
  have ht : η (ρ (δ x) v) = action F.Carrier (EvenTwoRank.elementaryEmbedding F.Carrier (p x)) (η v) := by
    change equiv F.Carrier (Natural.action F.Carrier g⁻¹ (ρ (δ x) v)) = _
    rw [hmark,he,e.apply_symm_apply]
    have hg : g⁻¹ * (g * EvenTwoRank.elementaryEmbedding F.Carrier (p x) * g⁻¹) =
        EvenTwoRank.elementaryEmbedding F.Carrier (p x) * g⁻¹ := by group
    rw [←Module.End.mul_apply,←map_mul,hg,map_mul,Module.End.mul_apply]
    exact LinearMap.congr_fun ((repEquiv F.Carrier).isIntertwining' _) _
  rw [ht]
  exact elementary_action_displacement (p x) (η v)



end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
