module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.Reduction
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The literal offender on the binary central cover

When L⁺ is the whole faithful seed quotient, the original L-action on U and
that quotient action are equivariantly isomorphic. Pull the prepared best
offender back along this identification and apply the cover's offender clause
with its own natural-module group isomorphism. A full-center subgroup of
SL₃(2) is the actual point-stabilizer kernel: displacement identifies it with
Hom(U/P,P), a two-dimensional binary space. This proves that the literal
seed offender image is a Klein four-group.

The same action identification transports the cover's quadratic ratio one
and supplies the exact rank equality consumed by B.1.5. These are conditional
comparison results: construction of the four-dimensional cover remains with
its independent source producer. Neither U=[V,L] nor A≤L is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.8(2),
printed p.91, and the proof of B.5.9, printed p.107, case (V).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers
open QuasisimpleSource
open Theory.LinearAlgebra.BinaryFivePointStabilizer BinaryLinear.OuterCyclic

/-- The full subgroup with a common transvection center in SL₃(2) is Klein four.
The isomorphism uses its actual displacement into the fixed line. -/
theorem fullCenter_klein
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hA : IsFullCenterGroup BinaryField.two 3 A) :
    Nonempty (A ≃* Multiplicative (Fin 2 → ZMod 2)) := by
  change ∃ P : Submodule (ZMod 2) (Fin 3 → ZMod 2),
    Module.finrank (ZMod 2) P = 1 ∧
      ∀ g, g ∈ A ↔ ∀ v, specialLinearNatural 3 g v - v ∈ P at hA
  obtain ⟨P, hP, hA⟩ := hA
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h] at hP
    simp at hP
  obtain ⟨z, hzP, hz⟩ := P.ne_bot_iff.mp hP0
  have hPe : P = line z := eq_span_singleton_of_mem_of_finrank_eq_one hP hzP hz
  let e := slEquivLinear 3
  have hmem (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      g ∈ A ↔ ∀ v, e g v - v ∈ line z := by
    simpa only [hPe, e, slEquivLinear_apply, specialLinearNatural_apply] using hA g
  have hfix (g : A) : e g.val z = z := by
    have hp : e g.val z ∈ line z := by
      simpa only [sub_add_cancel] using
        (line z).add_mem ((hmem g.val).mp g.property z) (Submodule.mem_span_singleton_self z)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hp
    have ha0 : a ≠ 0 := by
      intro h
      have hg : e g.val z = 0 := by simpa [h] using ha.symm
      exact hz ((e g.val).map_eq_zero_iff.mp hg)
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    simpa [ha1] using ha.symm
  let f : A →* kernel z :=
    { toFun := fun g => ⟨⟨e g.val, hfix g⟩,
        (mem_kernel_iff z _).mpr ((hmem g.val).mp g.property)⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact e.map_one
      map_mul' := fun g h => by
        apply Subtype.ext; apply Subtype.ext; exact e.map_mul g.val h.val }
  have hf : Function.Bijective f := by
    constructor
    · intro g h he
      apply Subtype.ext
      apply e.injective
      exact congrArg (fun k : kernel z => k.val.val) he
    · intro k
      let g := e.symm k.val.val
      have hg : g ∈ A := (hmem g).mpr (by
        simpa only [g, e.apply_symm_apply] using (mem_kernel_iff z k.val).mp k.property)
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact e.apply_symm_apply k.val.val
  have hq : Module.finrank (ZMod 2) (QuotientSpace z) = 2 := by
    have hd := (line z).finrank_quotient_add_finrank
    rw [finrank_span_singleton hz] at hd
    norm_num at hd ⊢
    change Module.finrank (ZMod 2) ((Fin 3 → ZMod 2) ⧸ line z) = 2
    omega
  have hd : Module.finrank (ZMod 2) (QuotientSpace z →ₗ[ZMod 2] line z) =
      Module.finrank (ZMod 2) (Fin 2 → ZMod 2) := by
    rw [Module.finrank_linearMap, hq, finrank_span_singleton hz]
    simp
  let a := LinearEquiv.ofFinrankEq _ _ hd
  exact ⟨(MulEquiv.ofBijective f hf).trans
    ((kernelDisplacementEquiv z).trans a.toAddEquiv.toMultiplicative)⟩

section Transport
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

private def symmAction (e : ActionEquiv ρ σ) : ActionEquiv σ ρ where
  groupEquiv := e.groupEquiv.symm
  linearEquiv := e.linearEquiv.symm
  intertwines g w := by
    apply e.linearEquiv.injective
    rw [e.linearEquiv.apply_symm_apply, e.intertwines,
      e.groupEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply]

private theorem elementary_map (e : G ≃* H) {A : Subgroup G}
    (hA : IsElementaryTwo A) : IsElementaryTwo (A.map e.toMonoidHom) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro h
  apply hA.1
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_bot] using h

private theorem weight_map (e : ActionEquiv ρ σ) (A : Subgroup G) :
    weight σ (A.map e.groupEquiv.toMonoidHom) = weight ρ A := by
  unfold weight
  rw [rank_map_injective _ e.groupEquiv.injective,
    ← fixedSpace_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
    LinearEquiv.finrank_map_eq]

private theorem best_map (e : ActionEquiv ρ σ) {A : Subgroup G}
    (hA : IsBestOffender ρ A) : IsBestOffender σ (A.map e.groupEquiv.toMonoidHom) := by
  refine ⟨elementary_map e.groupEquiv hA.1, ?_⟩
  intro B hB
  have hm : (B.map e.groupEquiv.symm.toMonoidHom).map e.groupEquiv.toMonoidHom = B := by
    rw [map_map]; simp
  have hle : B.map e.groupEquiv.symm.toMonoidHom ≤ A := by
    have h := Subgroup.map_mono (f := e.groupEquiv.symm.toMonoidHom) hB
    simpa [map_map] using h
  rw [← hm, weight_map, weight_map]
  exact hA.2 _ hle

private theorem quadratic_map (e : ActionEquiv ρ σ) {A : Subgroup G}
    (hA : IsQuadratic ρ A) : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  have h := congrArg e.linearEquiv (hA a ha b hb v)
  change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
    σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
  simpa only [e.intertwines, map_sub] using h

private theorem ratio_le (e : ActionEquiv ρ σ) : quadraticRatio σ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hq⟩
  have hr : actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
    unfold actionRatio
    rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
      rank_map_injective _ e.groupEquiv.injective]
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom)
    (iInf_le_of_le ⟨elementary_map e.groupEquiv hA, quadratic_map e hq⟩ hr.le)

private theorem ratio_eq (e : ActionEquiv ρ σ) : quadraticRatio ρ = quadraticRatio σ :=
  le_antisymm (ratio_le (symmAction e)) (ratio_le e)

variable [Finite G]

/-- Identify the original L-action on U with the entire faithful seed action
when L⁺ is the whole quotient. The intertwiner is the identity on U. -/
noncomputable def seedWholeActionEquiv (ρ : Representation (ZMod 2) G V)
    {K : GroupClass} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (htop : seedComponentImage ρ hLA = ⊤) :
    ActionEquiv (seedComponentAction ρ hLA) (seedQuotientAction ρ hLA) where
  groupEquiv := (seedComponentEquiv ρ hLA p).trans
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  linearEquiv := (seedComponentActionEquiv ρ hLA p).linearEquiv
  intertwines g v := (seedComponentActionEquiv ρ hLA p).intertwines g v

end Transport
universe u v

variable {G : Type u} [Group G] [Finite G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- B.4.8(2)'s full-center description applies to the literal prepared offender
image, pulled back to the original component and mapped by the cover marking. -/
theorem seedOffenderImage_klein_of_cover {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (htop : seedComponentImage ρ hLA = ⊤)
    (cover : FourDimensionalCoverSource (seedComponentAction ρ hLA)) :
    Nonempty (seedOffenderImage ρ hLA ≃* Multiplicative (Fin 2 → ZMod 2)) := by
  let e := seedWholeActionEquiv ρ hLA p htop
  let B := (seedOffenderImage ρ hLA).map e.groupEquiv.symm.toMonoidHom
  have hb : IsBestOffender (seedComponentAction ρ hLA) B :=
    best_map (symmAction e) p.minimal.1
  obtain ⟨k⟩ := fullCenter_klein (B.map cover.natural.groupEquiv.toMonoidHom)
    ((cover.offenders B).mp hb)
  exact ⟨(e.groupEquiv.symm.subgroupMap (seedOffenderImage ρ hLA)).trans
    ((cover.natural.groupEquiv.subgroupMap B).trans k)⟩

/-- Transport the cover's ratio through the same whole-actor identification. -/
theorem seedQuotient_ratio_one_of_cover {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (htop : seedComponentImage ρ hLA = ⊤)
    (cover : FourDimensionalCoverSource (seedComponentAction ρ hLA)) :
    quadraticRatio (seedQuotientAction ρ hLA) = 1 :=
  (ratio_eq (seedWholeActionEquiv ρ hLA p htop)).symm.trans cover.ratio

/-- The literal B.1.5 rank-equality consumer for the exceptional-cover branch. -/
theorem seedRankEquality_of_cover {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (htop : seedComponentImage ρ hLA = ⊤)
    (cover : FourDimensionalCoverSource (seedComponentAction ρ hLA)) :
    SeedRankEquality ρ A L :=
  seedRankEquality_of_quotient_ratio_one ρ hLA p
    (seedQuotient_ratio_one_of_cover ρ hLA p htop cover)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers
