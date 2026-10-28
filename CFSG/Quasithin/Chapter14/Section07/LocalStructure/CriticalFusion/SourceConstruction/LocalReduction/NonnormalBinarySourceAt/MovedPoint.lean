module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Reciprocal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryReciprocal
public import Theory.Representation.OrthogonalFourPlusMatrix.RankTwoMovedPoint
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# The nonsingular moved point of the original exchanged critical actor

Coordinates on the entire original U/V₁ extend its normal component-orbit
action to the determinant normalizer. The actual critical involution has
binary displacement rank two, so its full moved space is a nonsingular
F₄-point. The literal order-eight commutator maps onto exactly this point;
the reciprocal central point survives in it and is nonsingular.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1057–1058,
refs/quasithin.pdf. The later local Y and weak-closure construction remain
separate source obligations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components

private theorem orthogonal_coordinates {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (hf : Function.Injective σ)
    (N : Subgroup D) [N.Normal] (hm : HasOrthogonalFourOrbit σ N) :
    ∃ (E : W ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Binary.V)
      (j : D →* linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action),
      Function.Injective j ∧ ∀ g v, E (σ g v) =
        normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action (j g) (E v) := by
  obtain ⟨f,e,he⟩ := hm
  let a := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  have hE (g : N) (v : W) : E (σ g v) =
      ClassicalOrthogonal.FourPlusMatrix.Binary.action (a g) (E v) := by
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates (e (σ g v)) = _
    rw [he,OrthogonalEight.binaryCoordinates_equivariant]
    rfl
  let γ : Representation (ZMod 2) D ClassicalOrthogonal.FourPlusMatrix.Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp σ
  have he' (g : D) (v : W) : E (σ g v) = γ g (E v) := by
    change E (σ g v) = E (σ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hres (g : N) : γ g = ClassicalOrthogonal.FourPlusMatrix.Binary.action (a g) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [←he']
    exact hE g w
  have him : N.map γ.asGroupHom = actionImage ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
    ext z
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨a ⟨g,hg⟩,Units.ext (hres ⟨g,hg⟩).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := a.surjective g
      exact ⟨g,g.property,Units.ext (hres g)⟩
  have hn (g : D) : γ.asGroupHom g ∈ linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
    change γ.asGroupHom g ∈ normalizer (actionImage ClassicalOrthogonal.FourPlusMatrix.Binary.action : Set _)
    rw [←him]
    exact N.le_normalizer_map γ.asGroupHom (mem_map_of_mem _
      (show g ∈ normalizer (N : Set D) from le_normalizer_of_normal (mem_top g)))
  let j := γ.asGroupHom.codRestrict _ hn
  refine ⟨E,j,?_,he'⟩
  intro x y heq
  exact hf (E.conjRingEquiv.injective (congrArg (fun z : linearNormalizer
    ClassicalOrthogonal.FourPlusMatrix.Binary.action => z.val.val) heq))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The selected original actor moves one full nonsingular F₄-point, and
its reciprocal point has a nonzero image on that same literal section. -/
theorem local_nonnormal_component_nonsingular_moved_point_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ hU : IsElementaryAbelian 2 F.U,
      letI := hU
      ∃ a : LocalQuotientAction F.H F.U (F.Vi 1),
      ∃ s : BinaryConjugationSection F.H F.U (F.Vi 1)
          (a.representation.comp (starMap F)),
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
        ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
        ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
        (F.Vi 1 ⊔ c.Zα : Subgroup G) ≤ ⁅F.U,c.Uα⁆ ∧
        ⁅F.U,c.Uα⁆ ≤ F.U ⊓ c.Uα ∧
        Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4 ∧
        Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
        ∃ (E : Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U) ≃ₗ[ZMod 2]
            ClassicalOrthogonal.FourPlusMatrix.Binary.V)
          (j : HStar F.H →* linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action),
          Function.Injective j ∧
          (∀ g v, E (a.representation g v) =
            normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action (j g) (E v)) ∧
          ∃ t : HStar F.H, zpowers t = star F c.Uα ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
            (s.imageSpace ⁅F.U,c.Uα⁆).map E.toLinearMap =
              LinearMap.range ((j t).val.val - LinearMap.id) ∧
            ∃ v : ClassicalOrthogonal.FourPlusMatrix.Binary.V, v.det ≠ 0 ∧
              (s.imageSpace ⁅F.U,c.Uα⁆).map E.toLinearMap =
                (Submodule.span ClassicalOrthogonal.FourPlusMatrix.Binary.F {v}).restrictScalars (ZMod 2) ∧
              ∃ z ∈ s.imageSpace c.Zα, z ≠ 0 ∧ (E z).det ≠ 0 := by
  obtain ⟨hU,a,hm,s,c,hs,hR,hcard,hindex,hcod,hcomm,hrev,hdisj,hplane,hCU,hE4,hfour,height,hdim⟩ :=
    local_nonnormal_component_reciprocal_plane_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := hU
  obtain ⟨t₀,ht₀,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := b.orbit_normal
  have hm' : HasOrthogonalFourOrbit a.representation b.orbit := horbit.symm ▸ hm
  obtain ⟨E,j,hj,hE⟩ := orthogonal_coordinates a.representation a.faithful b.orbit hm'
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨t,ht⟩ := exists_ne (1 : A)
  have ht1 : (t : HStar F.H) ≠ 1 := fun hh => ht (Subtype.ext hh)
  have ht2 : (t : HStar F.H) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    change t ^ Nat.card A = 1 at hh
    rw [show Nat.card A = 2 from hcard] at hh
    exact congrArg Subtype.val hh
  have hz : zpowers (t : HStar F.H) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card hcard ht)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hj2 : (j t) ^ 2 = 1 := by rw [←map_pow,ht2,map_one]
  have hjrank : operatorFixedCodim (j t).val.val = 2 := by
    have hh : fixedCodim a.representation A = operatorFixedCodim (j t).val.val := by
      calc
        fixedCodim a.representation A =
            fixedCodim (normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action)
              (A.map j) := fixedCodim_map_equivariant _ _ j E hE A
        _ = operatorFixedCodim (j t).val.val := by
          conv_lhs => rw [←hz,MonoidHom.map_zpowers,fixedCodim_zpowers_eq_displacement_rank]
          rfl
    exact hh.symm.trans hcod
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  have hsr : s.imageSpace ⁅F.U,c.Uα⁆ = (a.representation t - LinearMap.id).range := by
    rw [commutator_comm,s.imageSpace_commutator c.Uα F.U hAH le_rfl,s.imageSpace_self,
      subspaceCommutator_comp_map]
    change subspaceCommutator a.representation ⊤ A = _
    conv_lhs => rw [←hz,CyclicFixedRank.commutator_eq_range]
  have hmap : (s.imageSpace ⁅F.U,c.Uα⁆).map E.toLinearMap =
      LinearMap.range ((j t).val.val - LinearMap.id) := by
    rw [hsr]
    ext w
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      refine ⟨E x,?_⟩
      change (j t).val.val (E x) - E x = E (a.representation t x - x)
      rw [map_sub,hE]
      rfl
    · rintro ⟨x,rfl⟩
      obtain ⟨y,rfl⟩ := E.surjective x
      refine ⟨a.representation t y-y,⟨y,rfl⟩,?_⟩
      change E (a.representation t y-y) = (j t).val.val (E y) - E y
      rw [map_sub,hE]
      rfl
  obtain ⟨v,hv,hline⟩ := ClassicalOrthogonal.FourPlusMatrix.Binary.rank_two_involution_moved_point
    (j t) hj2 hjrank
  have hZne : s.imageSpace c.Zα ≠ ⊥ := by
    intro hz0
    have hZP : c.Zα ≤ F.Vi 1 := by
      intro z hz
      let zU : F.U := ⟨z,(hCU (hplane (mem_sup_right hz))).1⟩
      have hh : (s.coordinates zU).toAdd ∈ s.imageSpace c.Zα :=
        (s.mem_imageSpace_iff _ _).mpr ⟨zU,hz,rfl⟩
      rw [hz0,Submodule.mem_bot] at hh
      exact (s.coordinates_eq_one_iff zU).mp (Multiplicative.toAdd.injective hh)
    have hbot : c.Zα = ⊥ := hdisj.symm.eq_bot_of_le hZP
    have hc : Nat.card c.Zα = 2 := by
      rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
      simpa using F.card 1 (by decide)
    rw [hbot,Nat.card_unique] at hc
    omega
  obtain ⟨z,hzZ,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
  have hzmove : E z ∈ LinearMap.range ((j t).val.val - LinearMap.id) := by
    rw [←hmap]
    exact ⟨z,s.imageSpace_mono (le_sup_right.trans hplane) hzZ,rfl⟩
  have hzn : (E z).det ≠ 0 := by
    intro hh
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv (j t).val
    have he2 : e ^ 2 = 1 := by
      apply LinearEquiv.ext
      intro w
      exact congrArg (fun x : linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action => x.val.val w) hj2
    exact ClassicalOrthogonal.FourPlusMatrix.Binary.low_rank_involution_singular_not_mem_displacement
      e (ClassicalOrthogonal.FourPlusMatrix.Binary.normalizer_linearEquiv_mem _) hjrank.le he2
      (E z) (fun hh => hz0 (E.injective (hh.trans E.map_zero.symm))) hh hzmove
  exact ⟨hU,a,s,c,hs,hR,hcard,hindex,hcomm,hrev,hplane,hCU,hfour,height,
    E,j,hj,hE,t,hz,ht2,ht1,hmap,v,hv,hmap.trans hline,z,hzZ,hz0,hzn⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
