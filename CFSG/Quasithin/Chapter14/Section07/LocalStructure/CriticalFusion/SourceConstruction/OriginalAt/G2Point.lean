module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceContainedPoint
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Offender

/-!
# The original G₂ point marking with local structure

The critical rank bound supplies natural/Weyl recognition. Correct lifts
along the original core commutator to mark the actual point centralizer.
Its nonoffending actor is the natural four-group on that same marking.

Only Structural1222At at the original G,T is used. The source producers
qt-d-1222-source and qt-d-1434-source retain the earlier structural and
faithful inputs. Original residual alternatives, uniqueness, relative
component and alternating recognition retain qt-d-14763-source-data.
Final source 14.7.75 discharge remains with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.53–63, pp.1065–1069; F.9.18, pp.325–326.
The reused concrete model calculations retain LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
section PointMarking
open Atlas.G2 Atlas.G2.Natural.BinaryPointFlag
variable {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
private theorem point_marking_with_fixedness_at
    (ρ : Representation (ZMod 2) D E)
    (f : D →* Model F) (hf : Function.Injective f)
    (hrange : commutator (Model F) ≤ f.range)
    (p : E →ₗ[F] Natural.Space F) (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action F (f a) (p v))
    (C A : Subgroup D) (hAC : A ≤ C)
    (hn : C ≤ normalizer (A : Set D)) [IsElementaryAbelian 2 A]
    (v : E) (hv : p v ≠ 0)
    (hC : ∀ a, a ∈ C ↔ Natural.action F (f a) (p v) = p v)
    (hfix : ∀ a w, ρ a w = w ↔ Natural.action F (f a) (p w) = p w) :
    ∃ (f' : D →* Model F) (p' : E →ₗ[F] Natural.Space F),
      Function.Injective f' ∧ commutator (Model F) ≤ f'.range ∧ Function.Surjective p' ∧
      (∀ a w, p' (ρ a w) = Natural.action F (f' a) (p' w)) ∧
      (∀ a w, ρ a w = w ↔ Natural.action F (f' a) (p' w) = p' w) ∧
      C.map f' = BinaryCore.secondParabolic ⊓ f'.range ∧
      A.map f' ≤ unipotent ∧
      BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A.map f' : Set _) ∧
      Restricted.NaturalCoordinates.equiv F (p' v) = Pi.single 0 1 := by
  let E := Restricted.NaturalCoordinates.equiv F
  let z : Natural.Space F := E.symm (Pi.single 0 1)
  have hz : z ≠ 0 := by
    intro h
    have hh := congrArg E h
    have hh' : (Pi.single 0 1 : Fin 6 → F) = 0 := by
      simpa only [z,E.apply_symm_apply,map_zero] using hh
    have heq := congrFun hh' 0
    simp at heq
  obtain ⟨g,hg⟩ := Natural.derivedAction_transitive F (p v) z hv hz
  let f' := (MulAut.conj (g : Model F)).toMonoidHom.comp f
  let p' := (Natural.action F (g : Model F)).comp p
  have hp' : Function.Surjective p' := by
    intro w
    obtain ⟨u,hu⟩ := hp (Natural.action F (g : Model F)⁻¹ w)
    refine ⟨u, ?_⟩
    change Natural.action F (g : Model F) (p u) = w
    rw [hu,← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl
  have he' (a) (w) : p' (ρ a w) = Natural.action F (f' a) (p' w) := by
    change Natural.action F (g : Model F) (p (ρ a w)) =
      Natural.action F ((g : Model F)*f a*(g : Model F)⁻¹)
        (Natural.action F (g : Model F) (p w))
    rw [he]
    simp only [← Module.End.mul_apply,← map_mul]
    congr 2
    group
  have hfix' (a) (w) : ρ a w = w ↔ Natural.action F (f' a) (p' w) = p' w := by
    rw [←he', hfix, ←he]
    have hg : Function.Injective (Natural.action F (g : Model F)) := by
      apply Function.HasLeftInverse.injective
      refine ⟨Natural.action F (g : Model F)⁻¹,?_⟩
      intro w
      simp only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    exact hg.eq_iff.symm
  have hrange' : commutator (Model F) ≤ f'.range := by
    intro b hb
    let b' : Model F := (g : Model F)⁻¹*b*(g : Model F)
    have hb' : b' ∈ commutator (Model F) := by
      have hh := (inferInstance : (commutator (Model F)).Normal).conj_mem b hb (g : Model F)⁻¹
      simpa only [inv_inv] using hh
    obtain ⟨a,ha⟩ := hrange hb'
    refine ⟨a,?_⟩
    change (g : Model F)*f a*(g : Model F)⁻¹=b
    rw [ha]
    dsimp only [b']
    group
  have hpv : E (p' v) = Pi.single 0 1 := by
    change E (Natural.derivedAction F g (p v)) = _
    rw [hg]
    exact E.apply_symm_apply _
  have hC' (a) : a ∈ C ↔
      Restricted.NaturalCoordinates.action F (f' a) (Pi.single 0 1) = Pi.single 0 1 := by
    rw [hC,← hpv]
    have hcoord := LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (f' a)) (p' v)
    change E (Natural.action F (f' a) (p' v)) =
      Restricted.NaturalCoordinates.action F (f' a) (E (p' v)) at hcoord
    rw [← hcoord, E.injective.eq_iff,← he']
    change Natural.action F (f a) (p v) = p v ↔
      Natural.action F (g : Model F) (p (ρ a v)) = Natural.action F (g : Model F) (p v)
    rw [he]
    have hi : Function.Injective (Natural.action F (g : Model F)) := by
      apply Function.HasLeftInverse.injective
      refine ⟨Natural.action F (g : Model F)⁻¹,?_⟩
      intro w
      simp only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    exact hi.eq_iff.symm
  obtain ⟨hu,hn'⟩ := marked_point_actor_bounds f' hrange' C A hAC hn hC'
  exact ⟨f',p',(MulAut.conj (g : Model F)).injective.comp hf,hrange',hp',he',hfix',marked_point_image f' C hC',hu,hn',hpv⟩

private theorem fixedCodim_eq_of_fixed_reflecting_projection_at
    {D J E M : Type*} [Group D] [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) D E) (τ : Representation (ZMod 2) J M)
    (f : D →* J) (p : E →ₗ[ZMod 2] M) (hp : Function.Surjective p)
    (hfix : ∀ a w, ρ a w = w ↔ τ (f a) (p w) = p w) (A : Subgroup D) :
    fixedCodim ρ A = fixedCodim τ (A.map f) := by
  have hc : fixedSpace ρ A = (fixedSpace τ (A.map f)).comap p := by
    ext v
    constructor
    · intro hv
      rintro ⟨b,hb⟩
      obtain ⟨a,ha,rfl⟩ := hb
      exact (hfix a v).mp (hv ⟨a,ha⟩)
    · intro hv a
      exact (hfix a v).mpr (hv ⟨f a,mem_map_of_mem f a.property⟩)
  let q := (fixedSpace ρ A).mapQ (fixedSpace τ (A.map f)) p hc.le
  have hi : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ,←hc,Submodule.mkQ_map_self]
  have hs : Function.Surjective q := by
    intro v
    obtain ⟨w,rfl⟩ := (fixedSpace τ (A.map f)).mkQ_surjective v
    obtain ⟨w,rfl⟩ := hp w
    exact ⟨(fixedSpace ρ A).mkQ w,rfl⟩
  exact (LinearEquiv.ofBijective q ⟨hi,hs⟩).finrank_eq

private theorem nonoffender_point_actor_eq_natural_at
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) D E)
    (f : D →* Model F) (hf : Function.Injective f)
    (p : E →ₗ[F] Natural.Space F) (hp : Function.Surjective p)
    (hfix : ∀ a w, ρ a w = w ↔ Natural.action F (f a) (p w) = p w)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hn : ¬ IsOffender ρ A)
    (hu : A.map f ≤ unipotent)
    (hN : BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A.map f : Set _)) :
    A.map f = BinaryCore.natural ∧ rank A = 2 := by
  let := hA.2
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hne : A.map f ≠ ⊥ := by
    intro hb
    apply hA.1
    exact (Subgroup.map_injective hf) (hb.trans (Subgroup.map_bot f).symm)
  have hAE := elementary_normalized_point_le (A.map f) hu hN
  have hc := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAE)
  rw [BinaryCore.card_elementary] at hc
  have hr := Nat.log_mono_right (b := 2) hc
  change rank (A.map f) ≤ 3 at hr
  have he := fixedCodim_eq_of_fixed_reflecting_projection_at ρ (Natural.action F) f p hp hfix A
  have hsmall : rank (A.map f) < 3 := by
    by_contra! hh
    have hr3 : rank (A.map f) = 3 := by omega
    have hEq : A.map f = BinaryCore.elementary := Subgroup.eq_of_le_of_card_ge hAE (by
      rw [BinaryCore.card_elementary,
        (show IsElementaryTwo (A.map f) from ⟨hne,inferInstance⟩).card_eq_two_pow_rank,hr3]
      decide)
    apply hn
    refine ⟨hA,?_⟩
    have hel : BinaryCore.elementary = EvenTwoRank.elementary F := by
      ext g
      constructor
      · rintro ⟨x,⟨hd,he⟩,rfl⟩
        refine ⟨Multiplicative.ofAdd ![x.a,x.b,x.c],?_⟩
        change unipotentProduct (EvenTwoRank.elementaryParameters F _) =
          unipotentProduct (BinaryCore.parameters x)
        congr 1
        simp [EvenTwoRank.elementaryParameters,BinaryCore.parameters,hd,he]
      · rintro ⟨x,rfl⟩
        exact ⟨⟨x.toAdd 0,x.toAdd 1,x.toAdd 2,0,0⟩,⟨rfl,rfl⟩,rfl⟩
    rw [he,hEq,hel]
    have hd := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim
      (F := F) (n := 1) (by norm_num) (by decide) _
      (Atlas.G2.NaturalOffenders.natural_elementary_offender (n := 1) (by norm_num) (by decide))
    change fixedCodim (Natural.action F) (EvenTwoRank.elementary F) = 3 at hd
    rw [hd,←rank_map_injective f hf A,hr3]
  obtain ⟨ha,hr2⟩ := Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.point_actor_eq_natural
    (A.map f) hu hN hne hsmall
  exact ⟨ha,by rwa [rank_map_injective f hf A] at hr2⟩
end PointMarking
open Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

include c in
theorem source_selected_critical_bound_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ)
    (path : CriticalPath (L := L) F) (selection : path.RankSelection) :
    IsQuadratic σ (star F path.Uα) ∧
      fixedCodim σ (star F path.Uα) ≤ 2 * rank (star F path.Uα) := by
  have hker : (σ.comp (starMap F)).ker = pCore 2 F.H := by
    rw [MonoidHom.ker_comp_of_injective (starMap F) σ hf]
    exact QuotientGroup.ker_mk' _
  have hb := (LocalReduction.critical_fixedCodim_bounds_of_kernel_at h hab structural hker c path).1
  have hs := selection.comparison
  have he : fixedCodim (σ.comp (starMap F)) (path.Uα.subgroupOf F.H) =
      fixedCodim σ (star F path.Uα) := by
    rw [fixedCodim, fixedSpace_comp_map]
    rfl
  rw [he] at hb
  refine ⟨?_, by change _ ≤ 2 * Nat.log 2 (Nat.card (star F path.Uα)); omega⟩
  rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ v
  exact LocalReduction.critical_quadratic h hab c path a ha b hb v

include c in
private theorem source_nonoffender_parabolic_of_projection_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (hirr : IsIrrPlus σ (star F (K F)) ⊤)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hn : ¬ IsOffender σ (star F path.Uα))
    (e : star F (K F) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (hmark : ∀ a : star F (K F), i a = (e a : Atlas.G2.Model (ZMod 2)))
    (p : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)) (hp : Function.Surjective p)
    (he : ∀ a v, p (σ a v) = Atlas.G2.Natural.action (ZMod 2) (i a) (p v))
    (hk : p.ker ≤ fixedSpace σ (star F (K F))) :
    ∃ (f : HStar F.H →* Atlas.G2.Model (ZMod 2))
      (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)),
      Function.Injective f ∧ commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range ∧
      Function.Surjective q ∧
      (∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v)) ∧
      (∀ a v, σ a v = v ↔ Atlas.G2.Natural.action (ZMod 2) (f a) (q v) = q v) ∧
      (star F (F.H ⊓ centralizer (path.Zα : Set G))).map f =
        Atlas.G2.BinaryCore.secondParabolic ⊓ f.range ∧
      (star F path.Uα).map f ≤ Atlas.G2.unipotent ∧
      Atlas.G2.BinaryParabolicPair.derivedSecondAmbient ≤
        normalizer ((star F path.Uα).map f : Set _) ∧
      ∃ t : F.U, (t : G) ∈ path.Zα ∧
        Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2) (q (c.coordinates t).toAdd) =
          Pi.single 0 1 := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : (star F (K F)).Normal := hfit ▸ inferInstance
  have hfull : Coinvariants.ker (σ.comp (star F (K F)).subtype) = ⊤ := by
    rw [←subspaceCommutator_top_eq_coinvariants]
    exact full_star_commutator c h
  have hfix := Atlas.G2.Natural.OrthogonalCover.binary_cover_point_fixed_iff
    (star F (K F)) e i hmark σ p hp (fun _ hv a => hk hv a) hfull he
  obtain ⟨t,ht,hpt⟩ := source_nonoffender_point_survives c h hab path hplace selection hn i p he hfix
  have ht1 : (t : G) ≠ 1 := by
    intro hh
    have ht' : t = 1 := Subtype.ext hh
    apply hpt
    rw [ht',map_one]
    exact p.map_zero
  have htn : ¬ (t : G) ∈ centralizer (F.H.pCoreIn 2 : Set G) := by
    intro hh
    have hv := source_core_centralizer_fixed c hirr hcomm
      ((c.mem_imageSpace_iff _ _).mpr ⟨t,⟨t.property,hh⟩,rfl⟩)
    apply hpt
    apply Atlas.G2.Natural.Transport.fixed_eq_zero
    intro g
    have hg : i (e.symm g) = g := (hmark _).trans (congrArg Subtype.val (e.apply_symm_apply g))
    change Atlas.G2.Natural.action (ZMod 2) g (p (c.coordinates t).toAdd) = _
    rw [←hg,←he]
    exact congrArg p (hv (e.symm g))
  let A := star F path.Uα
  let C := star F (F.H ⊓ centralizer (path.Zα : Set G))
  have hA := critical_elementary h hab path hplace selection
  let : IsElementaryAbelian 2 A := hA.2
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : IsElementaryAbelian 2 path.Uα :=
    IsElementaryAbelian.map (MulAut.conj path.conjugator⁻¹).toMonoidHom
  have hZA : path.Zα ≤ path.Uα := map_mono c.kernel_le
  have hAC : A ≤ C := map_mono (subgroupOf_mono F.H (le_inf hAH
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hZA))))
  have hnA : C ≤ normalizer (A : Set _) := by
    rintro _ ⟨a,ha,rfl⟩
    apply le_normalizer_map (starMap F)
    refine ⟨a,?_,rfl⟩
    change a ∈ normalizer (path.Uα.subgroupOf F.H : Set F.H)
    rw [mem_normalizer_iff]
    intro b
    exact mem_normalizer_iff.mp (partner_centralizer_normalizes path ha.2) b
  have hC (a) : a ∈ C ↔
      Atlas.G2.Natural.action (ZMod 2) (i a) (p (c.coordinates t).toAdd) = p (c.coordinates t).toAdd :=
    (source_point_centralizer_star_iff c path t ht ht1 htn a).trans (hfix a _)
  have hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range := by
    intro a ha
    exact ⟨e.symm ⟨a,ha⟩,(hmark _).trans (congrArg Subtype.val (e.apply_symm_apply ⟨a,ha⟩))⟩
  obtain ⟨f,q,hf,hJ',hq,heq,hfixq,hCq,hAq,hNq,htq⟩ := point_marking_with_fixedness_at
    σ i hi hJ p hp he C A hAC hnA (c.coordinates t).toAdd hpt hC hfix
  exact ⟨f,q,hf,hJ',hq,heq,hfixq,hCq,hAq,hNq,t,ht,htq⟩

theorem source_nonoffender_point_parabolic_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hn : ¬ IsOffender σ (star F path.Uα)) :
    ∃ (f : HStar F.H →* Atlas.G2.Model (ZMod 2))
      (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)),
      Function.Injective f ∧ commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range ∧
      Function.Surjective q ∧
      (∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v)) ∧
      (∀ a v, σ a v = v ↔ Atlas.G2.Natural.action (ZMod 2) (f a) (q v) = q v) ∧
      (star F (F.H ⊓ centralizer (path.Zα : Set G))).map f =
        Atlas.G2.BinaryCore.secondParabolic ⊓ f.range ∧
      (star F path.Uα).map f ≤ Atlas.G2.unipotent ∧
      Atlas.G2.BinaryParabolicPair.derivedSecondAmbient ≤
        normalizer ((star F path.Uα).map f : Set _) ∧
      ∃ t : F.U, (t : G) ∈ path.Zα ∧
        Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2) (q (c.coordinates t).toAdd) =
          Pi.single 0 1 := by
  have hA := critical_elementary h hab path hplace selection
  have hirr := source_isIrrPlus c h hcomponent hfit eK hf P hP orbit path hplace selection hA
  obtain ⟨hq,hb⟩ := source_selected_critical_bound_at c h hab structural hf path selection
  obtain ⟨eK',i,hi,hmark,p,hp,hk,he⟩ := source_projection c hcomponent hfit eK hirr
    _ hA hq hb
  let j : ((K F) ⧸ pCore 2 (K F)) ≃* star F (K F) :=
    Chapter13.Section08.Components.componentStarEquiv F.H (K F) (map_subtype_le _) hcomponent
  let e : star F (K F) ≃* commutator (Atlas.G2.Model (ZMod 2)) := j.symm.trans eK'
  have hmark' (a : star F (K F)) : i a = (e a : Atlas.G2.Model (ZMod 2)) := by
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 (K F)) (j.symm a)
    have ha : j (QuotientGroup.mk' (pCore 2 (K F)) k) = a := by rw [hk,j.apply_symm_apply]
    have hj := Chapter13.Section08.Components.componentStarEquiv_mk F.H (K F)
      (map_subtype_le _) hcomponent k
    change (j (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H) =
      starMap F ⟨k,map_subtype_le _ k.property⟩ at hj
    rw [←ha,hj,hmark]
    exact congrArg Subtype.val (congrArg eK' (j.symm_apply_apply _)).symm
  have hk' : p.toLinearMap.ker ≤ fixedSpace σ (star F (K F)) := by
    intro v hv a
    have hh := hk hv (e a)
    have ha : modelActor (map_subtype_le _) hcomponent eK' (e a) = a := by
      change (j (eK'.symm (eK' (j.symm a))) : HStar F.H) = a
      rw [eK'.symm_apply_apply,j.apply_symm_apply]
    change σ (modelActor (map_subtype_le _) hcomponent eK' (e a)) v = v at hh
    rwa [ha] at hh
  exact source_nonoffender_parabolic_of_projection_at c h hab hfit hirr hcomm
    path hplace selection hn e i hi hmark' p.toLinearMap hp he hk'

theorem source_nonoffender_point_actor_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection) (hn : ¬ IsOffender σ (star F path.Uα)) :
    ∃ (f : HStar F.H →* Atlas.G2.Model (ZMod 2))
      (q : W →ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)),
      Function.Injective f ∧ commutator (Atlas.G2.Model (ZMod 2)) ≤ f.range ∧
      Function.Surjective q ∧
      (∀ a v, q (σ a v) = Atlas.G2.Natural.action (ZMod 2) (f a) (q v)) ∧
      (∀ a v, σ a v = v ↔ Atlas.G2.Natural.action (ZMod 2) (f a) (q v) = q v) ∧
      (star F (F.H ⊓ centralizer (path.Zα : Set G))).map f =
        Atlas.G2.BinaryCore.secondParabolic ⊓ f.range ∧
      (star F path.Uα).map f = Atlas.G2.BinaryCore.natural ∧
      rank (star F path.Uα) = 2 ∧
      ∃ t : F.U, (t : G) ∈ path.Zα ∧
        Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2) (q (c.coordinates t).toAdd) =
          Pi.single 0 1 := by
  obtain ⟨f,q,hf,hJ,hq,he,hfix,hC,hA,hN,hpoint⟩ := source_nonoffender_point_parabolic_at
    c h hab hcomponent hfit eK structural hf hcomm P hP orbit path hplace selection hn
  obtain ⟨hEq,hr⟩ := nonoffender_point_actor_eq_natural_at σ f hf q hq hfix
    (star F path.Uα) (critical_elementary h hab path hplace selection) hn hA hN
  exact ⟨f,q,hf,hJ,hq,he,hfix,hC,hEq,hr,hpoint⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
