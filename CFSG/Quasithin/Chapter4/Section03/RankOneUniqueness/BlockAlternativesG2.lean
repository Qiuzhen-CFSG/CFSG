module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesSymplectic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.Representation.G2OrthogonalCover.ShortParabolicMovement
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalElementary
public import Theory.Representation.BinaryConjugationSection.CommutatorImage

/-!
# The crossed natural G₂ block row

The original star action is transported to the literal block quotient and to
the full module coming from the source configuration. The short local row
moves the whole natural cover; the long local row fixes it through the
parabolic fixed space. The crossed copy then forces an elementary quotient
normalized by the short local group into its highest-root center, where the
short local group centralizes it. This contradicts the source crossing clause.
The proof keeps the original K, L and full W distinct from the chosen module.
Source: Aschbacher--Smith C.4.1 and 4.3.7, printed pp.151,615--616.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter12.Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

namespace G2BlockModule
open ExceptionalRestrictions Atlas.G2 Atlas.G2.Natural Atlas.G2.LieParabolicSetup
open Atlas.G2.Natural.OrthogonalCover.ParabolicFixed
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The short residual moves the whole block layer; the long residual is
incompatible with a nonzero fully moved module centralized by its two-core. -/
theorem local_module
    (h : IsShort X) (hq : 2 < Nat.card F)
    {rho : Model F →* MulAut (Multiplicative (Space F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = Natural.action F g v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W) (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X)) :
    (A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) = local₁ →
      ⁅blockU X,A⁆ = blockU X) ∧
    (A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) = local₂ → False) := by
  let := h.elementary
  let σ : Representation (ZMod 2) (Model F) (Additive (blockU X)) :=
    (uRepresentation h).comp m.quotientIso.symm.toMonoidHom
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let p : σ.IntertwiningMap (fullBinaryNatural F) :=
    q.toAdditiveLeft.toZModLinearMap 2 |>.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g u
      obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 X) (m.quotientIso.symm g)
      change (q (uAut h (m.quotientIso.symm g) u.toMul)).toAdd = _
      rw [←hx]
      change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X x u.toMul))).toAdd = _
      rw [m.intertwining,hrho,hx,m.quotientIso.apply_symm_apply]
      rfl)
  have hp : IsCover p := by
    refine ⟨?_,?_,?_⟩
    · intro v
      obtain ⟨u,hu⟩ := (m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective _))
        (Multiplicative.ofAdd v)
      exact ⟨Additive.ofMul u,hu⟩
    · intro u hu g
      have hz : u.toMul ∈ blockFixed X := by
        apply (QuotientGroup.eq_one_iff _).mp
        apply m.moduleIso.injective
        exact hu.trans (map_one m.moduleIso).symm
      exact (uRepresentation_fixed h u).mpr hz (m.quotientIso.symm g)
    · apply top_unique
      rw [←uRepresentation_moved h]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,u⟩,rfl⟩
      have he : σ (m.quotientIso g) u = uRepresentation h g u := by
        change uRepresentation h (m.quotientIso.symm (m.quotientIso g)) u = _
        rw [m.quotientIso.symm_apply_apply]
      change uRepresentation h g u - u ∈ Coinvariants.ker σ
      rw [←he]
      exact Coinvariants.sub_mem_ker (m.quotientIso g) u
  let π := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hπ : π.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hσ (x : X) (u : Additive (blockU X)) :
      ((σ (π x) u).toMul : X) = x * (u.toMul : X) * x⁻¹ := by
    change ((uRepresentation h (m.quotientIso.symm (m.quotientIso _)) u).toMul : X) = _
    rw [m.quotientIso.symm_apply_apply,uRepresentation_apply]
  constructor
  · intro hA
    let B := ⁅blockU X,A⁆
    let S : Submodule (ZMod 2) (Additive (blockU X)) :=
      AddSubgroup.toZModSubmodule 2 (B.subgroupOf (blockU X)).toAddSubgroup
    have hm : subspaceCommutator σ ⊤ (local₁ (F := F)) ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,u,_,rfl⟩
      rw [←hA] at hg
      obtain ⟨a,ha,rfl⟩ := hg
      change ((σ (π a) u - u).toMul : X) ∈ B
      change ((σ (π a) u).toMul : X) / (u.toMul : X) ∈ B
      rw [div_eq_mul_inv,hσ]
      exact (commutator_comm A (blockU X)).le (commutator_mem_commutator ha u.toMul.property)
    rw [short_cover_moved F p hq hp] at hm
    apply le_antisymm (commutator_le_left _ _)
    intro u hu
    exact hm (show Additive.ofMul (⟨u,hu⟩ : blockU X) ∈ ⊤ from trivial)
  · intro hA
    have hcore : (A.pCoreIn 2).map π = (local₂ (F := F)).pCoreIn 2 := by
      rw [map_pCoreIn_of_ker_isPGroup π (hπ ▸ pCore_isPGroup),hA]
    have hWfixed (u : Additive (blockU X)) (hu : (u.toMul : X) ∈ W) :
        u ∈ fixedSpace σ ((local₂ (F := F)).pCoreIn 2) := by
      intro g
      have hg := g.property
      have hg' : (g : Model F) ∈ (A.pCoreIn 2).map π := hcore.symm ▸ hg
      obtain ⟨a,ha,he⟩ := hg'
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((σ g.val u).toMul : X) = _
      rw [←he,hσ]
      exact mul_inv_eq_iff_eq_mul.mpr (hfix hu a ha)
    have hc : W ≤ centralizer (A : Set X) := by
      intro w hw a ha
      let u : Additive (blockU X) := Additive.ofMul ⟨w,hWU hw⟩
      have he := long_fixed F p hq hp (hWfixed u hw)
        ⟨π a,hA ▸ mem_map_of_mem π ha⟩
      have he' := congrArg (fun v : Additive (blockU X) => (v.toMul : X)) he
      change ((σ (π a) u).toMul : X) = w at he'
      rw [hσ] at he'
      exact mul_inv_eq_iff_eq_mul.mp he'
    exact hne (hcomm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
end G2BlockModule

/-- The original L-image is proper in K/O₂(K), by the source star-intersection
condition. This supplies the properness premise of parabolic placement. -/
theorem SourceConfiguration.block_quotient_local_proper
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K) :
    c.componentQuotientL ≠ ⊤ := by
  intro he
  have hle : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L ≤
      starM (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.H ⊓ normalizer (L : Set G)) := by
    apply map_mono
    apply comap_mono
    exact le_inf (le_inf (c.le_I.trans c.I_le_H) L.le_normalizer) c.le_component
  have hm := c.componentQuotientL_star hb
  rw [he,map_top_of_surjective _ (c.block_star_quotientEquiv hb).surjective] at hm
  exact (ChapterC.C27Source.star_thompson_intersection_from_source
    (c.block_source_input hf)).2.not_ge ((subgroupOf_eq_top.mp hm.symm).trans hle)

/-- Place the original L-image in a literal G₂ parabolic residual using the
full Sylow subgroup of K and the original local C-component embedding. -/
theorem SourceConfiguration.block_g2_local_frame
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hq : 2 < Nat.card F)
    (e : (c.K ⧸ pCore 2 c.K) ≃* Atlas.G2.Model F) :
    ∃ a : Atlas.G2.Model F,
      c.componentQuotientL.map (e.trans (MulAut.conj a)).toMonoidHom = Atlas.G2.LieParabolicSetup.local₁ ∨
      c.componentQuotientL.map (e.trans (MulAut.conj a)).toMonoidHom = Atlas.G2.LieParabolicSetup.local₂ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))
  have hk : f.ker = pCore 2 c.K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent f.ker := (hk ▸ pCore_isPGroup).isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  obtain ⟨P,hP⟩ := c.ordinary_component_sylow
  have hlocal := c.ordinaryLocal_mem_localCComponents D
  rw [←hP] at hlocal
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  have hproper : c.ordinaryLocal.map f ≠ ⊤ := by
    intro ht
    apply c.block_quotient_local_proper hf hb
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact (map_map _ _ _).trans ht
  obtain ⟨a,ha⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement hq
    (P.mapSurjective (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    (c.ordinaryLocal.map f) hm hproper
  refine ⟨a,?_⟩
  have he : (e.trans (MulAut.conj a)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp e.toMonoidHom := rfl
  simpa only [SourceConfiguration.componentQuotientL,SourceConfiguration.ordinaryLocal,
    map_map,f,he,MonoidHom.comp_assoc] using ha

set_option linter.style.haveILetI false in
omit [Finite G] in
/-- Exclude the actual nonbinary G₂ natural block row. The B.5 degree
restriction gives |F| > 2; the action marking and both parabolic cases retain
the original K, L, U(K), crossed U(K) and full W. -/
theorem SourceConfiguration.false_of_g2_model
    (hG : Finite G) (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    {F : BinaryField} (hF : 1 < F.degree)
    (hm : IsLinearBlockModel c.K (binaryG2 F)) : False := by
  letI := hG
  obtain ⟨rho,⟨m⟩,hrho⟩ := hm
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hd : 2 ≤ F.degree := by omega
    have hp : 2 ^ 2 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide) hd
    exact lt_of_lt_of_le (by decide) hp
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hfr : f.range = c.K.map c.H.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have hU : (blockU c.K).map f = c.blockLayer := by rw [← map_map]
  let A := L.comap f
  let B := c.blockFullModule.comap f
  have hLA : A.map f = L := map_comap_eq_self (by rw [hfr]; exact c.le_component)
  have hWL : c.blockFullModule ≤ L := by
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    simpa only [hs] using c.c28.module_le
  have hWB : B.map f = c.blockFullModule :=
    map_comap_eq_self (hWL.trans (by rw [hfr]; exact c.le_component))
  have hBU : B ≤ blockU c.K := by
    intro b hb'
    apply (mem_map_iff_mem hfi).mp
    rw [hU]
    exact c.fullModule_le_blockLayer hf hb'
  have hBne : B ≠ ⊥ := by
    intro he
    have hWne := c.c28.module_nontrivial
    apply hWne
    change c.blockFullModule = ⊥
    rw [← hWB, he, Subgroup.map_bot]
  have hBA : ⁅B,A⁆ = B := by
    apply map_injective hfi
    rw [map_commutator, hWB, hLA]
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    exact (show c.blockFullModule = ⁅c.blockFullModule,L⁆ from by
      simpa only [hs] using c.c28.module_commutator).symm
  have hIN : c.I ≤ normalizer (L : Set G) := by
    rw [c.I_eq]
    exact sup_le L.le_normalizer (c.c28.radical_le.trans inf_le_right)
  have hcore : L.pCoreIn 2 ≤ c.I.pCoreIn 2 := pCoreIn_mono_of_normalizes c.le_I hIN
  have hfix : B ≤ centralizer (A.pCoreIn 2 : Set c.K) := by
    intro w hw a ha
    apply hfi
    change f a * f w = f w * f a
    have haL : f a ∈ L.pCoreIn 2 := by
      have hm' := mem_map_of_mem f ha
      rwa [map_pCoreIn_of_injective 2 A f hfi,hLA] at hm'
    obtain ⟨v,hv,hvw⟩ := c.c28.module_le_center_radical hw
    have hc := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
      (mem_center_iff.mp hv ⟨f a,hcore haL⟩)
    change f a * (v : G) = (v : G) * f a at hc
    change (v : G) = f w at hvw
    rwa [hvw] at hc
  obtain ⟨a,ha⟩ := c.block_g2_local_frame D hf hb hq m.quotientIso
  let m' := m.innerMarking a
  rcases ha with ha | ha
  · have hplace : A.map (m'.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))) =
        Atlas.G2.LieParabolicSetup.local₁ := by
      change A.map ((m.quotientIso.trans (MulAut.conj a)).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 c.K))) = _
      simpa only [SourceConfiguration.componentQuotientL,A,f,subgroupOf,comap_comap,←map_map] using ha
    have hcomm0 := (G2BlockModule.local_module hb.short hq m' hrho A B hBU hBne hBA hfix).1 hplace
    have hcomm : ⁅c.blockLayer,L⁆ = c.blockLayer := by
      have hmapeq := congrArg (Subgroup.map f) hcomm0
      rw [map_commutator,hU,hLA] at hmapeq
      exact hmapeq
    have hUR : c.blockLayer ≤ c.I.pCoreIn 2 :=
      c.blockLayer_le_blockCore.trans
        ((map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
          c.c28.ambient_core_le_radical)
    have hUL : c.blockLayer ≤ normalizer (L : Set G) :=
      hUR.trans (c.c28.radical_le.trans inf_le_right)
    have hLL : c.blockLayer ≤ L := by
      rw [←hcomm,commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp hUL
    have hL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp
        (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
    have hcrossL : c.crossedBlockLayer ≤ L := by
      exact (map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom) hLL).trans_eq hL
    have hcrossComm : ⁅c.crossedBlockLayer,L⁆ = c.crossedBlockLayer := by
      have hh := congrArg (Subgroup.map (MulAut.conj c.t⁻¹).toMonoidHom) hcomm
      rw [map_commutator,hL] at hh
      simpa only [SourceConfiguration.crossedBlockLayer] using hh
    let E0 := c.crossedBlockLayer.comap f
    have hE0map : E0.map f = c.crossedBlockLayer :=
      map_comap_eq_self (hcrossL.trans (by rw [hfr]; exact c.le_component))
    let : IsElementaryAbelian 2 (blockU c.K) := hb.short.elementary
    let : IsElementaryAbelian 2 c.blockLayer := hU ▸ IsElementaryAbelian.map f
    let : IsElementaryAbelian 2 c.crossedBlockLayer :=
      IsElementaryAbelian.map (MulAut.conj c.t⁻¹).toMonoidHom
    let : IsElementaryAbelian 2 E0 := IsElementaryAbelian.comap_of_injective f hfi _
    have hE0A : E0 ≤ A := by
      intro x hx
      exact hcrossL hx
    have hE0comm : ⁅E0,A⁆ = E0 := by
      apply map_injective hfi
      rw [map_commutator,hE0map,hLA]
      exact hcrossComm
    let π := m'.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))
    have hπ : π.ker = pCore 2 c.K := by
      rw [MonoidHom.ker_comp_of_injective _ _ m'.quotientIso.injective,QuotientGroup.ker_mk']
    let E := E0.map π
    letI : IsElementaryAbelian 2 E := IsElementaryAbelian.map π
    have hAplace : A.map π = Atlas.G2.LieParabolicSetup.local₁ := hplace
    have hEsub : E ≤ Atlas.G2.LieParabolicSetup.local₁ := by
      change E0.map π ≤ _
      rw [←hAplace]
      exact map_mono hE0A
    have hEcomm : ⁅E,Atlas.G2.LieParabolicSetup.local₁⁆ = E := by
      have hh := congrArg (Subgroup.map π) hE0comm
      rw [map_commutator,hAplace] at hh
      simpa only [E] using hh
    have hEnorm : Atlas.G2.LieParabolicSetup.local₁ ≤
        normalizer (E : Set (Atlas.G2.Model F.Carrier)) :=
      le_normalizer_iff_commutator_le_right.mpr (by
        rw [commutator_comm]
        exact hEcomm.le)
    have hroot := Atlas.G2.LieParabolicSetup.elementary_normal_short_local_le_highestRoot
      (F := F.Carrier) E hEsub hEnorm
    have hEcentral : E ≤ centralizer
        (Atlas.G2.LieParabolicSetup.local₁ (F := F.Carrier) : Set _) := by
      intro x hx y hy
      obtain ⟨b,rfl⟩ := hroot hx
      have hc := Subgroup.mem_centralizer_singleton_iff.mp
        (Atlas.G2.LieParabolicSetup.local₁_le_centralizer_rootA b.toAdd hy)
      exact hc
    have hEbot : E = ⊥ := by
      exact hEcomm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hEcentral)
    have hE0core : E0 ≤ pCore 2 c.K := by
      rw [←hπ]
      intro x hx
      have hx' : π x ∈ E := mem_map_of_mem π hx
      rw [hEbot] at hx'
      exact Subgroup.mem_bot.mp hx'
    have hcrossCore : c.crossedBlockLayer ≤ c.blockCore := by
      rw [←hE0map]
      rintro _ ⟨x,hx,rfl⟩
      exact mem_map_of_mem c.H.subtype (mem_map_of_mem c.K.subtype (hE0core hx))
    exact c.crossedBlockLayer_not_le_blockCore hb hcrossCore
  · have hplace : A.map (m'.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))) =
        Atlas.G2.LieParabolicSetup.local₂ := by
      change A.map ((m.quotientIso.trans (MulAut.conj a)).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 c.K))) = _
      simpa only [SourceConfiguration.componentQuotientL,A,f,subgroupOf,comap_comap,←map_map] using ha
    exact (G2BlockModule.local_module hb.short hq m' hrho A B hBU hBne hBA hfix).2 hplace

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
