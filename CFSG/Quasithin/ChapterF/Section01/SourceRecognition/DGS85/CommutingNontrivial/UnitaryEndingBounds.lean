module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorModule
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryActorElements
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommutatorGeometry

/-!
# Large unitary ending constituents in DGS 8.3

The full opposite neighborhood acts quadratically on the same irreducible
constituent used for the critical-center estimate. Its image has exactly the
original core index. If that image has order at least four, the unitary
individual-element estimate applies to a nonidentity element of the critical
center image. Thus its original centralizer index is at least q². This uses
neither descent of the whole residual module nor a reverse failure of 8.3.

Source: DGS85, Groups and Graphs, (5.10)(b) and (8.3)(2), pp.111–112,136.
UnitaryEndingCommutator applies this in both critical orientations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem constituent_quadratic {H D W : Type*} [Group H] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (q : H →* D)
    {A₀ : Subgroup D} {i j : ℕ} (d : ResidualConstituent ρ q A₀ i j)
    (A : Subgroup H) (hq : IsQuadratic ρ A) : IsQuadratic d.action (A.map q) := by
  rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩ z
  rw [d.descent,d.descent]
  apply Subtype.ext
  exact hq x hx y hy z

private theorem ending_large_actor_field_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* D)
    (q₀ : ℕ)
    (hlower : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W],
      ∀ (ρ : Representation (ZMod 2) D W), (∃ g, ρ g ≠ 1) →
      ∀ A : Subgroup D, IsElementaryAbelian 2 A → 4 ≤ Nat.card A →
      IsQuadratic ρ A → ∀ t : D, t ∈ A → t ≠ 1 →
        q₀^2 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers t)))
    (hlarge : 4 ≤ (Q (Reduction.reducedFamily L S₀) a').relIndex
      (V (Reduction.reducedFamily L S₀) beta 1)) :
    q₀^2 ≤ (centralizer (Z (Reduction.reducedFamily L S₀) a : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a'
  let U := (V Γ a' 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let A := ((V Γ beta 1).subgroupOf H).map q
  let A₀ := ((Z Γ a).subgroupOf H).map q
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ a' H (sylowGenerated_le _)
  obtain ⟨hb2,⟨d⟩⟩ := reduced_critical_ending_constituent h hc hab hd hb hcomm e
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite d.space.toSubmodule := d.finiteSpace
  let : d.action.IsIrreducible := d.irreducible
  let : Nontrivial d.space.toSubmodule := Subrepresentation.irreducible_module_nontrivial d.action
  let : IsElementaryAbelian 2 (V Γ beta 1) := CommutingThreeProfile.V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) hb2 beta
  have hVH : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta a' hb hd.le
  let : IsElementaryAbelian 2 ((V Γ beta 1).subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hk : q.ker = (Q Γ a').subgroupOf H := by
    have hcore : H.pCoreIn 2 = Q Γ a' := graphLocalGroup_core ht a'
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  have hcard : Nat.card A = (Q Γ a').relIndex (V Γ beta 1) :=
    BinaryConjugationSection.actor_image_card_eq_relIndex H (Q Γ a') (V Γ beta 1) q hk hVH
  have hA4 : 4 ≤ Nat.card A := hcard.symm ▸ hlarge
  obtain ⟨_,_,hquad⟩ := neighborhood_residual_section ht (Reduction.reduced_kernel_sylow h)
    a' hb2 H (core_le_graphLocalGroup ht a') (sylowGenerated_le _)
  have hqA : IsQuadratic d.action A :=
    constituent_quadratic (fixedQuotientAction U (pResidual 2 H)) q d
      ((V Γ beta 1).subgroupOf H) (hquad beta hd.le)
  have hx : fixedSpace d.action ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone d.action le_top).trans d.residualFixed.le)
  have hnt : ∃ g, d.action g ≠ 1 := by
    by_contra! hh
    obtain ⟨z,hz⟩ := exists_ne (0 : d.space.toSubmodule)
    have hfixed : z ∈ fixedSpace d.action ⊤ := by
      intro g
      change d.action g z = z
      rw [hh]
      rfl
    exact hz (hx.le hfixed)
  have hA₀ : A₀ ≠ ⊥ := by
    intro he
    have hcard₀ : Nat.card A₀ = (Q Γ a').relIndex (Z Γ a) := d.actorCard
    rw [he,card_bot] at hcard₀
    exact hc.2 ((relIndex_eq_one.mp hcard₀.symm).trans (source_Z_Q_U ht a').2)
  obtain ⟨t,htA₀,ht1⟩ := A₀.bot_or_exists_ne_one.resolve_left hA₀
  have hA₀A : A₀ ≤ A := map_mono (comap_mono (Z_neighbor_le_V Γ hab.symm))
  have hl := hlower d.space.toSubmodule d.action hnt A inferInstance hA4 hqA t (hA₀A htA₀) ht1
  have hi : Nat.card (d.space.toSubmodule ⧸ fixedSpace d.action (zpowers t)) ≤
      Nat.card (d.space.toSubmodule ⧸ fixedSpace d.action A₀) := by
    let : Finite (d.space.toSubmodule ⧸ fixedSpace d.action A₀) :=
      Finite.of_surjective _ (fixedSpace d.action A₀).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone d.action (zpowers_le.mpr htA₀)))
  exact hl.trans (hi.trans d.fixedIndex)

/-- A large full-neighborhood image at a unitary ending forces a field-square
index on the original critical center, for both SU₃ and PSU₃ quotients. -/
theorem reduced_ending_unitary_large_actor_field_square (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^n))
    (hlarge : 4 ≤ (Q (Reduction.reducedFamily L S₀) a').relIndex
      (V (Reduction.reducedFamily L S₀) beta 1)) :
    (2^n)^2 ≤ (centralizer (Z (Reduction.reducedFamily L S₀) a : Set (Reduction.G₀ L S₀))).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply ending_large_actor_field_square h hc hab hd hb hcomm e (2^n) ?_ hlarge
    intro W _ _ _ ρ hnt A hA hA4 hq t ht ht1
    let := hA
    exact psu3_elementary_element_field_square J hn hK hconj ρ hnt A hA4 hq t ht ht1
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    apply ending_large_actor_field_square h hc hab hd hb hcomm e (2^n) ?_ hlarge
    intro W _ _ _ ρ hnt A hA hA4 hq t ht ht1
    let := hA
    exact su3_elementary_element_field_square J hn hK hconj ρ hnt A hA4 hq t ht ht1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
