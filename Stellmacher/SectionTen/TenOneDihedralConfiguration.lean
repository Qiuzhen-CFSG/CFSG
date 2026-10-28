module
public import Stellmacher.SectionTen.TenOneSmallCommutatorActor
public import Stellmacher.SectionFiveToSeven.Result7_8.LocalInputs
public import Stellmacher.SectionThree.GeneratedDihedralAction.SylowGeneration
public import Stellmacher.SectionThree.GeneratedDihedralImage
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.TwoResidualConjugateSupplement

/-!
# Prescribed-actor dihedral data in Stellmacher (10.1)

For an actual first-module actor outside the terminal core, extract a perfect
two-residual subgroup inside the terminal residual. Its join with the actual
middle-terminal edge stabilizer is the entire terminal stabilizer. Its image
modulo the terminal core, together with the same actor image, is dihedral.
The record retains the primitive extraction's actual coatom, factorization,
cyclic odd rotation, and reflection data; that coatom commutes with the
extracted residual modulo the terminal core.

The actual neighborhood-core containment and elementary first module supply
the edge extraction hypotheses. The proved primitive prescribed-actor
construction supplies the raw witnesses. Residual functoriality gives their
containment and perfection. A subgroup generating with its own conjugate
supplements the two-residual, so the extracted residual supplies the same
edge generation as the extracted group. The coatom's rotation centralizer
lifts to the claimed commutator bound, and odd cyclic inversion gives the
literal dihedral quotient. No involution-lifting assertion from the legacy
numbered (3.6) or (7.8) interfaces is used.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.63,
the prescribed-actor application of (3.6), assertions (i)–(iii), in
`refs/files/stellmacher-n-group.pdf`. The quotient convention is defined on
p.59. The actor remains prescribed, so the selected order-four displacement
witness can be reused without changing any subsequent data.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionThree
open scoped Pointwise commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public structure TenOneDihedralConfigurationData
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex) (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep) where
  module_le : VAt ctx.Γ ctx.criticalPath.firstStep ≤ GAt ctx.Γ ctx.criticalPath.a'
  raw : PrimitiveDihedralExtractionData (GAt ctx.Γ ctx.criticalPath.a')
    (QAt ctx.Γ middle) (VAt ctx.Γ ctx.criticalPath.firstStep) module_le actor hactor
  residual_le : raw.F₀ ≤ EAt ctx.Γ ctx.criticalPath.a'
  residual_perfect : BenderSuzuki.External.hktPResidual 2 raw.F₀ = ⊤
  edge_generated : raw.F₀ ⊔ (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a') =
    GAt ctx.Γ ctx.criticalPath.a'
  coatom_commutator : ⁅raw.F₀, raw.A₀⁆ ≤ QAt ctx.Γ ctx.criticalPath.a'
  dihedral :
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let q := QuotientGroup.mk' (pCore 2 P)
    let rotation := (raw.F₀.subgroupOf P).map q
    Nonempty ((rotation ⊔ Subgroup.zpowers (q ⟨actor, module_le hactor⟩) :
      Subgroup (P ⧸ pCore 2 P)) ≃* DihedralGroup (raw.p ^ raw.n))

private theorem residual_sup_of_conjugate_generation
    (V L : Subgroup G) (x : G) (hx : x ∈ L)
    (hgen : V ⊔ V.conjBy x = L) : twoResidualIn L ⊔ V = L := by
  have hVL : V ≤ L := le_sup_left.trans_eq hgen
  let VL := V.subgroupOf L
  let xL : L := ⟨x, hx⟩
  have hconj : (VL.conjBy xL).map L.subtype = V.conjBy x := by
    rw [map_conjBy, Subgroup.map_subgroupOf_eq_of_le hVL]
    rfl
  have hgenL : VL ⊔ VL.conjBy xL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hconj, Subgroup.map_subgroupOf_eq_of_le hVL,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hs := twoResidualAmbient_top_sup_of_conjugate_generation VL xL hgenL
  have hmap := congrArg (Subgroup.map L.subtype) hs
  have hRmap : (twoResidualAmbient (⊤ : Subgroup L)).map L.subtype = twoResidualIn L :=
    map_twoResidualAmbient_of_subgroup_image ⊤ L.subtype L
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
  rw [Subgroup.map_sup, hRmap, Subgroup.map_subgroupOf_eq_of_le hVL,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap

public theorem ten_one_dihedral_configuration
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.a') :
    Nonempty (TenOneDihedralConfigurationData ctx middle actor hactor) := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let M := GAt ctx.Γ middle
  let edge := P ⊓ M
  let sylow : Sylow 2 edge := default
  let S := sylowTwoAmbient edge sylow
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVmiddle : V ≤ QAt ctx.Γ middle :=
    (show V ≤ GeneratedNeighborhoodV ctx.Γ middle from
      le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst, rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle)
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case
      (by omega : 1 < ctx.criticalPath.length)).1
  let _ : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
  have hPhi : frattiniAmbient V ≤ Q := by
    rw [frattiniAmbient, frattini_eq_bot_of_isElementaryAbelian (R := V) (p := 2),
      Subgroup.map_bot]
    exact bot_le
  have hnot : ¬ V ≤ Q := fun hle => hout (hle hactor)
  have hi := sevenEight_local_inputs ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal))
    V hVmiddle hnot hPhi sylow
  have hQ : Q = twoCoreAmbient P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' = _
    rw [ctx.Γ.twoCoreAt_def]
    rfl
  have hAP : V ≤ P := hi.actor_le.trans (sylow_le_of_mem_PSet hi.first_mem)
  have hTnot : ¬ QAt ctx.Γ middle ≤ twoCoreAmbient P := by
    intro hle
    exact hnot (hVmiddle.trans (hle.trans_eq hQ.symm))
  let e := solvablePrimitive_dihedralExtraction S hi.sectionThree P hi.first_mem
    (QAt ctx.Γ middle) hi.neighbor_core_normal V hi.actor_le actor hactor
    (hQ ▸ hout) hi.frattini_le_core hi.solvable hTnot
  let L := V ⊔ V.conjBy (e.x : G)
  have hLP : L ≤ P := by
    dsimp only [L]
    rw [← (generated_inside_and_quotient_image P V hAP e.x).1]
    exact Subgroup.map_subtype_le _
  have hF : e.F₀ = twoResidualIn L := e.residual_generated
  have hFres : e.F₀ ≤ EAt ctx.Γ ctx.criticalPath.a' := by
    rw [hF]
    change twoResidualIn L ≤ ctx.Γ.twoResidualAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_mono L P hLP
  have hperfect : BenderSuzuki.External.hktPResidual 2 e.F₀ = ⊤ := by
    rw [hF]
    exact twoResidualAmbient_has_top_twoResidual L
  have hsupp : e.F₀ ⊔ V = L := by
    rw [hF]
    exact residual_sup_of_conjugate_generation V L e.x e.x_mem_generated rfl
  have hLS : L ⊔ S = P :=
    extracted_sup_sylow_eq S hi.sectionThree P hi.first_mem hi.solvable
      (QAt ctx.Γ middle) V hAP actor hactor e
  have hSedge : S ≤ M ⊓ P := by
    have hh : S ≤ P ⊓ M := Subgroup.map_subtype_le _
    exact le_inf (hh.trans inf_le_right) (hh.trans inf_le_left)
  have hVedge : V ≤ M ⊓ P := hi.actor_le.trans hSedge
  have hgen : e.F₀ ⊔ (M ⊓ P) = P := by
    apply le_antisymm (sup_le e.F₀_le_P inf_le_right)
    calc
      P = L ⊔ S := hLS.symm
      _ = (e.F₀ ⊔ V) ⊔ S := congrArg (fun K : Subgroup G => K ⊔ S) hsupp.symm
      _ ≤ e.F₀ ⊔ (M ⊓ P) := sup_le
        (sup_le le_sup_left (hVedge.trans le_sup_right)) (hSedge.trans le_sup_right)
  have hcomm : ⁅e.F₀, e.A₀⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro coatom hcoatom rotation hrotation
    let a : P := ⟨coatom, hAP (e.A₀_le hcoatom)⟩
    let r : P := ⟨rotation, e.F₀_le_P hrotation⟩
    let q := QuotientGroup.mk' (pCore 2 P)
    have hc := e.A₀_centralizes_rotation coatom hcoatom (q r)
      (Subgroup.mem_map_of_mem q hrotation)
    change q a * q r = q r * q a at hc
    have hk : ⁅a, r⁆ ∈ pCore 2 P := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅a, r⁆ = 1
      rw [map_commutatorElement, commutatorElement_def, hc]
      simp [mul_assoc]
    rw [hQ]
    exact Subgroup.mem_map_of_mem P.subtype hk
  let q := QuotientGroup.mk' (pCore 2 P)
  let rotation := (e.F₀.subgroupOf P).map q
  let t := q ⟨actor, hAP hactor⟩
  have hcyclic : IsCyclic rotation := by
    rw [show rotation = Subgroup.zpowers (q e.x) from e.rotation_eq]
    infer_instance
  have hodd : Odd (Nat.card rotation) := by rw [e.rotation_card]; exact e.odd_p.pow
  have ht : t ∉ rotation := by
    intro ht
    have hdvd := orderOf_dvd_natCard (⟨t, ht⟩ : rotation)
    have horder : orderOf t = 2 := orderOf_eq_prime e.reflection_involution.2
      e.reflection_involution.1
    apply hodd.not_two_dvd_nat
    simpa only [Subgroup.orderOf_mk, horder] using hdvd
  have hdihedral := rotation.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted t
    hcyclic e.reflection_involution.2 ht e.reflected
  rw [e.rotation_card] at hdihedral
  exact ⟨⟨hAP, e, hFres, hperfect, hgen, hcomm, hdihedral⟩⟩

public theorem ten_one_nontransvection_configuration
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ∃ actor : G, ∃ hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep,
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
        QuotientCardEq
          (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
            ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4 ∧
        ZAt ctx.Γ ctx.criticalPath.firstStep ≤
          ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ∧
        Nonempty (TenOneDihedralConfigurationData ctx middle actor hactor) := by
  obtain ⟨actor, hactor, hout, hcase⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  obtain ⟨hindex, hcenter⟩ := hcase.resolve_left (hno actor hactor hout)
  exact ⟨actor, hactor, hout, hindex, hcenter,
    ten_one_dihedral_configuration ctx middle hpath actor hactor hout⟩

end Stellmacher.SectionTen
