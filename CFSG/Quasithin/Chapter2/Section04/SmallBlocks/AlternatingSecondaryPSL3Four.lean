module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryComponentSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.CentralQuotient
public import Theory.SpecificGroups.PSL3Four.CentralCover.SylowFixedInnerRank
public import Theory.GroupTheory.CentralActorRank
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The exceptional linear-three-four component in the secondary centralizer

The original marked involution fixes a component Sylow subgroup. Its source
model action is inner, since its central quotient is neither A₆ nor A₇.
The pure binary covering center then has trivial Frattini subgroup, and the
lifted elementary root plane has order sixteen times the center. Two-rank
at most four forces the component center to be trivial. Joining its root
plane to the independent central involution gives ambient two-rank at least
five. No normality of the ordinary component is required.

Source: Aschbacher–Smith, the secondary-centralizer component inspection in
2.4.29, printed pp.545–546, and I.2.2(3), printed pp.409–410.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Chapter1.QuasisimpleInvolutions ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {C : GroupClass.{u}}
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The marked source component cannot have central quotient PSL₃(4)
inside a rank-four group with a central involution. -/
theorem MathieuSourceSetup.psl_three_four_false (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC C X)
    (u : H) (hu : u ∈ center H) (hu2 : orderOf u = 2)
    (hrank : primeRank 2 H ≤ 4)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4) : False := by
  let D := L.subgroupOf H
  let eD : D ≃* L := subgroupOfEquivOfLe c.component_le
  let : IsQuasisimple D := c.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eD
  obtain ⟨hc,⟨e⟩⟩ := center_and_native_quotient_of_psl_four hmodel
  obtain ⟨_,α₀,P₀,hα₀,d₀,_⟩ := (c.lemma115_hypotheses hG).component_inputs D c.component
  let α := (MulAut.congr eD) α₀
  let P := P₀.mapSurjective (f := eD.toMonoidHom) eD.surjective
  have hα (x : L) : (α x : G) = z * (x : G) * z⁻¹ := hα₀ (eD.symm x)
  obtain ⟨β,hβ,hm⟩ := c.modelAction115 hG hABC
  have heq : β = α := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext ((hβ x).trans (hα x).symm)
  rw [heq] at hm
  have hi : α ∈ (MulAut.conj : L →* MulAut L).range := by
    rcases inner_or_alternating_quotient_of_modelAction hm with h | h6 | h7
    · exact h
    · obtain ⟨e6⟩ := h6
      have hh := Nat.card_congr (e.symm.trans e6).toEquiv
      rw [Matrix.PSL3Four.card_PSL,nat_card_alternatingGroup,Nat.card_fin] at hh
      norm_num [Nat.factorial] at hh
    · obtain ⟨e7⟩ := h7
      have hh := Nat.card_congr (e.symm.trans e7).toEquiv
      rw [Matrix.PSL3Four.card_PSL,nat_card_alternatingGroup,Nat.card_fin] at hh
      norm_num [Nat.factorial] at hh
  have hfix : ∀ x ∈ P, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change eD (α₀ (eD.symm (eD x))) = eD x
    rw [eD.symm_apply_apply,d₀.fixes x hx]
  have ho : orderOf α = 2 := ((MulAut.congr eD).orderOf_eq α₀).trans d₀.order_two
  have hrL : primeRank 2 L ≤ 4 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion c.component_le)
      (inclusion_injective c.component_le)).trans hrank
  have hZ : center L = ⊥ :=
    Matrix.PSL3Four.center_eq_bot_of_sylow_fixed_inner_involution e (hc.symm ▸ pCore_isPGroup)
      P α ho hi hfix hrL
  have hZD : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : eD x ∈ center L := (centerCongr eD ⟨x,hx⟩).property
    rw [hZ,mem_bot] at he
    exact eD.injective (he.trans eD.map_one.symm)
  let eL : L ≃* Matrix.PSL3Four.PSL :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  let eN := eD.trans eL
  obtain ⟨A,hA,hcard⟩ := Matrix.PSL3Four.exists_elementary_sixteen
  let := hA
  let E := A.map eN.symm.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hE : Nat.card E = 2 ^ 4 := by
    rw [card_map_of_injective eN.symm.injective,hcard]
    norm_num
  have hh := Subgroup.primeRank_ge_of_central_actor D hZD E hE u hu hu2
  omega

/-- Apply the exclusion to the literal involution centralizer, discharging
centrality, the intrinsic element order, and the universal A/B/C input. -/
theorem MathieuSourceSetup.centralizer_psl_three_four_false
    {u : G} {P : Sylow 2 (centralizer ({u} : Set G))}
    (c : MathieuSourceSetup (centralizer ({u} : Set G)) L M P z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hu2 : orderOf u = 2)
    (hrank : primeRank 2 (centralizer ({u} : Set G)) ≤ 4)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4) : False := by
  let H := centralizer ({u} : Set G)
  let a : H := ⟨u,mem_centralizer_singleton_iff.mpr rfl⟩
  have ha : a ∈ center H := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have ho : orderOf a = 2 :=
    (orderOf_injective H.subtype H.subtype_injective a).symm.trans hu2
  exact c.psl_three_four_false hG
    (fun X _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := X))
    a ha ho hrank hmodel

end CFSG.Quasithin.Chapter2.ComponentRefinement

namespace CFSG.Quasithin.Chapter2
open Stellmacher
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
variable (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
variable (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
variable (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
variable (hsingle : d.L0 = d.block)
variable (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
variable (u : G) (hu2 : orderOf u = 2)
variable (huR : u ∈ (center (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
  (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype)
variable (hout : ¬ d.H ⊓ centralizer ({u} : Set G) ≤ M)
variable (hMu : M ⊓ centralizer ({u} : Set G) = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
variable (hi : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)).relIndex (T : Subgroup G) = 2)
variable (P : Sylow 2 (centralizer ({u} : Set G)))
variable (hP : (P : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype =
  (T : Subgroup G) ⊓ centralizer ({u} : Set G))
variable (z : G) (hz : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
variable (hz2 : orderOf z = 2)


include hG hM hTM hu hST hsingle hA hu2 huR hout hMu hi hP hz hz2 in
/-- The original single-alternating source markings exclude the exceptional
row for the literal ordinary component and its literal two-core quotient. -/
theorem MinimalBlockSetup.single_alternating_secondary_psl_three_four_false_of_marks
    (hrank : primeRank 2 (centralizer ({u} : Set G)) ≤ 4)
    (K : Subgroup (centralizer ({u} : Set G)))
    (hK : IsComponent (centralizer ({u} : Set G)) K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) : False := by
  let H := centralizer ({u} : Set G)
  let L := K.map H.subtype
  let e : K ≃* L := K.equivMapOfInjective H.subtype H.subtype_injective
  have hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 := by
    obtain ⟨F,hF,hfin,hcard,⟨f⟩⟩ := hmodel
    exact ⟨F,hF,hfin,hcard,
      ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans f⟩⟩
  let c := d.single_alternating_secondary_refinement_setup_of_marks hG T hM hTM hu hST
    hsingle hA u hu2 huR hout hMu hi P hP z hz hz2 K hK
  exact c.centralizer_psl_three_four_false hG hu2 hrank hm

end CFSG.Quasithin.Chapter2
