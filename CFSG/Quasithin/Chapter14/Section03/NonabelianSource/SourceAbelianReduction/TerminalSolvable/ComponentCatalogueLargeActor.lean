module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogue
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SmallCenterKernel
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The degree-six component kernel in the larger-actor branch

In the degree-six, actor-rank-three alternative of original 14.3.14, the
G.10 dimension equation bounds the smaller actor by order two. The literal
displaced-center equivalence transfers this bound to the tilded center.
The proved two-element automorphism-kernel calculation then identifies the
terminal kernel with O₂(H), and subnormality gives the restricted kernel
required on each lifted component. The ambient kernel equality is proved
only from these numerical hypotheses; it is not assumed for a general row.

An actual equivalence of the full dotted group with G₂(2) identifies every
ordinary component with the concrete derived carrier G₂(2)′ and makes it
normal. The source applications retain the original quotient map and lift.
The degree-four/degree-six recognition remains an explicit input, not a
classification asserted by this module.

Source: Aschbacher--Smith 12.8.10--13, 14.3.13--15 and G.11.2, printed
pp.853--856, 993--994 and 364--367. The binary G₂ carrier and simplicity
proof come from the licensed ATLAS port cited by their imported modules.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic

private theorem smaller_card_le_two_of_six_three
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {B : LinearMap.BilinForm (ZMod 2) W}
    {v : W} {E : Submodule (ZMod 2) W} {X : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (hyp : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hd : finrank (ZMod 2) W = 6)
    (hm : finrank (ZMod 2) (Additive X) = 3) : Nat.card X₀ ≤ 2 := by
  have hE := B.twice_finrank_le_of_isotropic hyp.nondegenerate E hyp.isotropic
  have he := hyp.dimension
  have hq : 2 ≤ Group.rank (X ⧸ X₀) := by omega
  have hqf := IsElementaryAbelian.rank_le_finrank (p := 2) (X ⧸ X₀)
  have hcX : Nat.card X = 8 := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod, hm, show 2 ^ 3 = 8 from rfl] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
  have hcQ : 4 ≤ Nat.card (X ⧸ X₀) := by
    rw [Nat.card_congr Additive.ofMul,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (hq.trans hqf)
  have hc := X₀.card_mul_index
  rw [index_eq_card,hcX] at hc
  nlinarith

variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    {T : Sylow 2 G} {L M : Subgroup G}

/-- In the degree-six, rank-three source row the literal smaller actor has
order at most two. The center quotient therefore has order at most two,
and the original tilded action forces the terminal kernel to equal O₂(H). -/
theorem rankTwo_terminal_kernel_of_six_three
    (h : RankTwoHypothesis κ T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3) :
    F.terminalHatAction.ker = pCore 2 F.H := by
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hc := smaller_card_le_two_of_six_three hyp hd hm
  have hle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hc
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  let eZ := (Recognition.rankTwo_terminal_center_equiv h F d hne g hgP hgH).symm.trans
    (F.terminalCenterTildeEquiv hZH)
  have hcZ : Nat.card (F.tilde F.ZU) ≤ 2 := by
    rw [← Nat.card_congr eZ.toEquiv]
    exact hc
  have hp := Recognition.terminal_kernel_isPGroup_of_tilde_center_card_le_two F d hcZ
  exact le_antisymm (le_sSup ⟨inferInstance,hp⟩)
    (F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide) d.tilde_kernel)

/-- Restrict the proved degree-six kernel to the actual C-component;
subnormality identifies its intersection with the intrinsic two-core. -/
theorem ComponentLift.restricted_kernel_of_six_three
    (h : RankTwoHypothesis κ T L M)
    {F : InvariantFlag T (rankTwoSeed T M) 2}
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) {g : G}
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3)
    {K : Subgroup G} (hK : ComponentLift F g K) :
    F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
      pCore 2 (K.subgroupOf F.H) := by
  rw [rankTwo_terminal_kernel_of_six_three h F hne g hgP hgH hyp hd hm]
  exact (pCore_subnormal_eq_comap 2 hK.component.subnormal).symm

/-- Every ordinary component in the full binary octonion group is its
actual derived subgroup, not the full group. -/
theorem component_eq_binaryG2_derived
    (L : Subgroup (Atlas.G2.Model (ZMod 2)))
    (hL : IsComponent (Atlas.G2.Model (ZMod 2)) L) :
    L = Atlas.G2.BinaryParabolicPair.DerivedModel := by
  let D := Atlas.G2.BinaryParabolicPair.DerivedModel
  let := hL.2
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  have hLD : L ≤ D := by
    change L ≤ commutator (Atlas.G2.Model (ZMod 2))
    rw [← commutator_eq_self (H := L)]
    exact commutator_mono le_top le_top
  have hne : L.subgroupOf D ≠ ⊥ := by
    intro he
    have hh := congrArg (map D.subtype) he
    rw [map_subgroupOf_eq_of_le hLD,Subgroup.map_bot] at hh
    exact hL.isCComponent.ne_bot hh
  have ht := ((show (L.subgroupOf D).IsSubnormal from hL.1.subgroupOf)).eq_bot_or_top_of_isSimpleGroup
    (inferInstance : IsSimpleGroup D)
  exact le_antisymm hLD (subgroupOf_eq_top.mp (ht.resolve_left hne))

/-- An actual full G₂(2) equivalence recognizes each component as G₂(2)′
and proves its relative normality. -/
theorem component_binaryG2_image
    {D : Type*} [Group D] (e : D ≃* Atlas.G2.Model (ZMod 2))
    (L : Subgroup D) (hL : IsComponent D L) :
    L.Normal ∧ Nonempty (L ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) := by
  have he := component_eq_binaryG2_derived (L.map e.toMonoidHom) (hL.map_equiv e)
  have hn : (L.map e.toMonoidHom).Normal := he.symm ▸ inferInstance
  have hc := hn.comap e.toMonoidHom
  rw [comap_map_eq_self_of_injective e.injective] at hc
  exact ⟨hc,⟨(e.subgroupMap L).trans (MulEquiv.subgroupCongr he)⟩⟩


open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The literal source degree-six alternative supplies a normal moved G₂(2)′
component and its intrinsic restricted kernel. The only recognition inputs
are the numerical degree/rank and an actual equivalence of the full dotted group. -/
theorem source_component_large_actor_of_six_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3)
    (eG : F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H) := by
  have hF := Recognition.original_terminal_fitting_centralizer_ne_bot
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn
  obtain ⟨D,hD,hmove,_⟩ := hyp.exists_moved_component_constituents hn hF
  obtain ⟨K,hKH,hlocal,hcomp,he,_,hspan⟩ :=
    Recognition.terminal_component_lift hG F (by decide) D hD
  change F.terminalDot K = D at he
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,he.symm ▸ hD,he.symm ▸ hmove,hspan⟩
  obtain ⟨hnorm,hiso⟩ := component_binaryG2_image eG D hD
  refine ⟨K,hK,he.symm ▸ hnorm,he.symm ▸ hiso,?_⟩
  exact hK.restricted_kernel_of_six_three
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) hne hgP hgH hyp hd hm

/-- The degree-six output supplies the actual catalogue quotient row.
No assumption identifies the ambient kernel or the intrinsic two-core quotient. -/
theorem source_component_catalogue_of_six_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3)
    (eG : F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  obtain ⟨K,hK,hnorm,⟨eK⟩,hk⟩ := source_component_large_actor_of_six_three
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hd hm eG
  exact ⟨K,hK,Or.inl ⟨hK.eq_conjugateSpanBy_of_image_normal hnorm,
    Or.inl ⟨(hK.twoCoreQuotientEquivDot_of_restricted_kernel hk).trans eK⟩⟩⟩

/-- Conditional assembly of the larger-actor source branch. The numerical
alternatives and degree-four component recognition are independent inputs;
the existing A₆ source owner excludes that row. The degree-six kernel,
relative normality, model identification and local lift are discharged here.
This theorem is not an unconditional proof of 14.3.14 or 14.3.15. -/
theorem source_component_large_actor_of_degree_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hdegrees :
      (finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))))
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    (∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
      ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
    (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H)) := by
  rcases hdegrees with ⟨hd,_⟩ | ⟨hd,hm,⟨eG⟩⟩
  · have hF := Recognition.original_terminal_fitting_centralizer_ne_bot
      hG T hempty hM hu hmany hcard e F hne g hgP hgH hn
    obtain ⟨D,hD,hmove,_⟩ := hyp.exists_moved_component_constituents hn hF
    rcases hfour hd D hD hmove with h5 | h6
    · exact Or.inl ⟨D,hD,hmove,h5⟩
    · obtain ⟨K,hKH,hlocal,hcomp,he,_,hspan⟩ :=
        Recognition.terminal_component_lift hG F (by decide) D hD
      change F.terminalDot K = D at he
      have hK : ComponentLift F g K :=
        ⟨hKH,hlocal,hcomp,he.symm ▸ hD,he.symm ▸ hmove,hspan⟩
      exact (hsix K hK (he.symm ▸ h6)).elim
  · exact Or.inr (source_component_large_actor_of_six_three
      hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hd hm eG)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
