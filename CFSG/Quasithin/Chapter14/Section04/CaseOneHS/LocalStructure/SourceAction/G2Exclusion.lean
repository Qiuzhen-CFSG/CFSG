module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.CatalogueExclusions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.SmallCenter
public import Theory.GroupTheory.CoprimeSubgroupLift
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Theory.Representation.G2BinaryPointCubicFixer
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Excluding the literal G₂(2) action on the original HS flag

The six-dimensional order calculation gives an order-two conjugate-center
image. The self-centralizing simple derived group lies in the image of
C_H(Z(U)). An order-three point stabilizer in that image lifts through its
two-group kernel and fixes V₂, hence normalizes the conjugate center and
centralizes its order-two image. The concrete binary point-parabolic
calculation contradicts this for a nonidentity involution.

All coordinates, quotient maps and subgroups are the original ones.
Centerlessness remains the preceding source premise. The final consumer
reduces the existing marked alternatives to dimension four or whole-component
recognition; it does not assume or assert an exhaustive action classifier.
Those remaining identifications are still required for ActionStructure.
Source: Aschbacher--Smith 14.3.24 and 14.3.32, printed pp.1000,1003--1004.
-/

public section

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- Cubics in the original center-centralizing point image centralize the
order-two conjugate-center image. -/
theorem source_point_cube_centralizes_conjugate_center
    (v : Additive F.Uhat) (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (g : G) (hgP : g ∈ F.P L)
    (hz : Nat.card (F.terminalDot (conjugate F.ZU g)) = 2)
    (a : F.TerminalHdot)
    (ha : a ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : a ∈ F.terminalDot (centralizer (F.ZU : Set G))) (ha3 : a^3=1) :
    a ∈ centralizer (F.terminalDot (conjugate F.ZU g) : Set F.TerminalHdot) := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let D := C.map q
  let f : C →* D := q.subgroupMap C
  have hk : IsPGroup 2 f.ker := by
    have hle : f.ker ≤ (pCore 2 F.H).subgroupOf C := by
      intro x hx
      apply source_center_centralizing_kernel_le_core d earlier hq chosen structural alternatives F hne
      exact ⟨x.property,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩
    exact (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf C)).to_le hle
  let aa : D := ⟨a,haZ⟩
  have hao : orderOf aa ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext ha3)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card (zpowers aa)) := by
    rw [hn,Nat.card_zpowers]
    exact ((by decide : Nat.Coprime 2 3).pow_left n).coprime_dvd_right hao
  obtain ⟨s,hs⟩ := f.exists_subgroup_section_of_coprime_kernel (q.subgroupMap_surjective C)
    (zpowers aa) hcop
  let b : C := s ⟨aa,mem_zpowers aa⟩
  have hb3 : b^3=1 := by
    rw [← map_pow]
    have hh : (⟨aa,mem_zpowers aa⟩ : zpowers aa)^3=1 := Subtype.ext (Subtype.ext ha3)
    rw [hh,map_one]
  have hba : q b.val = a := by
    have hh : f b = aa := DFunLike.congr_fun hs (⟨aa,mem_zpowers aa⟩ : zpowers aa)
    exact congrArg Subtype.val hh
  have hbplane : (b.val:G) ∈ centralizer (F.Vi 2 : Set G) :=
    source_point_preimage_centralizes_plane_of_cube_one d earlier hq chosen structural alternatives
      F hne v hline b.val (hba.symm ▸ ha) b.property (congrArg Subtype.val hb3)
  have hpoint : conjugate (F.Vi 1) g ≤ F.Vi 2 :=
    conjugate_le_of_normalizes (F.monotone (by decide : 1≤2)) g
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
  have hn : (b.val:G) ∈ normalizer (conjugate F.ZU g : Set G) := by
    have hHn : conjugate F.H g ≤ normalizer (conjugate F.ZU g : Set G) := by
      simpa only [conjugate,map_equiv_normalizer_eq] using
        map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) F.H_normalizes_ZU
    apply hHn
    change (b.val:G) ∈ (normalizer (F.Vi 1 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact Subgroup.centralizer_le_normalizer _ (centralizer_le hpoint hbplane)
  have hnH : b.val ∈ normalizer ((conjugate F.ZU g).subgroupOf F.H : Set F.H) := by
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    exact hn (x:G)
  apply normalizer_le_centralizer_of_card_two _ hz
  rw [← hba]
  exact le_normalizer_map q (mem_map_of_mem q hnH)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The natural G₂(2) row is excluded on the original nonextraspecial flag. -/
theorem source_no_caseSix (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) :
    ¬ CaseSix F.terminalRepresentation := by
  rintro ⟨hd,e,c,he⟩
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hc : Nat.card F.Uhat = 64 := by
    rw [← Nat.card_congr (Additive.toMul (α := F.Uhat))]
    simpa [hd] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat))
  have hr : primeRank 2 F.TerminalHdot ≤ 3 := by
    rw [primeRank_equiv 2 e,Atlas.G2.EvenTwoRank.two_rank (ZMod 2) (n := 1) (by simp)]
  have hX : Nat.card (F.terminalDot (F.X g)) ≤ 8 :=
    (primeRank_le_iff_elementary_card_le F.TerminalHdot).mp hr _ inferInstance
  have hcenter := (source_six_dimensional_orders d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH hX).2.1
  have hzcard : Nat.card (F.terminalDot (conjugate F.ZU g)) = 2 := by
    let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
    have hzH : conjugate F.ZU g ≤ F.H :=
      (F.conjugate_ZU_le_X g).trans (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP))
    let q := dotMap F F.uhatAction (conjugate F.ZU g) hzH
    have hk : q.ker=f.ker := dotMap_ker F F.uhatAction (conjugate F.ZU g) hzH
    let eqv := (QuotientGroup.quotientKerEquivOfSurjective q
      (dotMap_surjective F F.uhatAction (conjugate F.ZU g) hzH)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange f))
    have hh := source_conjugate_center_image_order d earlier hq chosen structural alternatives
      F hne hI g hgP hgH
    rw [hcenter] at hh
    change Nat.card (dotImage F F.uhatAction (conjugate F.ZU g))=2
    rw [Nat.card_congr eqv.toEquiv]
    change 2 * Nat.card f.range = 4 at hh
    omega
  let K := commutator F.TerminalHdot
  have hmap : K.map e.toMonoidHom=commutator (Atlas.G2.Model (ZMod 2)) := by
    change (commutator F.TerminalHdot).map e.toMonoidHom = _
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,commutator_def]
  let eK := (e.subgroupMap K).trans (MulEquiv.subgroupCongr hmap)
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hKa : ¬ IsMulCommutative K := by
    intro hcomm
    let := hcomm
    have hp : (Nat.card K).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr eK.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hp
    norm_num at hp
  have hKc : centralizer (K : Set F.TerminalHdot)=⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    apply Atlas.G2.LieAutomorphismExtensions.binaryConjugation_injective
    rw [map_one]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    obtain ⟨k,hk,hky⟩ := (show y.val∈K.map e.toMonoidHom from hmap.symm ▸ y.property)
    have hcomm := congrArg e (hx k hk)
    have hky' : e k=y.val := hky
    change e x*y.val*(e x)⁻¹=y.val
    have hh : e x*y.val=y.val*e x := by
      simpa only [map_mul,hky'] using hcomm.symm
    rw [hh,mul_inv_cancel_right]
  have hKC := source_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH K hKa hKc
  have hzX : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hzbot : F.terminalDot (conjugate F.ZU g)=⊥ := by
    apply bot_unique
    intro z hz
    apply mem_bot.mpr
    apply Atlas.G2.Natural.BinaryPointFlag.eq_one_of_point_cubic_fixer
      F.terminalRepresentation e c he v hyp.point_ne_zero z (hyp.fixes_point (hzX hz))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) z (hzX hz))
    intro a ha haK ha3
    exact source_point_cube_centralizes_conjugate_center d earlier hq chosen structural alternatives
      F hne v hline.symm g hgP hzcard a ha (hKC haK) ha3 z hz
  have hh := Nat.card_congr (MulEquiv.subgroupCongr hzbot).toEquiv
  rw [hzcard,card_bot] at hh
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
open ChapterG.Section11.ExchangedRecognition
/-- Apply the literal catalogue sieve to the original HS flag, retaining the
whole-component recognition obligation with all its original hypotheses. -/
theorem source_four_or_whole_action_of_centerless (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (CaseTwo F.terminalRepresentation B ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_remaining_action_of_centerless d earlier hq chosen structural alternatives F hne hZ hI g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with (h2 | h6) | hwhole
  · exact Or.inl h2
  · exact (source_no_caseSix d earlier hq chosen structural alternatives F hne hZ hI h6).elim
  · exact Or.inr hwhole

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
