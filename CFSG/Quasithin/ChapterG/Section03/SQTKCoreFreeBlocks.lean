module

public import CFSG.Quasithin.ChapterG.Section03.CoreFreeBlockModels
import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedSource
import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
import Theory.GroupTheory.CComponent.ResidualLifting
import Theory.SpecificGroups.BinaryLinear.Perfect
import Theory.SpecificGroups.BinaryLinear.EvenLieLevi
import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Literal SQTK block lifts without a spanning assumption

Triviality of the actual actor two-core makes every produced block action
faithful. The full binary blocks are sections of the original SQTK group,
so each has dimension three through five and a literal C-component lift.
The conjugacy family of one lift bounds the block count by two. A companion
forces dimension three by the rank-two component normality theorem.

Source: Aschbacher--Smith1.2.1 and12.7.18, printed pp.504 and845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
open ChapterA.Section02
universe u
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H : Type u} [Group H] [Finite H]

private def binary_coordinates : V ≃ₗ[ZMod 2] OuterCyclic.Space (Module.finrank (ZMod 2) V) :=
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin])

private def binary_group_coordinates : BinaryLinear.GL V ≃*
    OuterCyclic.LinearGroup (Module.finrank (ZMod 2) V) :=
  SmallParabolicLevi.linearGroupCongr binary_coordinates

private theorem binary_quasisimple (hn : 3 ≤ Module.finrank (ZMod 2) V) :
    IsQuasisimple (BinaryLinear.GL V) := by
  let n := Module.finrank (ZMod 2) V
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn
  let : IsSimpleGroup (OuterCyclic.LinearGroup n) :=
    (OuterCyclic.projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  let : Group.IsPerfect (OuterCyclic.LinearGroup n) := linearGroup_isPerfect n hn
  let : IsSimpleGroup (BinaryLinear.GL V) := binary_group_coordinates.isSimpleGroup
  let : Group.IsPerfect (BinaryLinear.GL V) := Group.IsPerfect.ofSurjective
    (f := binary_group_coordinates.symm.toMonoidHom) binary_group_coordinates.symm.surjective
  have hz : center (BinaryLinear.GL V) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }

private theorem section_dimension (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hsection : IsSectionOf (BinaryLinear.GL V) H)
    (hn : 3 ≤ Module.finrank (ZMod 2) V) : Module.finrank (ZMod 2) V ≤ 5 := by
  let := binary_quasisimple hn
  have hsem : IsSemisimple (BinaryLinear.GL V) := by
    let : IsQuasisimple (⊤ : Subgroup (BinaryLinear.GL V)) := IsQuasisimple.of_mulEquiv topEquiv.symm
    exact top_unique (le_sSup (show IsComponent (BinaryLinear.GL V) ⊤ from ⟨.top,inferInstance⟩))
  have hs := (theoremA_knownSimple (G := H)).stronglyQuasithin_section
    hH.stronglyQuasithin hH.isKGroup hsection hsem
  by_contra hn6
  have hn6 : 6 ≤ Module.finrank (ZMod 2) V := by omega
  let e := binary_group_coordinates.trans
    (OuterCyclic.projectiveEquivLinear (by omega : 0 < Module.finrank (ZMod 2) V)).symm
  exact EvenLieLevi.not_quasithin_projective hn6 (isQuasithin_of_equiv e hs.quasithin)

private theorem sqtk_quotient (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
  refine ⟨?_,hH.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)

private theorem component_lift {A : Type u} [Group A]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (q : H →* A) (hq : Function.Surjective q)
    (B : Subgroup A) (hB : IsComponent A B) :
    ∃ C : Subgroup H, C.IsCComponent ∧ C.map q = B := by
  apply exists_cComponent_map_eq_of_preimage_layer q hq hB.isCComponent
  exact Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
      (fun Y _ _ => theoremA_knownSimple (G := Y))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun Y _ _ => theoremC_knownSimple (G := Y))) hX hO)
    (sqtk_quotient (hH.subgroup (B.comap q)))

/-- Each actual block has a literal C-component lift through the
full quotient map, and its binary dimension is between three and five. -/
theorem sqtk_core_free_block_lifts
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (Q : Subgroup (BinaryLinear.GL V)) (q : H →* Q) (hq : Function.Surjective q)
    (x : V) (hsource : Hypotheses Q (MulAction.orbit Q x))
    (hcore : pCore 2 Q = ⊥) (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (hl : LocalStructure Q (MulAction.orbit Q x)) :
    ∀ i : OrbitBlock Q (MulAction.orbit Q x),
      (3 ≤ Module.finrank (ZMod 2) (blockSpace Q (MulAction.orbit Q x) i) ∧
        Module.finrank (ZMod 2) (blockSpace Q (MulAction.orbit Q x) i) ≤ 5) ∧
      ∃ C : Subgroup H, C.IsCComponent ∧
        C.map q = (blockGroup Q (MulAction.orbit Q x) i).subgroupOf Q := by
  let Δ := MulAction.orbit Q x
  let D := generated Q Δ
  obtain ⟨e,_,_,_⟩ := core_free_block_models hsource hcore hf hd
  have hDQ : D ≤ Q := generated_le Q Δ
  have hnorm : (D.subgroupOf Q).Normal := generated_normal Q Δ (by
    intro g hg v hv
    obtain ⟨b,rfl⟩ := MulAction.mem_orbit_iff.mp hv
    exact MulAction.mem_orbit_iff.mpr ⟨(⟨g,hg⟩ : Q)*b,rfl⟩)
  intro i
  let B := blockGroup Q Δ i
  have hjoin : (⨆ i : OrbitBlock Q Δ,blockGroup Q Δ i) = D := hd.group_join
  have hBD : B ≤ D := (le_iSup (blockGroup Q Δ) i).trans hjoin.le
  have hBQ : B ≤ Q := hBD.trans hDQ
  let := binary_quasisimple (hl.dimension_ge_three i)
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (e i).symm
  let : IsQuasisimple (B.subgroupOf Q) := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBQ).symm
  have hDN : D ≤ normalizer (B : Set (BinaryLinear.GL V)) := by
    rw [←hjoin]
    apply iSup_le
    intro j
    by_cases hij : i = j
    · subst j
      exact B.le_normalizer
    · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      intro g hg
      apply mem_centralizer_iff.mpr
      intro b hb
      exact (hd.groups_commute i j hij b hb g hg).eq
  have hnBQ : ((B.subgroupOf Q).subgroupOf (D.subgroupOf Q)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hDN hg) (b : BinaryLinear.GL V)
  have hcomp : IsComponent Q (B.subgroupOf Q) :=
    ⟨IsSubnormal.step _ _ (subgroupOf_mono Q hBD) hnorm.isSubnormal hnBQ,inferInstance⟩
  have hsection : IsSectionOf (BinaryLinear.GL (blockSpace Q Δ i)) H :=
    (((IsSectionOf.subgroup (B.subgroupOf Q)).of_mulEquiv
      ((e i).symm.trans (subgroupOfEquivOfLe hBQ).symm)).ambient_surjective q hq)
  exact ⟨⟨hl.dimension_ge_three i,section_dimension hH hsection (hl.dimension_ge_three i)⟩,
    component_lift hH q hq _ hcomp⟩

/-- The literal blocks form an image of one lifted component's conjugacy
family, so the original SQTK orbit bound allows at most two blocks. -/
theorem sqtk_core_free_block_count
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (Q : Subgroup (BinaryLinear.GL V)) (q : H →* Q) (hq : Function.Surjective q)
    (x : V) (hsource : Hypotheses Q (MulAction.orbit Q x))
    (hcore : pCore 2 Q = ⊥) (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (hl : LocalStructure Q (MulAction.orbit Q x)) :
    Nat.card (OrbitBlock Q (MulAction.orbit Q x)) ≤ 2 := by
  classical
  let Δ := MulAction.orbit Q x
  let B (i : OrbitBlock Q Δ) := blockGroup Q Δ i
  obtain ⟨e,_,_,_⟩ := core_free_block_models hsource hcore hf hd
  have hBQ (i : OrbitBlock Q Δ) : B i ≤ Q := generated_le Q i.val
  have hne (i : OrbitBlock Q Δ) : B i ≠ ⊥ := by
    let := binary_quasisimple (hl.dimension_ge_three i)
    let : IsQuasisimple (B i) := IsQuasisimple.of_mulEquiv (e i).symm
    let : IsSimpleGroup ((B i) ⧸ center (B i)) := IsQuasisimple.simple
    let : Nontrivial (B i) := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (center (B i)))
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have hBi : Function.Injective B := by
    intro i j hij
    by_contra hneij
    have hdij := hd.group_independent.pairwiseDisjoint hneij
    change Disjoint (B i) (B j) at hdij
    rw [hij] at hdij
    exact hne j (disjoint_self.mp hdij)
  let i : OrbitBlock Q Δ := ⟨MulAction.orbit (generated Q Δ) x,x,MulAction.mem_orbit_self x,rfl⟩
  obtain ⟨C,hC,hCq⟩ := (sqtk_core_free_block_lifts hH Q q hq x hsource hcore hf hd hl i).2
  let f := Q.subtype.comp q
  have hCf : C.map f = B i := by
    rw [show C.map f = (C.map q).map Q.subtype from (map_map _ _ _).symm,hCq,
      map_subgroupOf_eq_of_le (hBQ i)]
  have hg (j : OrbitBlock Q Δ) : ∃ g : H,
      (C.map (MulAut.conj g).toMonoidHom).map f = B j := by
    obtain ⟨a,ha,he⟩ := hd.groups_conjugate i j
    obtain ⟨g,hg⟩ := hq ⟨a,ha⟩
    refine ⟨g,?_⟩
    have hconj : (C.map (MulAut.conj g).toMonoidHom).map f =
        (C.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro c
      change f (g*c*g⁻¹) = f g*f c*(f g)⁻¹
      rw [map_mul,map_mul,map_inv]
    rw [hconj,hCf]
    have hfg : f g = a := congrArg Subtype.val hg
    rw [hfg]
    exact he
  choose g hg using hg
  let lift : OrbitBlock Q Δ →
      Set.range (fun g : H => C.map (MulAut.conj g).toMonoidHom) :=
    fun j => ⟨C.map (MulAut.conj (g j)).toMonoidHom,⟨g j,rfl⟩⟩
  have hinj : Function.Injective lift := by
    intro j k he
    apply hBi
    exact (hg j).symm.trans ((congrArg (fun D : Subgroup H => D.map f)
      (congrArg Subtype.val he)).trans (hg k))
  have hc : Nat.card (Set.range (fun g : H => C.map (MulAut.conj g).toMonoidHom)) ≤ 2 := by
    rw [Nat.card_coe_set_eq,ncard_conjugates_eq_index_normalizer]
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source (sqtk_quotient hH) hC with hn | hi
    · let := hn
      rw [normalizer_eq_top,index_top]
      omega
    · omega
  exact (Nat.card_le_card_of_injective lift hinj).trans hc


private theorem block_rank_two {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (hn : 4 ≤ Module.finrank (ZMod 2) W) :
    2 ≤ primeRank 3 (BinaryLinear.GL W) := by
  let n := Module.finrank (ZMod 2) W
  let e : W ≃ₗ[ZMod 2] OuterCyclic.Space n := LinearEquiv.ofFinrankEq _ _ (by
    simp only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin]
    rfl)
  let E := (SmallParabolicLevi.linearGroupCongr e).trans (OuterCyclic.slEquivLinear n).symm
  rw [primeRank_equiv 3 E]
  exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hn

private theorem rank_two_lifts {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hr : 2 ≤ primeRank 3 B) :
    2 ≤ primeRank 3 A := by
  by_contra hn
  let P : Sylow 3 A := Classical.choice inferInstance
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (show primeRank 3 A ≤ 1 by omega)
  have hB := P.primeRank_le_one_of_surjective hc f hf
  omega

/-- A companion block forces the literal full linear action to have degree three. -/
theorem sqtk_core_free_block_dimension_three
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (Q : Subgroup (BinaryLinear.GL V)) (q : H →* Q) (hq : Function.Surjective q)
    (x : V) (hsource : Hypotheses Q (MulAction.orbit Q x))
    (hcore : pCore 2 Q = ⊥) (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (hl : LocalStructure Q (MulAction.orbit Q x))
    (i j : OrbitBlock Q (MulAction.orbit Q x)) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (blockSpace Q (MulAction.orbit Q x) i) = 3 := by
  let Δ := MulAction.orbit Q x
  let B := blockGroup Q Δ i
  let D := blockGroup Q Δ j
  have hBQ : B ≤ Q := generated_le Q i.val
  have hDQ : D ≤ Q := generated_le Q j.val
  obtain ⟨e,_,_,_⟩ := core_free_block_models hsource hcore hf hd
  obtain ⟨⟨hlow,_⟩,C,hC,hCq⟩ := sqtk_core_free_block_lifts hH Q q hq x hsource hcore hf hd hl i
  by_contra hdim
  have hr : 2 ≤ primeRank 3 B := by
    rw [primeRank_equiv 3 (e i)]
    exact block_rank_two (by omega)
  have hrC : 2 ≤ primeRank 3 C := by
    apply rank_two_lifts (q.subgroupMap C) (q.subgroupMap_surjective C)
    rw [hCq,primeRank_equiv 3 (subgroupOfEquivOfLe hBQ)]
    exact hr
  let : C.Normal := Chapter1.Section02.rank_two_component_normal hH hC hrC
  have hnormal : (B.subgroupOf Q).Normal := by
    rw [←hCq]
    exact Subgroup.Normal.map inferInstance q hq
  obtain ⟨g,hg,he⟩ := hd.groups_conjugate i j
  have hBD : B = D := by
    have hm : B.map (MulAut.conj g).toMonoidHom = B := by
      apply le_antisymm
      · rintro y ⟨b,hb,rfl⟩
        exact hnormal.conj_mem (⟨b,hBQ hb⟩ : Q) hb (⟨g,hg⟩ : Q)
      · intro b hb
        have hmem : g⁻¹*b*g ∈ B :=
          hnormal.conj_mem (⟨b,hBQ hb⟩ : Q) hb (⟨g,hg⟩ : Q)⁻¹
        refine ⟨g⁻¹*b*g,hmem,?_⟩
        simp [mul_assoc]
    exact hm.symm.trans he
  have hdis := hd.group_independent.pairwiseDisjoint hij
  change Disjoint B D at hdis
  rw [←hBD] at hdis
  have hbot : B = ⊥ := disjoint_self.mp hdis
  have hr0 : primeRank 3 B ≤ 1 := by
    have hh := primeRank_le_card (G := B) 3
    simpa only [hbot,card_bot] using hh
  omega

end CFSG.Quasithin.ChapterG.Section03
