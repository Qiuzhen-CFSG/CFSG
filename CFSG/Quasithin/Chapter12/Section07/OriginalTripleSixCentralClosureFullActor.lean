module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOneBlock
public import CFSG.Quasithin.ChapterG.Section03.SpanningOneBlockActor
public import CFSG.Quasithin.ChapterG.Section03.RootSeedNormalClosure

/-!
# The full original inner central-closure actor

The unique spanning block is the whole quotient module, so its full linear
restriction identifies the original image with the whole binary linear group.
The nontrivial original U-image normally generates that actor. The literal
R=<U^C_G(z)> is normalized by H and contains U, hence its image is also the
whole actor. No equality between the original C_G(z)- and H-closures is used.

Source: Aschbacher--Smith12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The same original representation is the full binary linear actor in
dimension three, four or five, and the literal original R maps onto it. -/
theorem original_tripleSix_central_closure_full_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    let Z := zpowers (z:G)
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧ pCore 2 φ.range = ⊥ ∧
          (Nat.card ((U.subgroupOf H).map φ) = 4 ∨ Nat.card ((U.subgroupOf H).map φ) = 16) ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            (∀ g ∈ (U.subgroupOf H).map φ, g x = x) ∧
            (∀ g ∈ (U.subgroupOf H).map φ, ∀ y, g y-y ∈ BinaryTransvectionGroups.centerLine x) ∧
            ChapterG.Section03.FullAction φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.Decomposition φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.LocalStructure φ.range (MulAction.orbit φ.range x) ∧
            (∀ i : ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x),
              (3 ≤ Module.finrank (ZMod 2) (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i) ∧
                Module.finrank (ZMod 2) (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i) ≤ 5) ∧
              ∃ B : Subgroup H, B.IsCComponent ∧ B.map φ.rangeRestrict =
                (ChapterG.Section03.blockGroup φ.range (MulAction.orbit φ.range x) i).subgroupOf φ.range) ∧
            Nat.card (ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x)) = 1 ∧
            BinaryTransvectionGroups.generated φ.range (MulAction.orbit φ.range x) = ⊤ ∧
            φ.range = ⊤ ∧ (R.subgroupOf H).map φ = φ.range ∧
            (Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 3 ∨
              Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 4 ∨
              Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 5) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_one_block
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,hcard,x,hx,hpoint,horbit,hfix,hmove,hfull,hdecomp,hlocal,hlifts,hone⟩ := hrest
  let := he
  have hHC : H ≤ C :=
    (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).1
  have hspan : Submodule.span (ZMod 2) (MulAction.orbit φ.range x) = ⊤ := by
    have heq : MulAction.orbit φ.range x = Set.range (fun g : φ.range => g.val x) := by
      ext y
      exact MulAction.mem_orbit_iff
    rwa [heq]
  obtain ⟨hspaces,hgenerated,hwhole⟩ :=
    ChapterG.Section03.spanning_one_block_actor hfull hdecomp hspan hone
  have hdim : Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 3 ∨
      Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 4 ∨
      Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 5 := by
    obtain ⟨i,_⟩ := Nat.card_eq_one_iff_exists.mp hone
    have hh := (hlifts i).1
    rw [hspaces i,finrank_top] at hh
    change 3 ≤ Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) ∧
      Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) ≤ 5 at hh
    omega
  let A := (U.subgroupOf H).map φ
  have hAR : A ≤ BinaryTransvectionGroups.rootGroup φ.range x := by
    intro g hg
    refine ⟨?_,?_,hmove g hg⟩
    · obtain ⟨u,_,rfl⟩ := hg
      exact ⟨u,rfl⟩
    · intro v hv
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,hfix g hg]
  have hAne : A ≠ ⊥ := by
    intro hb
    change Nat.card A = 4 ∨ Nat.card A = 16 at hcard
    rw [hb,card_bot] at hcard
    omega
  have hroot := ChapterG.Section03.root_seed_normal_closure x hfull hdecomp hlocal
    hspan A hAR hAne
  have hRN : (R.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (hHC.trans (le_normalizer_conjugateSpanBy U C))
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hwhole
  let : ((R.subgroupOf H).map φ).Normal := Normal.map hRN φ hsurj
  have hle : conjugateSpanBy A φ.range ≤ (R.subgroupOf H).map φ :=
    conjugateSpanBy_le (map_mono (subgroupOf_mono H (le_conjugateSpanBy U C)))
      le_normalizer_of_normal
  have hR : (R.subgroupOf H).map φ = φ.range := by
    rw [hroot,hgenerated] at hle
    exact (top_unique hle).trans hwhole.symm
  exact ⟨hHW,hZN,he,φ,hformula,hker,hcore,hcard,x,hx,hpoint,horbit,hfix,hmove,
    hfull,hdecomp,hlocal,hlifts,hone,hgenerated,hwhole,hR,hdim⟩

end CFSG.Quasithin.Chapter12.Section07
