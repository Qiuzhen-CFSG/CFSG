module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.AmbientCubic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.FixedPair

/-!
# The original fixed-pair failure produces an ambient cubic block

The single pair in the original Baum(T) forces the A₃ residual block in
the constructed C.1.17 member K. The marking is transported to the actual
Baumann subgroup of M; its block then extends subnormally to M using the
proved source geometry. The same residual R retains R=[R,J(T)] and
M=RT, the latter following from the actual Sylow supplement in K.

The raw empty-family consumer keeps precisely the full earlier A/C, 3.1.1,
B.2.16 and universal C.1.18 pair. The selected block, its subnormality,
Thompson movement and generation are conclusions, not input certificates.
Source: Aschbacher--Smith 15.4.7 and C.1.26--28, pp.1158,132--134.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure FamilySource.ThompsonSource ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem member_native_setup {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    let S := T.subtype h.sylow_le
    SectionTwo.Hypotheses M ∧
    pCore 2 M = (S : Subgroup M) ⊓ centralizer (SectionTwo.vSubgroup S : Set M) ∧
    (¬ SectionTwo.vSubgroup S ≤ centralizer (elementaryAbelianMaxJ (S : Subgroup M) : Set M)) ∧
    IsUniqueMaximalContaining (S : Subgroup M) ⊤ ∧
    centralizer (omegaOneCenterAmbient (S : Subgroup M) : Set M) = S := by
  let S := T.subtype h.sylow_le
  have hmin := member_minimal_parabolic h hZ
  have hh := ChapterC.RankOne.Solvable.sectionTwoHypotheses_of_proper_subgroup
    h.solvable (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
    (S : Subgroup M) hmin.1.1
  have hv : SectionTwo.vSubgroup S = internalModule T M := closure_eq_internalModule T M h.sylow_le
  have hcore : pCore 2 M = (S : Subgroup M) ⊓ centralizer (SectionTwo.vSubgroup S : Set M) := by
    rw [hv,internal_centralizer T M h.sylow_le h.center_centralizer]
    exact (inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal S)).symm
  have hnot : ¬ SectionTwo.vSubgroup S ≤ centralizer
      (elementaryAbelianMaxJ (S : Subgroup M) : Set M) := by
    rw [hv]
    intro hc
    apply h.thompson_moved
    have hm := map_mono (f := M.subtype) (le_centralizer_iff.mp hc)
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,map_centralizer_subtype] at hm
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hm.trans inf_le_right))
  have hu : IsUniqueMaximalContaining (S : Subgroup M) ⊤ := by
    obtain ⟨⟨N,hN,huniq⟩,_⟩ := ChapterB.isMinimalParabolicOver_top_iff S |>.mp hmin
    exact (uniqueMaximalContaining_top_iff _).mpr
      ⟨N,hN.1,hN.2,fun N' ha hb => huniq N' ⟨ha,hb⟩⟩
  have hc : centralizer (omegaOneCenterAmbient (S : Subgroup M) : Set M) = S := by
    have hΩM : omegaOneCenterAmbient (T : Subgroup G) ≤ M :=
      fun _ hz => h.sylow_le ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
    apply map_injective M.subtype_injective
    change (centralizer (omegaOneCenterAmbient (T.subtype h.sylow_le : Subgroup M) : Set M)).map
      M.subtype = ((T.subtype h.sylow_le : Subgroup M)).map M.subtype
    rw [restricted_omega, map_centralizer_subtype,map_subgroupOf_eq_of_le hΩM,
      h.center_centralizer,Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,
      inf_eq_right.mpr h.sylow_le]
  exact ⟨hh,hcore,hnot,hu,hc⟩

/-- The original local member gives its actual ambient residual block and generation. -/
theorem member_marked_ambient_cubic_block {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup M) (e : ChapterB.baumann (T : Subgroup G) →* K)
    (hc : InLocalClass e) (he : ∀ b, ((e b : M) : G) = (b : G))
    (hgen : K ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤)
    (hb : ChapterC.IsBlock (pResidual 2 K))
    (ha : ChapterC.IsAlternatingBlock (pResidual 2 K) 3) :
    let R := (pResidual 2 K).map K.subtype
    ChapterC.IsBlock R ∧ ChapterC.IsAlternatingBlock R 3 ∧
    R = ⁅R,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆ ∧
    R ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ := by
  let S := T.subtype h.sylow_le
  let B := ChapterB.baumann (S : Subgroup M)
  let a : B ≃* ChapterB.baumann (T : Subgroup G) :=
    (B.equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr (restricted_baumann_map T M h.sylow_le))
  let f := e.comp a.toMonoidHom
  have hfval (b : B) : (f b : M) = (b : M) := by
    apply M.subtype_injective
    exact he (a b)
  have hBK : B ≤ K := by
    intro b hb
    have hh := (f ⟨b,hb⟩).property
    rwa [hfval] at hh
  have hf : f = inclusion hBK := by
    ext b
    exact congrArg Subtype.val (hfval b)
  have hclass : InLocalClass (inclusion hBK) := by
    rw [←hf]
    exact hc.precomp_equiv a
  obtain ⟨hh,hcore,hnot,hu,hC⟩ := member_native_setup h hZ
  obtain ⟨hb',ha',hJ⟩ := selected_ambient_cubic_block hh S hcore hnot hu hC K hBK hclass hb ha
  refine ⟨hb',ha',hJ,?_⟩
  obtain ⟨P,hP,_⟩ := hclass.sylow
  have hPB : (P : Subgroup K).map K.subtype = B := by
    rw [←hP,MonoidHom.range_eq_map,map_map]
    change (⊤ : Subgroup B).map B.subtype = B
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hRK := congrArg (map K.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,hPB,←MonoidHom.range_eq_map,range_subtype] at hRK
  calc
    (pResidual 2 K).map K.subtype ⊔ (S : Subgroup M) =
        ((pResidual 2 K).map K.subtype ⊔ B) ⊔ (S : Subgroup M) := by
      rw [sup_assoc,sup_eq_right.mpr (show B ≤ (S : Subgroup M) from inf_le_left)]
    _ = ⊤ := by rw [hRK]; exact hgen

/-- The failure of the one universal pair yields an A₃ block subnormal in the original M. -/
theorem member_fixed_pair_ambient_block {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u})
    (hfail : ¬ M ≤ normalizer (D.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G)) :
    ∃ K : Subgroup M,
      let R := (pResidual 2 K).map K.subtype
      ChapterC.IsBlock R ∧ ChapterC.IsAlternatingBlock R 3 ∧
      R = ⁅R,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆ ∧
      R ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ := by
  obtain ⟨K,e,hc,he,hgen,hb,ha⟩ := member_fixed_pair_alternatingThree h hZ D hD hfail
  exact ⟨K,member_marked_ambient_cubic_block h hZ K e hc he hgen hb ha⟩

/-- Original empty-family source application, with all block geometry constructed. -/
theorem source_fixed_pair_ambient_block
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    ∃ (M X : Subgroup G) (s : ℕ) (h : Input KnownSimple.IsKnownSimple T M X s)
      (K : Subgroup M),
      let R := (pResidual 2 K).map K.subtype
      ChapterC.IsBlock R ∧ ChapterC.IsAlternatingBlock R 3 ∧
      R = ⁅R,elementaryAbelianMaxJ (T.subtype h.sylow_le : Subgroup M)⁆ ∧
      R ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ := by
  obtain ⟨M,X,s,h,K,e,hc,he,hgen,hb,ha⟩ :=
    source_fixed_pair_local_block hA hC h311 hB hG T hempty hmany hZ D hD
  exact ⟨M,X,s,h,K,member_marked_ambient_cubic_block h hZ K e hc he hgen hb ha⟩
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
