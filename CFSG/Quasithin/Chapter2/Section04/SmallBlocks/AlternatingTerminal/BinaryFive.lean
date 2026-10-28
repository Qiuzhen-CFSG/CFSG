module
public import Theory.SpecificGroups.BinaryLinear.FiveElementaryNormalizer
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.BinaryFourQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.Chapter1.Section01
/-!
# The actual binary-five normalizer escape

For an alternating-five block in GL₅(2), its elementary commutator layer
has an endpoint-parabolic normalizer. After carrying this actual normalizer
to a point stabilizer, the layer is the whole point radical. Centralization
of the layer by the block's core kills that core in the GL₄(2) quotient.
The full-Sylow quotient obstruction excludes locality in this normalizer.

Source: Aschbacher–Smith 2.4.25, printed p.543. The normalizer is canonical
in the original block, so ambient normalization is preserved by transport.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveElementaryNormalizer
open Theory.LinearAlgebra BinaryFivePointStabilizer
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))
    (matrixEquivLinear 5).toEquiv

theorem point_not_local (v : Space 5) (hv : v ≠ 0)
    (A : Subgroup (stabilizer v)) (hA : ChapterC.IsAlternatingBlock A 5)
    (hU : ((ChapterC.blockU A).map A.subtype).map (stabilizer v).subtype =
      (kernel v).map (stabilizer v).subtype)
    (S : Sylow 2 (stabilizer v)) :
    A ∉ ChapterA.Section03.localCComponents S := by
  let q : stabilizer v →* PSL(4, ZMod 2) :=
    (projectiveEquivLinear (by decide : 0 < 4)).symm.toMonoidHom.comp (pointQuotient v hv)
  have hq : Function.Surjective q :=
    (projectiveEquivLinear (by decide : 0 < 4)).symm.surjective.comp
      (pointQuotient_surjective v hv)
  have hk : q.ker = kernel v := by
    ext a
    change (projectiveEquivLinear (by decide : 0 < 4)).symm (pointQuotient v hv a) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    change a ∈ (pointQuotient v hv).ker ↔ _
    rw [pointQuotient_ker]
  apply not_local_of_binary_four_quotient q hq (by
    rw [hk]; exact IsElementaryAbelian.isPGroup 2 _) A hA ?_ S
  have hline0 : Submodule.span (ZMod 2) {v} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hv
  have hlinet : Submodule.span (ZMod 2) {v} ≠ ⊤ := by
    intro he
    have hd := finrank_span_singleton (K := ZMod 2) hv
    rw [he,finrank_top] at hd
    norm_num [Space] at hd
  have hc : centralizer (((ChapterC.blockU A).map A.subtype).map
      (stabilizer v).subtype : Set (LinearGroup 5)) ≤
      (kernel v).map (stabilizer v).subtype := by
    rw [hU,point_kernel_map]
    exact centralizer_radical_le hline0 hlinet
  rw [hk]
  intro a ha
  have ham : a.val ∈ (kernel v).map (stabilizer v).subtype := by
    apply hc
    rcases ha with ⟨b,hb,rfl⟩
    rintro u ⟨w,⟨z,hz,rfl⟩,rfl⟩
    exact congrArg (fun z : A => z.val.val) (hA.2.1.core_centralizes_blockU hb z hz)
  rcases ham with ⟨b,hb,hba⟩
  have he : b = a := Subtype.ext hba
  exact he ▸ hb
end CFSG.Quasithin.Chapter2.AlternatingTerminal
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveElementaryNormalizer
open Theory.LinearAlgebra BinaryFivePointStabilizer
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))
    (matrixEquivLinear 5).toEquiv

private theorem blockU_image {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    (ChapterC.blockU (A.map f)).map (A.map f).subtype =
      ((ChapterC.blockU A).map A.subtype).map f := by
  let e := A.equivMapOfInjective f hf
  rw [← ChapterC.RankOne.Solvable.blockU_map_equiv e,map_map,map_map]
  rfl

private theorem blockU_subgroupOf {G : Type*} [Group G]
    {A N : Subgroup G} (hAN : A ≤ N) :
    ((ChapterC.blockU (A.subgroupOf N)).map (A.subgroupOf N).subtype).map N.subtype =
      (ChapterC.blockU A).map A.subtype := by
  let e := subgroupOfEquivOfLe hAN
  rw [← ChapterC.RankOne.Solvable.blockU_map_equiv e,map_map,map_map]
  rfl

theorem binary_five_normalizer_obstruction
    (A : Subgroup (LinearGroup 5)) (hA : ChapterC.IsAlternatingBlock A 5)
    (hc : Nat.card ((ChapterC.blockU A).map A.subtype) = 16) :
    let N := normalizer ((ChapterC.blockU A).map A.subtype : Set (LinearGroup 5))
    N ∈ Chapter1.He (LinearGroup 5) ∧ A ≤ N ∧
      ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  let U := (ChapterC.blockU A).map A.subtype
  let N := normalizer (U : Set (LinearGroup 5))
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  have hU : IsPGroup 2 U := (pCore_isPGroup.to_le ChapterC.blockU_le_core).map A.subtype
  have h5 : 5 ∣ Nat.card N := by
    obtain ⟨a⟩ := hA.2.2.quotient_iso
    have hcard : Nat.card (A ⧸ pCore 2 A) = 60 := by
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]; norm_num
    apply dvd_trans (b := Nat.card A) _ (card_dvd_of_le hAN)
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),hcard]
    exact dvd_mul_of_dvd_left (by decide : 5 ∣ 60) _
  obtain ⟨a,v,hv,hNP⟩ : ∃ a : MulAut (LinearGroup 5), ∃ v : Space 5,
      v ≠ 0 ∧ N.map a.toMonoidHom = stabilizer v := by
    rcases normalizer_isEndParabolic U hU hc h5 with ⟨v,hv,he⟩ | ⟨f,hf,he⟩
    · refine ⟨1,v,hv,?_⟩
      change N.map (MonoidHom.id _) = _
      rw [map_id]
      exact
        he.trans (FiveFlagGeometry.pointParabolic_eq_stabilizer hv)
    · obtain ⟨v,hv,hvP⟩ := FiveParabolicStabilizer.hyperplane_map_graph hf
      exact ⟨graphLinear 5,v,hv,by change (normalizer (U : Set (LinearGroup 5))).map _ = _; rw [he,hvP,FiveFlagGeometry.pointParabolic_eq_stabilizer hv]⟩
  let e : N ≃* stabilizer v := (N.equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr hNP)
  have hline0 : Submodule.span (ZMod 2) {v} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hv
  have hlinet : Submodule.span (ZMod 2) {v} ≠ ⊤ := by
    intro he
    have hd := finrank_span_singleton (K := ZMod 2) hv
    rw [he,finrank_top] at hd
    norm_num [Space] at hd
  have hP : centralizer (pCore 2 (stabilizer v) : Set (stabilizer v)) ≤
      pCore 2 (stabilizer v) := by
    have hh := centralizer_parabolic_twoCore_le hline0 hlinet
    rwa [FiveFlagGeometry.pointParabolic_eq_stabilizer hv] at hh
  refine ⟨Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hP),hAN,?_⟩
  intro Q hlocal
  let B := (A.subgroupOf N).map e.toMonoidHom
  let eA := (subgroupOfEquivOfLe hAN).symm.trans
    ((A.subgroupOf N).equivMapOfInjective e.toMonoidHom e.injective)
  have hB : ChapterC.IsAlternatingBlock B 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv eA hA
  have hBU : ((ChapterC.blockU B).map B.subtype).map (stabilizer v).subtype =
      U.map a.toMonoidHom := by
    rw [blockU_image _ _ e.injective, map_map]
    have he : (stabilizer v).subtype.comp e.toMonoidHom = a.toMonoidHom.comp N.subtype := rfl
    rw [he,←map_map,blockU_subgroupOf hAN]
  have hUk := eq_point_kernel (U.map a.toMonoidHom) (hU.map _)
    ((card_map_of_injective a.injective).trans hc) (by
      rw [← map_equiv_normalizer_eq,card_map_of_injective a.injective]
      exact h5) v hv (by rw [← map_equiv_normalizer_eq]; exact hNP.le)
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  let : Group.IsSolvable e.toMonoidHom.ker := by rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  have hlocB := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom
  exact point_not_local v hv B hB (hBU.trans hUk)
    (Q.mapSurjective hes) hlocB
end CFSG.Quasithin.Chapter2.AlternatingTerminal
