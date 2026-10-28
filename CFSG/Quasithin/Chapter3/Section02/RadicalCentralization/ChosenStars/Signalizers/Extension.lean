module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Signalizers.Models
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.Orders
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Extension

/-!
# Two-signalizers through the actual linear-three central cover

For a normal (S)L₃(p) subgroup K with two-group ambient quotient, descend
the conjugation action to K/Z(K). Perfectness detects its kernel and the
scalar-center order shows that the defining subgroup keeps order p².
The projective automorphism theorem kills the image of the two-signalizer.
The remaining centralizer is nilpotent: its map to H/K has central kernel.
Its two-subgroups therefore lie in O₂(H). In the core-free quotient they
vanish, with no faithful-action or scalar-kernel premise left over.

Source: Aschbacher--Smith, proof of 1.3.8, printed p.513.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars.Signalizers
open Chapter1.XiEmbedding
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
variable {p : ℕ} [Fact p.Prime]

private theorem linearThree_cover_data {Q : Type*} [Group Q] [Finite Q]
    (hm : LinearThreeModel p Q) :
    Group.IsPerfect Q ∧ Nat.card (center Q) ∣ 3 ∧
      Nonempty ((Q ⧸ center Q) ≃* PSL(3,ZMod p)) := by
  have hproj := linearThree_center_model hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hproj
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using hF)
  refine ⟨?_,?_,⟨e.trans (Atlas.fieldEquivPSL 3 eF)⟩⟩
  · rcases hm with ⟨E,_,_,_,⟨f⟩⟩ | ⟨E,_,_,_,⟨f⟩⟩
    · let : Group.IsPerfect SL(3,E) := Atlas.sl_perfect 3 (by decide)
      exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
    · let : Group.IsPerfect PSL(3,E) := Atlas.psl_perfect 3 (by decide)
      exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  · rcases hm with ⟨E,_,_,_,⟨f⟩⟩ | ⟨E,_,_,_,⟨f⟩⟩
    · rw [Nat.card_congr (centerCongr f).toEquiv]
      exact Matrix.SL3.card_center_dvd_three E
    · let : Group.IsPerfect SL(3,E) := Atlas.sl_perfect 3 (by decide)
      rw [Nat.card_congr (centerCongr f).toEquiv,
        Group.IsPerfect.center_quotient_center_eq_bot SL(3,E),card_bot]
      exact one_dvd _

/-- A two-subgroup centralizing a normal factor with two-group quotient lies
in the ambient two-core, including factors with nontrivial odd center. -/
theorem centralizing_two_le_core {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (hq : IsPGroup 2 (H ⧸ K))
    (S : Subgroup H) (hS : IsPGroup 2 S) (hc : S ≤ centralizer (K : Set H)) :
    S ≤ pCore 2 H := by
  let C := centralizer (K : Set H)
  let f := (QuotientGroup.mk' K).comp C.subtype
  have hker : f.ker ≤ center C := by
    intro x hx
    have hxK : (x : H) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (y.property x hxK).symm
  let : Group.IsNilpotent (H ⧸ K) := hq.isNilpotent
  let : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨U,hU⟩ := hS.comap_subtype.exists_le_sylow (G := C)
  have hmap := (map_mono (f := C.subtype) hU).trans
    (U.map_le_pCore (inferInstance : C.Normal) inferInstance 2)
  change (S.subgroupOf C).map C.subtype ≤ pCore 2 H at hmap
  rw [map_subgroupOf_eq_of_le (show S ≤ C from hc)] at hmap
  exact hmap

/-- The model two-signalizer theorem in the literal normal extension. Its
conjugation kernel and scalar center are both discharged. -/
theorem extension_two_eq_bot {H : Type*} [Group H] [Finite H]
    (hp : 3 < p) (K : Subgroup H) [K.Normal]
    (hm : LinearThreeModel p K) (hq : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥)
    (P : Subgroup K) (hP : IsPGroup p P) (hc : Nat.card P = p ^ 2)
    (S : Subgroup H) (hS : IsPGroup 2 S)
    (hn : P.map K.subtype ≤ normalizer (S : Set H)) : S = ⊥ := by
  obtain ⟨hperfect,hZ,⟨e⟩⟩ := linearThree_cover_data hm
  let := hperfect
  let π := QuotientGroup.mk' (center K)
  let g := e.toMonoidHom.comp π
  let f := (MulAut.centralQuotientAction e).comp (MulAut.conjNormal : H →* MulAut K)
  have hk : Nat.Coprime p (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hp)).of_dvd_right hZ
  have hi := e.injective.comp (injective_comp_subtype_of_coprime_ker π hk P hP)
  have hcard : Nat.card (P.map g) = p ^ 2 := by
    let eP : P ≃* P.map g := MulEquiv.ofBijective (g.subgroupMap P)
      ⟨fun x y h => hi (congrArg Subtype.val h),g.subgroupMap_surjective P⟩
    exact (Nat.card_congr eP.toEquiv.symm).trans hc
  have hmap : (P.map K.subtype).map f =
      (P.map g).map (MulAut.conj : PSL(3,ZMod p) →* MulAut PSL(3,ZMod p)) := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    ext x y
    have he : (MulAut.conjNormal : H →* MulAut K) (x : H) = MulAut.conj x := by
      ext z
      rfl
    change MulAut.centralQuotientAction e (MulAut.conjNormal (x : H)) y = _
    rw [he,MulAut.centralQuotientAction_conj]
    rfl
  have hbot : S.map f = ⊥ := automorphism_normalized_two_eq_bot hp (P.map g)
    (hP.map g) hcard (S.map f) (hS.map f) (by
      rw [← hmap]
      exact (map_mono hn).trans (S.le_normalizer_map f))
  have hSC : S ≤ centralizer (K : Set H) := by
    have hSf := (map_eq_bot_iff S).mp hbot
    intro s hs
    have he : (MulAut.conjNormal : H →* MulAut K) s = 1 := by
      apply MulAut.centralQuotientAction_injective e
      exact (hSf hs).trans (map_one _).symm
    change s ∈ (MulAut.conjNormal : H →* MulAut K).ker at he
    rwa [MulAut.conjNormal_ker_eq_centralizer] at he
  exact le_bot_iff.mp ((centralizing_two_le_core K hq S hS hSC).trans hcore.le)
end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars.Signalizers
