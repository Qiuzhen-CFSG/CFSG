module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement.MatrixBlocks.RootCommutators
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion.BlockStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Factors.Transport
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom

/-!
# No A₃ blocks in direct powers of nonbinary symplectic Borels

Subnormality and two-perfection put [U^k,X] inside the image of the
intrinsic block layer U(X). The genuine alternating-three module has
|U(X)| = 4 and exponent two. In any coordinate, a nonunipotent element
whose unipotent commutators have square one would inject the central
root plane F² into the image of U(X). Since |F| ≥ 4, this is impossible.
Thus X lies in the unipotent direct power, and two-perfection makes X
trivial, contrary to its nonzero block module.

The argument works for every exponent n > 1, including n = 2. The final
embedding interface retains the even-degree hypothesis supplied by the
parent reduction and subnormality in the entire direct power. No ambient
E.6 hypotheses, no-block premise or Sylow-center rank bound are used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12–13, printed pp.123–125; E.6.8, printed p.248 (PDF p.259).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry
open CFSG.Quasithin.ChapterC
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement.MatrixBlocks

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem unipotent_power_isPGroup {n : ℕ} (hF : Nat.card F = 2^n) (k : ℕ) :
    IsPGroup 2 (pi Set.univ (fun _ : Fin k => unipotent.subgroupOf (borel (F := F)))) := by
  let R := (unipotent (F := F)).subgroupOf borel
  have hp : IsPGroup 2 R := (isPGroup_unipotent hF).comap_subtype
  obtain ⟨m, hm⟩ := hp.exists_card_dvd_pow
  intro x
  refine ⟨m, Subtype.ext (funext fun i => ?_)⟩
  exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
    ((_root_.orderOf_dvd_natCard (⟨x.val i, x.property i (Set.mem_univ i)⟩ : R)).trans hm))

/-- There is no genuine alternating-three block subnormal in a finite power of the matrix Borel. -/
theorem no_alternatingThree_subnormal_power {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (k : ℕ)
    (X : Subgroup (Fin k → borel (F := F))) (hs : X.IsSubnormal) :
    ¬ IsAlternatingBlock X 3 := by
  intro hx
  let R := (unipotent (F := F)).subgroupOf borel
  let P : Subgroup (Fin k → borel (F := F)) := pi Set.univ (fun _ => R)
  let : P.Normal := ⟨by
    intro x hx y i _
    exact (inferInstance : R.Normal).conj_mem _ (hx i (Set.mem_univ i)) _⟩
  have hpP : IsPGroup 2 P := unipotent_power_isPGroup hF k
  let C := (blockU X).map X.subtype
  have hc : ⁅P, X⁆ ≤ C :=
    commutator_le_core_commutator_of_isSubnormal X P hs hx.2.1.twoPerfect hpP
      le_normalizer_of_normal
  let _ := hx.2.1.elementary
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.map_subtype
  have hcardC : Nat.card C = 4 := by
    rw [card_map_of_injective X.subtype_injective]
    exact LinearThree.BorelPlacement.Containment.A3Exclusion.alternatingThree_blockU_card hx
  have hXP : X ≤ P := by
    intro x hxx i _
    let ev := Pi.evalMonoidHom (fun _ : Fin k => borel (F := F)) i
    let Ci := C.map ev
    have hcCi : Nat.card Ci ≤ 4 := by
      have hh := Nat.card_le_card_of_surjective (ev.subgroupMap C) (ev.subgroupMap_surjective C)
      simpa only [hcardC] using hh
    have hmem (r : unipotent (F := F)) :
        ⁅(⟨r.val, unipotent_le_borel r.property⟩ : borel (F := F)), x i⁆ ∈ Ci := by
      let rb : borel (F := F) := ⟨r.val, unipotent_le_borel r.property⟩
      have hr : (fun _ : Fin k => rb) ∈ P := fun _ _ => r.property
      exact mem_map_of_mem ev (hc (commutator_mem_commutator hr hxx))
    have hsquare (r : unipotent (F := F)) : ⁅r.val, (x i).val⁆ ^ 2 = 1 := by
      let _ : IsElementaryAbelian 2 Ci := IsElementaryAbelian.map ev
      have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (hmem r)
      exact congrArg Subtype.val hh
    change (x i).val ∈ unipotent
    by_contra hxi
    have hinj := RootCommutators.central_commutator_injective (x i) hsquare hxi
    let j : F × F → Ci := fun st =>
      ⟨⁅(⟨(theta st.1 st.2).val, unipotent_le_borel (theta st.1 st.2).property⟩ : borel (F := F)), x i⁆,
        hmem (theta st.1 st.2)⟩
    have hj : Function.Injective j := by
      intro a b hab
      apply hinj
      exact congrArg (fun z : Ci => z.val.val) hab
    have hjc := Nat.card_le_card_of_injective j hj
    rw [Nat.card_prod, hF] at hjc
    have hfour : 4 ≤ 2^n := by
      exact (by norm_num : 4 = 2^2).le.trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    have : 2^n * 2^n ≤ 4 := hjc.trans hcCi
    nlinarith
  let g : X →* P := inclusion hXP
  have hg := hx.2.1.twoPerfect.hom_eq_one_of_isPGroup hpP g
  have hone (x : X) : x = 1 := by
    apply inclusion_injective hXP
    exact (DFunLike.congr_fun hg x).trans (map_one g).symm
  apply hx.2.1.blockU_ne_bot
  exact eq_bot_iff.mpr (fun x _ => mem_bot.mpr (hone x))

/-- Intrinsic exclusion, retaining subnormality in the full direct power. -/
theorem no_alternatingThree_embedding {X : Type*} [Group X]
    {n : ℕ} (hn : 1 < n) (_heven : Even n) (hF : Nat.card F = 2^n)
    (hx : IsAlternatingBlock X 3) {k : ℕ}
    (f : X →* (Fin k → borel (F := F))) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) : False := by
  exact no_alternatingThree_subnormal_power hn hF k f.range hs
    (hx.of_mulEquiv (MonoidHom.ofInjective hf))

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement.MatrixBlocks
