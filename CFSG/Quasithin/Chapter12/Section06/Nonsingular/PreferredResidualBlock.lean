module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ResidualBlock
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredBlock

/-!
# Residual blocks at the unchanged preferred nonsingular point

The preferred point with nontrivial original C_V(L) already excludes an
ambient Sylow in its centralizer. The original index-four bound therefore
sharpens to |S:T_v| <= 2 for its containing local Sylow. Nonquasisimplicity,
normalizer escape and all local block premises are discharged at this
same point. The result retains the actual A6-block and V_v layer, the
relative K_v-block in G_v, and V_v <= [U,K_v] with U=R2(K_v S).

The full A7 model, canonical FF analysis, remaining HS/J4 exclusions,
splitting and fixed-space elimination remain. Earlier invariance/TI
retain producer qt-d-1222-source and final discharge owner qt-d-12634-source.
Neither 12.6.2 nor 12.6.23 is asserted. Source: Aschbacher--Smith,
12.6.13 and 12.6.16--18, printed pp.826--827, combined manuscript
of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A containing local Sylow has index at most two over T_v once the preferred
ambient-Sylow alternative has been excluded. -/
theorem nonsingular_sylow_index_le_two_of_no_ambient
    (T : Sylow 2 G) (v : G)
    (hi : (Tv T v).relIndex (T : Subgroup G) = 4)
    (hn : ∀ P : Sylow 2 G, (P : Subgroup G) ≤ Gv v → ¬ Tv T v ≤ (P : Subgroup G))
    (S : Sylow 2 (Gv v))
    (hTS : Tv T v ≤ (S : Subgroup (Gv v)).map (Gv v).subtype) :
    (Tv T v).relIndex ((S : Subgroup (Gv v)).map (Gv v).subtype) ≤ 2 := by
  let A := Tv T v
  let P := (S : Subgroup (Gv v)).map (Gv v).subtype
  have hP : IsPGroup 2 P := S.isPGroup'.map _
  have hb : A.relIndex P ≤ 4 := by
    simpa only [hi] using Tv_relIndex_le T v P hP hTS
  have hfour : A.relIndex P ≠ 4 := by
    intro he
    have h1 := (A.subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hTS).toEquiv] at h1
    change Nat.card A * A.relIndex P = Nat.card P at h1
    have h2 := (A.subgroupOf (T : Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ (T : Subgroup G) from inf_le_left)).toEquiv] at h2
    change Nat.card A * A.relIndex (T : Subgroup G) = Nat.card T at h2
    have hc : Nat.card P = Nat.card T := by
      rw [←h1,he,←h2]
      exact congrArg (Nat.card A * ·) hi.symm
    obtain ⟨P₀,hPP₀⟩ := hP.exists_le_sylow
    have heq : P = (P₀ : Subgroup G) := eq_of_le_of_card_ge hPP₀
      (by rw [hc,Nat.card_congr (P₀.equiv T).toEquiv])
    exact hn P₀ (heq ▸ map_subtype_le _) (heq ▸ hTS)
  have hthree : A.relIndex P ≠ 3 := by
    intro he
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    have hd : 3 ∣ 2 ^ n := hn ▸ (he ▸ A.relIndex_dvd_card P)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  change A.relIndex P ≤ 2
  omega

/-- The source-preferred point now constructs its A6-block and the actual
relative K_v-block, and places V_v in the canonical moved module. All block
premises are discharged; the original nontrivial C_V(L) is retained. -/
theorem SourceHypothesis.exists_preferred_nonsingular_residual_block_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ChapterC.IsAlternatingBlock L 8 ∧
      ChapterC.IsAlternatingBlock (Lv L (w : G)) 6 ∧
      (ChapterC.blockU (Lv L (w : G))).map (Lv L (w : G)).subtype = Vv L V (w : G) ∧
      ChapterC.IsShort (Kv (w : G)) ∧
      ChapterC.IsBlock ((Kv (w : G)).subgroupOf (Gv (w : G))) ∧
      ∃ S : Sylow 2 (Gv (w : G)),
        let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
        let J := Kv (w : G) ⊔ S₀
        Tv T (w : G) ≤ S₀ ∧ (Tv T (w : G)).relIndex S₀ ≤ 2 ∧
        Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (w : G) : Set G))
          (Gv (w : G) ⊓ normalizer (Lv L (w : G) : Set G)) ∧
        R L (Kv (w : G)) S₀ (w : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (w : G)) ∧
        generalizedFitting J = pCore 2 J ∧
        centralizer ((U (Kv (w : G)) S₀).subgroupOf J : Set J) = pCore 2 J ∧
        U (Kv (w : G)) S₀ = (reducedTwoSubgroup J).map J.subtype ∧
        Vv L V (w : G) ≤ ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hL,hno⟩ :=
    H.exists_preferred_nonsingular_no_ambient_sylow_of_fixed D hTV hTI hz v hv he
  have hnq : ¬ IsQuasisimple (Kv (w : G)) := fun h =>
    hz (H.nonsingular_quasisimple_fixed_eq_bot D w hw h hTV hi hnot)
  obtain ⟨_,hA,hU,hC,hCB,S,hTS,hN,hReq,hF,hker,hred,hm⟩ :=
    H.nonsingular_residual_block_of_not_quasisimple D w hw hTV hnq hs hi hnot
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hU,hC,hCB,
    S,hTS,nonsingular_sylow_index_le_two_of_no_ambient T (w : G) hi hno S hTS,
    hN,hReq,hF,hker,hred,hm⟩

end CFSG.Quasithin.Chapter12.Section06
