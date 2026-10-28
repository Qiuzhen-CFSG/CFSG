module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarSplitting
public import Theory.GroupTheory.SylowThreeNormalizerSection
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original scalar cubic gives the Frattini complements

The cubic complement is Sylow in the literal two-residual X. Its Frattini
factorization therefore applies to both KT and the original T, since both
normalize X and U. The fixed-free scalar action makes the actual cubic
normalizer disjoint from U. No identification of the whole core with U is used.

Source: the first paragraph of Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- One actual scalar cubic simultaneously complements the original chosen
module in KT and T through their literal normalizers of that cubic. -/
theorem original_tripleSix_central_closure_scalar_frattini
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let X := tripleSixScalarResidual K
    let M := K ⊔ (T : Subgroup G)
    ∃ Y : Subgroup G, Y ≤ X ∧ Nat.card Y = 3 ∧ X = U ⊔ Y ∧
      M = U ⊔ (M ⊓ normalizer (Y : Set G)) ∧
      (T : Subgroup G) = U ⊔ ((T : Subgroup G) ⊓ normalizer (Y : Set G)) ∧
      Disjoint U (normalizer (Y : Set G)) := by
  let X := tripleSixScalarResidual K
  let M := K ⊔ (T : Subgroup G)
  obtain ⟨_,Y,hYX,hYcard,hXY,hd⟩ :=
    original_tripleSix_central_closure_scalar_splitting h structural D a z hz hzT hnot houter
  change Y ≤ X at hYX
  change X=U ⊔ Y at hXY
  have hXK : X ≤ K := map_subtype_le _
  have hXU : X ≤ normalizer (U : Set G) := hXK.trans D.normalizes
  have hMU : M ≤ normalizer (U : Set G) :=
    sup_le D.normalizes ((structural K h).2.2 U D).1
  have hMX : M ≤ normalizer (X : Set G) :=
    (sup_le K.le_normalizer D.sylow_normalizes_component).trans
      (tripleSixScalarResidual_normalizer_at K)
  have hXcard : Nat.card X=Nat.card U*3 := by
    rw [hXY,card_sup_eq_mul_of_normalizes_of_disjoint U Y (hYX.trans hXU) hd,hYcard]
  let C := Y.subgroupOf X
  have hCcard : Nat.card C=3 := (Nat.card_congr (subgroupOfEquivOfLe hYX).toEquiv).trans hYcard
  have hi : C.index=Nat.card U := by
    have hh := C.card_mul_index
    rw [hCcard,hXcard] at hh
    omega
  have hn : ¬ 3 ∣ C.index := by
    rw [hi]
    obtain ⟨n,hn⟩ := D.elementary.isPGroup.exists_card_eq
    rw [hn]
    exact fun hh => (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hh)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 X := (IsPGroup.of_card (p:=3) (n:=1) (by simpa using hCcard)).toSylow hn
  have hP : (P : Subgroup X).map X.subtype=Y := map_subgroupOf_eq_of_le hYX
  have hgen : (P : Subgroup X).map X.subtype ⊔ U=X := by
    rw [hP,hXY,sup_comm]
  have hfactor (A : Subgroup G) (hUA : U ≤ A) (hAM : A ≤ M) :
      A=U ⊔ (A ⊓ normalizer (Y : Set G)) := by
    apply le_antisymm ?_ (sup_le hUA inf_le_left)
    intro b hb
    obtain ⟨n,hn,r,hr,he⟩ := SylowThreeNormalizer.normalizer_factorization
      X U A P hgen hUA hXU (hAM.trans hMU) (hAM.trans hMX) ⟨b,hb⟩
    rw [hP] at hn
    have hm : n*r ∈ U ⊔ (A ⊓ normalizer (Y : Set G)) :=
      (U ⊔ (A ⊓ normalizer (Y : Set G))).mul_mem
        (mem_sup_right hn) (mem_sup_left hr)
    simpa only [he] using hm
  have hfix : U ⊓ centralizer (Y : Set G)=⊥ := by
    apply bot_unique
    apply le_trans _ (tripleSixScalarResidual_fixed_eq_bot D a).le
    refine le_inf inf_le_left ?_
    apply le_centralizer_iff.mp
    change X ≤ centralizer (U ⊓ centralizer (Y : Set G) : Set G)
    rw [hXY]
    let := D.elementary
    exact sup_le ((Subgroup.le_centralizer U).trans (centralizer_le inf_le_left))
      (le_centralizer_iff.mp inf_le_right)
  refine ⟨Y,hYX,hYcard,hXY,hfactor M (D.le_component.trans le_sup_left) le_rfl,
    hfactor T D.le_sylow le_sup_right,disjoint_iff.mpr ?_⟩
  exact (SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf U Y
    (hYX.trans hXU) hd).trans hfix

end CFSG.Quasithin.Chapter12.Section07
