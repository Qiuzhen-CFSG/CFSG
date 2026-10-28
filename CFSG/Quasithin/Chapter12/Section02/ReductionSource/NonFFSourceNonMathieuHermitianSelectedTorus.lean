module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusRanks
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianTorus

/-!
# The selected torus on the original chosen Hermitian orbit

The selected pair in the original ambient group supplies a cyclic actor
of order 2^k−1. Its lift lies in N_G(L) ∩ I and has the same order in
I/O₂(I) and in the literal orbit automizer. It normalizes the selected
core actor's image, by normality of AB inside I and triviality of B's
action on V. No ambient normality of A is used.

The existing half-field descent supplies the original coordinates. The
proved rank identity and automizer rank bound make the selected fixed
space larger than 3n when k < 2n. The proved parabolic exponent then gives
k ∣ 4n whenever this torus preserves the marked parabolic. The earlier
E.2.14(9) source clause identifies its fixed subgroup with V ∩ V^i and
remains explicit.

Selection, its remaining fixed-space and parabolic inputs, the endpoint
k = 2n, and the field-four endgame remain obligations of the enclosing
Hermitian exclusion. These results do not assert that exclusion, and do
not remove n = 1.

Source: Aschbacher–Smith 8.2.2(8)–8.2.4, printed pp.715–716, and
E.2.14(9), printed p.227 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The torus and its original ambient lift, including normalization of the
literal selected core actor. -/
theorem sourceOrbit_hermitian_selected_torus
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S) (hk : 1 < k) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ∃ (y : ↥(normalizer (L : Set G) ⊓ I)) (x : Automizer D.sourceOrbit),
      x = (selectedActionMap (normalizer (L : Set G)) I D.sourceOrbit
        (s.normalizer_eq ▸ inf_le_right) y).val ∧
      orderOf y = 2^k-1 ∧
      orderOf (selectedStarMap (normalizer (L : Set G)) I y) = 2^k-1 ∧
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^k-1 ∧
      x ∈ normalizer (inducedAutomizer D.sourceOrbit A : Set (Automizer D.sourceOrbit)) := by
  obtain ⟨y,x,hxy,hy,hq,hx,ho⟩ :=
    Chapter8.Section02.HermitianSource.selected_exists_automizer_torus s hk
  exact ⟨y,x,hxy,hy,hq,hx,ho,
    Chapter8.Section02.HermitianSource.selected_normalizes_actor s hx⟩

/-- The E.2.14(9) fixed subgroup on the original chosen orbit, using the
constructed torus and proved centralizer bound of that selected pair. -/
theorem sourceOrbit_hermitian_selected_torus_fixed
    (e14 : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S) (hk : 1 < k) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ∃ x : Automizer D.sourceOrbit,
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^k-1 ∧
      x ∈ normalizer (inducedAutomizer D.sourceOrbit A : Set (Automizer D.sourceOrbit)) ∧
      automizerFixedGroup D.sourceOrbit (zpowers x) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨_,x,_,_,_,hx,ho,hfixed⟩ :=
    Chapter8.Section02.HermitianSource.selected_exists_torus_fixed
      KnownSimple.IsKnownSimple e14 h28 hchar hTI s hk
  exact ⟨x,hx,ho,Chapter8.Section02.HermitianSource.selected_normalizes_actor s hx,hfixed⟩


/-- The selected fixed-space identity and the actual Hermitian rank bounds
remove the large-fixed-space premise in the strict range k < 2n. -/
theorem sourceOrbit_hermitian_selected_fixed_torus_order
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (e14 : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S) (hk : 1 < k)
    (n : ℕ) [NeZero n] (hkn : k < 2*n)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ∃ x : Automizer D.sourceOrbit,
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^k-1 ∧
      x ∈ normalizer (inducedAutomizer D.sourceOrbit A : Set (Automizer D.sourceOrbit)) ∧
      automizerFixedGroup D.sourceOrbit (zpowers x) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      3*n < Module.finrank (ZMod 2)
        (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x)) ∧
      (PreservesMaximalParabolic n
          (coordinateHom (automizerRepresentation D.sourceOrbit) n
            (D.hermitianOrbitCoordinates n d) x) →
        k ∣ 4*n ∧ n ∣ Module.finrank (ZMod 2)
          (fixedSpace (automizerRepresentation D.sourceOrbit) (zpowers x))) := by
  obtain ⟨x,hx,ho,hn,hfixed⟩ := D.sourceOrbit_hermitian_selected_torus_fixed
    e14 h28 hchar hTI s hk
  have hlarge := Chapter8.Section02.HermitianSource.selected_fixed_rank_gt_three_mul
    s n (D.sourceOrbit_hermitian_rank n d)
    (D.sourceOrbit_hermitian_automizer_rank n d h).le hkn x hfixed
  refine ⟨x,hx,ho,hn,hfixed,hlarge,?_⟩
  intro hp
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  obtain ⟨hdeg,horder⟩ := D.sourceOrbit_hermitian_odd_parabolic_order h n d x hodd hlarge hp
  rw [ho] at horder
  exact ⟨(Chapter8.Section02.Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd
    (by omega : 0 < k)).mp horder,hdeg⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
