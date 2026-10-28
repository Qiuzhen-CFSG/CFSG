module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicCubicSieve
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourResidualModels
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourDiagramLift
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual binary residual under cubic rotation control

The source rotation sieve first gives the full residual as PSL₂(31) or
PSL₃(2), with trivial center and the original maximal core equal to O₂.
The stronger cubic-only hypothesis applies to the actual marked quotient
and forces every odd-linear row to the binary PSL₃(2) diagram model.
The core-free projection identifies that model with the whole residual.

Both the maximal overlap and the image of the original Sylow are retained;
no central kernel is discarded without proving it trivial.
Source: Aschbacher–Smith 8.2.9, printed pp.720–721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterB ChapterE HermitianSource
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

/-- The cubic-only restriction leaves the actual binary full residual,
with the original maximal overlap and diagram witness retained. -/
theorem parabolic_quotient_cubic_residual_model
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2)
    (h3 : primeRank 3 X ≤ 1) (h5 : primeRank 5 X ≤ 1)
    (hrot : let q := QuotientGroup.mk' (pCore 2 X)
      ∀ (v r : X ⧸ pCore 2 X), v ∈ W.map q → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
        ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a → orderOf r = 3) :
    minimalParabolicCore S hP = pCore 2 X ∧
    let q := QuotientGroup.mk' (pCore 2 X)
    let M := (minimalParabolicMax S hP).map q
    let T := (S : Subgroup X).map q
    ∃ K : Subgroup (X ⧸ pCore 2 X), IsComponent (X ⧸ pCore 2 X) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (X ⧸ pCore 2 X) = K ∧
      center K = ⊥ ∧ K ⊔ T = ⊤ ∧ SingleClauses M K T ∧
      ClassicalGroup.IsPSL K 3 2 ∧ DiagramModel M K T 1 := by
  obtain ⟨hcore,K,hcomp,hK,hn,hres,hcenter,hgen,hclauses,hmodels⟩ :=
    parabolic_quotient_small_residual_models hX S hP hs W hWS hout hMW hcard h3 h5
      (fun v r hv hv1 hi p a hp hp2 ha hr => Or.inl (hrot v r hv hv1 hi p a hp hp2 ha hr))
  refine ⟨hcore,K,hcomp,hK,hn,hres,hcenter,hgen,hclauses,?_⟩
  rcases hmodels with ⟨_,hm⟩ | hm
  · let := hn
    let N := pCore 2 X
    let q := QuotientGroup.mk' N
    let R := S.mapSurjective (QuotientGroup.mk'_surjective N)
    let A := W.map q
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
    have hk : q.ker ≤ (S : Subgroup X) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal S
    have hPq := minimalParabolic_surjective S hP q (QuotientGroup.mk'_surjective N) hk
    have hmax : minimalParabolicMax R hPq = (minimalParabolicMax S hP).map q :=
      (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective N)
        (by simpa only [q,QuotientGroup.ker_mk'] using minimalParabolicTwoCore_le_core S hP)).symm
    have hJq : minimalParabolicCore R hPq = ⊥ := by
      change (minimalParabolicMax R hPq).normalCore = ⊥
      rw [hmax]
      exact image_normalCore_eq_bot _ _ hcore
    let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
    have hsq : ¬Group.IsSolvable (X ⧸ N) := fun hh =>
      hs ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,hh⟩)
    have hAout : ¬A ≤ minimalParabolicCore R hPq := by
      intro hh
      have hb : A = ⊥ := bot_unique (hh.trans hJq.le)
      change Nat.card A = 2 at hcard
      rw [hb,card_bot] at hcard
      omega
    have hMA : minimalParabolicMax R hPq ≤ normalizer (A : Set (X ⧸ N)) := by
      rw [hmax]
      exact (map_mono hMW).trans (le_normalizer_map q)
    have hm' := hm
    rw [←hmax] at hm'
    obtain ⟨hb,hd⟩ := parabolic_odd_linear_cubic_rotation_model R hPq hsq K hK hgen
      A (map_mono hWS) hAout hMA hcard hrot hm'
    let j := QuotientGroup.mk' (sourceKernel (minimalParabolicMax R hPq))
    have hji : Function.Injective j := by
      apply j.ker_eq_bot_iff.mp
      rw [QuotientGroup.ker_mk']
      exact hJq
    let e : K ≃* sourceImage (minimalParabolicMax R hPq) K :=
      MulEquiv.ofBijective (j.subgroupMap K)
        ⟨fun x y he => Subtype.ext (hji (congrArg Subtype.val he)),j.subgroupMap_surjective K⟩
    obtain ⟨F,hF,hfin,hsize,⟨eF⟩⟩ := hb
    rw [hmax] at hd
    exact ⟨⟨F,hF,hfin,hsize,⟨e.trans eF⟩⟩,hd⟩
  · exact hm

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
