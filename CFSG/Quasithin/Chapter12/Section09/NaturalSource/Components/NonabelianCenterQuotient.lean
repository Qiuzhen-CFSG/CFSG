module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianCenterAction

public import Theory.GroupTheory.IrreducibleImageInterval
public import CFSG.Quasithin.Chapter12.Section08.Terminal.Centers

/-!
# The original center quotient and its centralizer in 12.9.4

Conjugation by the selected g carries (Z(U) intersect Z(U)^g)V₁ to the
kernel of the actual action of Z(U)^g on U/Z(U). Since g normalizes L₀,
its proved irreducibility on the dotted returning center transports to
the literal quotient Z(U)/((Z(U) intersect Z(U)^g)V₁).

L₀ also normalizes C_{Z(U)}(Z(U)^g). The returning center centralizes the
denominator and does not centralize all of Z(U), so irreducibility gives
C_{Z(U)}(Z(U)^g) = (Z(U) intersect Z(U)^g)V₁, of index four. The nonzero
commutator of the centers lies in Z(I₂); Sylow fixed points then give the
nontrivial source seed Ω₁(Z(T)) intersect Z(I₂).

These are the literal center-action inputs to the ensuing NaturalReduction 4
application. That contradiction, catalogue exhaustion and LocalControlInput
remain with the natural-branch assembly owner.

Source: Aschbacher--Smith 12.9.4, equation (*) and the following paragraph,
printed p.860 of refs/quasithin.pdf; the seed is from 12.8.13(5), p.856.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- Conjugation carries the exact denominator in (*) to the actual action kernel. -/
theorem nonabelian_center_denominator_conjugate {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate ((F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1) g =
      conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype := by
  obtain ⟨hcI,hk⟩ := nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH
  rw [hk,hcI,conjugate,Subgroup.map_sup]
  congr 1
  change conjugate (Section08.centerIn (F.I₂ L)) g = Section08.centerIn (F.I₂ L)
  rw [←centerIn_conjugate,(conjugate_eq_iff (F.I₂ L) g).mpr
    (le_normalizer_conjugateSpanBy F.U (F.P L) hgP)]

/-- Irreducibility on the literal center quotient, expressed by its invariant
subgroup interval. Both the denominator and actor are the source subgroups. -/
theorem nonabelian_caseFive_center_quotient_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∀ A : Subgroup G, (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ≤ A → A ≤ F.ZU →
      planeCentralizerResidual F L ≤ normalizer (A : Set G) →
      A = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ∨ A = F.ZU := by
  let := h.chosen.elementary
  let K := (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1
  let D := conjugate F.ZU g
  let R := planeCentralizerResidual F L
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hg2 := F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes hgP
  have hDH : D ≤ F.H := (F.conjugate_ZU_le_X g).trans (F.X_le_H g hg2)
  have hKZ : K ≤ F.ZU := sup_le inf_le_left (F.point_le_ZU (by have := h.rank; omega))
  have hKH : conjugate K g ≤ F.H := (map_mono hKZ).trans hDH
  have hker : D.subgroupOf F.H ⊓ q.ker = (conjugate K g).subgroupOf F.H := by
    apply Subgroup.map_injective F.H.subtype_injective
    rw [Subgroup.map_inf _ _ _ F.H.subtype_injective,map_subgroupOf_eq_of_le hDH,
      map_subgroupOf_eq_of_le hKH,QuotientGroup.ker_mk']
    exact (nonabelian_center_denominator_conjugate h earlier F hne g hgP hgH).symm
  have hRg : conjugate R g = R := (conjugate_eq_iff R g).mpr
    (parabolic_normalizes_planeResidual h earlier F hgP)
  intro A hKA hAZ hRA
  have hAgH : conjugate A g ≤ F.H := (map_mono hAZ).trans hDH
  have hRAN : R ≤ normalizer (conjugate A g : Set G) := by
    rw [←hRg]
    exact (map_mono hRA).trans (A.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  have hi := Subgroup.interval_of_irreducible_image q (R.subgroupOf F.H)
    (D.subgroupOf F.H) ((conjugate K g).subgroupOf F.H) hker
    (nonabelian_caseFive_center_irreducible_planeResidual h hn earlier F hne g hgP hgH B h5)
    ((conjugate A g).subgroupOf F.H) (comap_mono (map_mono hKA))
    (comap_mono (map_mono hAZ))
    ((comap_mono hRAN).trans ((conjugate A g).le_normalizer_comap F.H.subtype))
  have hconj : Function.Injective (fun C : Subgroup G => conjugate C g) :=
    Subgroup.map_injective (MulAut.conj g⁻¹).injective
  rcases hi with hi | hi
  · left
    apply hconj
    have he := congrArg (Subgroup.map F.H.subtype) hi
    simpa only [map_subgroupOf_eq_of_le hAgH,map_subgroupOf_eq_of_le hKH] using he
  · right
    apply hconj
    have he := congrArg (Subgroup.map F.H.subtype) hi
    simpa only [map_subgroupOf_eq_of_le hAgH,map_subgroupOf_eq_of_le hDH] using he

/-- The source L₀ normalizes both centers and hence their relative centralizer. -/
theorem nonabelian_planeResidual_normalizes_center_centralizer
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (g : G) (hgP : g ∈ F.P L) :
    planeCentralizerResidual F L ≤
      normalizer ((F.ZU ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) : Set G) := by
  have hRH : planeCentralizerResidual F L ≤ F.H := by
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans (inf_le_left.trans ((F.Li_le L 1).trans inf_le_right))
  have hRZ : planeCentralizerResidual F L ≤ normalizer (F.ZU : Set G) :=
    hRH.trans ((le_normalizer_conjugateSpanBy V F.H).trans
      (normalizer_le_normalizer_characteristic_image F.U (Subgroup.center F.U)))
  have hRD : planeCentralizerResidual F L ≤ normalizer (conjugate F.ZU g : Set G) := by
    rw [←(conjugate_eq_iff (planeCentralizerResidual F L) g).mpr
      (parabolic_normalizes_planeResidual h earlier F hgP)]
    exact (map_mono hRZ).trans (F.ZU.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  exact (le_inf hRZ (hRD.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf

/-- The precise centralizer equality following equation (*) on printed p.860. -/
theorem nonabelian_caseFive_center_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    F.ZU ⊓ centralizer (conjugate F.ZU g : Set G) =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 := by
  let := h.chosen.elementary
  have hKZ : (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ≤ F.ZU :=
    sup_le inf_le_left (F.point_le_ZU (by have := h.rank; omega))
  have hKD : (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ≤
      centralizer (conjugate F.ZU g : Set G) := by
    apply sup_le
    · have hD : IsMulCommutative (conjugate F.ZU g) := by
        change IsMulCommutative (F.ZU.map (MulAut.conj g⁻¹).toMonoidHom)
        infer_instance
      exact inf_le_right.trans (le_centralizer_iff_isMulCommutative.mpr hD)
    · exact (F.le_seed 1).trans (le_centralizer_iff.mp
        (F.conjugate_center_centralizes_seed g
          (F.P_le_seed_normalizer L h.chosen.normalizes hgP)))
  have hi := nonabelian_caseFive_center_quotient_irreducible h hn earlier F hne g hgP hgH B h5
    (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)) (le_inf hKZ hKD) inf_le_left
    (nonabelian_planeResidual_normalizes_center_centralizer h earlier F g hgP)
  apply hi.resolve_right
  intro he
  apply nonabelian_caseFive_centers_noncommuting h hn earlier F hne g hgP hgH B h5
  exact le_centralizer_iff.mp (he.ge.trans inf_le_right)

/-- The returning center has moved rank two on the original center. -/
theorem nonabelian_caseFive_center_centralizer_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    (F.ZU ⊓ centralizer (conjugate F.ZU g : Set G)).relIndex F.ZU = 4 := by
  rw [nonabelian_caseFive_center_centralizer h hn earlier F hne g hgP hgH B h5]
  exact nonabelian_caseFive_center_quotient_four h hn earlier F hne g hgP hgH B h5

/-- The actual seed Z_D = Ω₁(Z(T)) intersect Z(I₂) is nontrivial in the
orthogonal branch. This follows from the noncommuting original centers. -/
theorem nonabelian_caseFive_omega_center_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    sylowOmega T ⊓ Section08.centerIn (F.I₂ L) ≠ ⊥ := by
  let := h.chosen.elementary
  have hmeet := (nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1
  have hneI : Section08.centerIn (F.I₂ L) ≠ ⊥ := by
    intro he
    have hc : ⁅F.ZU,conjugate F.ZU g⁆ = ⊥ := le_bot_iff.mp
      ((F.centers_commutator_le g (F.P_le_seed_normalizer L h.chosen.normalizes hgP)).trans
        (hmeet.trans he).le)
    exact nonabelian_caseFive_centers_noncommuting h hn earlier F hne g hgP hgH B h5
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  have hs := (F.localKernel_commutator_squares h.source.simpleQTKE L _
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F earlier.alternatives)).2
  have hUT := F.binary_U_le_sylow (by have := h.rank; omega) hs
  have hIT : Section08.centerIn (F.I₂ L) ≤ (T : Subgroup G) :=
    hmeet.ge.trans (inf_le_left.trans ((map_subtype_le _).trans hUT))
  have hTP : (T : Subgroup G) ≤ F.P L :=
    (F.sylow_le_orderedParabolic L 1).trans (F.orderedParabolic_one L).le
  have hTN : (T : Subgroup G) ≤ normalizer (Section08.centerIn (F.I₂ L) : Set G) :=
    (hTP.trans (le_normalizer_conjugateSpanBy F.U (F.P L))).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L)))
  intro hz
  apply hneI
  apply eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) _ T.isPGroup' hIT hTN
  exact hz

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components


