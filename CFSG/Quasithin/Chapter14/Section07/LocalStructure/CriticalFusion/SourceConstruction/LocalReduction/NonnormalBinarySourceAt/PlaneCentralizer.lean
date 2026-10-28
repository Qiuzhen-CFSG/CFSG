module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.ReturningPoint
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryReturningPoint
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallInvariantLine
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The flag-plane centralizer in the original exchanged branch

The whole literal U/V₁ section is the determinant tensor for the normal
component orbit. Its original seed V/V₁ has four elements and is invariant
under the actual Sylow image. The small-invariant-space calculation makes
it the singular field line fixed by the inner Sylow. A centralizer of V₂
fixes a nonzero vector of this line; semilinearity therefore preserves the
whole line. The section's exact kernel lifts that invariance to the original
V, whose normalizer lies in M = N_G(L).

The final application discharges C_G(V₂) ≤ M in both clauses of 14.7.31.
For the second it retains the already constructed reciprocal plane and
returning-point geometry. Construction of Y,T_Y and the reciprocal-plane
centralizer core identity remain subsequent source obligations; no such
local premise is asserted or hidden in a recognition record here.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1057–1058,
and 14.7.31, printed p.1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem plane_centralizer_of_orthogonal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (N : Subgroup (HStar F.H)) [N.Normal]
    (hm : HasOrthogonalFourOrbit σ N)
    (S : Sylow 2 (HStar F.H))
    (hS : (S : Subgroup (HStar F.H)) = star F (T : Subgroup G)) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (V : Set G) := by
  obtain ⟨f,e,he⟩ := hm
  let f' := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  have hE (n : N) (v : W) : E (σ n v) =
      ClassicalOrthogonal.FourPlusMatrix.Binary.action (f' n) (E v) := by
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates (e (σ n v)) = _
    rw [he,OrthogonalEight.binaryCoordinates_equivariant]
    rfl
  obtain ⟨R,hR⟩ := S.exists_sylow_map_eq_inf_of_normal N
  have hc : Nat.card (s.imageSpace V) = 4 := by
    rw [s.imageSpace_card_eq_relIndex V (le_conjugateSpanBy V F.H)]
    have hh := relIndex_mul_card_of_le (F.le_seed 1)
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hv : Nat.card V = 8 := h.seed_card
    rw [hp,hv] at hh
    omega
  have hs : ∀ n ∈ R, ∀ v ∈ s.imageSpace V, σ (n : HStar F.H) v ∈ s.imageSpace V := by
    intro n hn v hv
    have hnS : (n : HStar F.H) ∈ (S : Subgroup (HStar F.H)) := by
      have hi := mem_map_of_mem N.subtype hn
      rw [hR] at hi
      exact hi.1
    rw [hS] at hnS
    obtain ⟨t,ht,heq⟩ := hnS
    rw [←heq]
    exact s.imageSpace_apply_mem V t (h.sylow_normalizes_seed_at structural ht) v hv
  have hnot : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro hh
    have hc := card_le_of_le hh
    rw [F.card 2 (by decide),F.card 1 (by decide)] at hc
    norm_num at hc
  obtain ⟨v,hv,hvn⟩ := SetLike.not_le_iff_exists.mp hnot
  let vU : F.U := ⟨v,le_conjugateSpanBy V F.H (F.le_seed 2 hv)⟩
  let w := (s.coordinates vU).toAdd
  have hw : w ∈ s.imageSpace V := (s.mem_imageSpace_iff _ _).mpr
    ⟨vU,F.le_seed 2 hv,rfl⟩
  have hwn : w ≠ 0 := fun hz => hvn ((s.coordinates_eq_one_iff vU).mp hz)
  have hCH : centralizer (F.Vi 2 : Set G) ≤ F.H :=
    (centralizer_le (F.monotone (by decide : 1 ≤ 2))).trans (Subgroup.centralizer_le_normalizer _)
  have hpres (x : G) (hx : x ∈ centralizer (F.Vi 2 : Set G))
      (u : G) (hu : u ∈ V) : x*u*x⁻¹ ∈ V := by
    let xH : F.H := ⟨x,hCH hx⟩
    have hfix : σ (starMap F xH) w = w := by
      have heq : (⟨x*v*x⁻¹,(mem_normalizer_iff.mp (s.normalized xH.property) v).mp vU.property⟩ : F.U) = vU := by
        apply Subtype.ext
        change x*v*x⁻¹ = v
        rw [←hx v hv,mul_inv_cancel_right]
      have hh := s.equivariant xH vU
      change (s.coordinates ⟨x*v*x⁻¹,_⟩).toAdd = σ (starMap F xH) w at hh
      rw [heq] at hh
      exact hh.symm
    let uU : F.U := ⟨u,le_conjugateSpanBy V F.H hu⟩
    have huW : (s.coordinates uU).toAdd ∈ s.imageSpace V :=
      (s.mem_imageSpace_iff _ _).mpr ⟨uU,hu,rfl⟩
    have hmove := ClassicalOrthogonal.FourPlusMatrix.Binary.normal_ambient_preserves_small_space
      σ N f' E hE R (s.imageSpace V) hc hs (starMap F xH) w hw hwn hfix
      (s.coordinates uU).toAdd huW
    have heq := s.equivariant xH uU
    change (s.coordinates ⟨x*u*x⁻¹,_⟩).toAdd = σ (starMap F xH) (s.coordinates uU).toAdd at heq
    rw [←heq] at hmove
    exact (s.coordinates_mem_imageSpace_iff_of_kernel_le V (F.le_seed 1) _).mp hmove
  intro x hx
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · exact hpres x hx u
  · intro hu
    have hh := hpres x⁻¹ ((centralizer (F.Vi 2 : Set G)).inv_mem hx) (x*u*x⁻¹) hu
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The original exchanged component forces the flag-plane centralizer into
M through the singular field line on the literal U/V₁ section. -/
theorem local_nonnormal_component_plane_centralizer_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (V : Set G) ∧
      centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hU,a,hm,hrest⟩ := local_nonnormal_component_whole_orthogonal_at d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let := hU
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := b.orbit_normal
  have hm' : HasOrthogonalFourOrbit a.representation b.orbit := horbit.symm ▸ hm
  let s₀ := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s₀.le
    kernel_le := s₀.line_le
    normalized := s₀.normalizes
    coordinates := s₀.quotient
    onto := s₀.surjective
    kernel_eq := s₀.kernel
    equivariant := fun x v => (s₀.conjugates x v).symm }
  have hC := plane_centralizer_of_orthogonal h structural a.representation s b.orbit hm' b.sylow hS
  exact ⟨hC,hC.trans (h.seed_normalizer_le_at structural)⟩

/-- Both original weak-closure applications now have their flag-plane
centralizer premise discharged. The second retains only the construction
of the normalizing overgroup, its relative Sylow and its plane core. -/
theorem local_nonnormal_component_weakClosure_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ L ⊔ (T : Subgroup G) ∧
      L ⊔ (T : Subgroup G) ≤
        normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ∧
      normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ≤
        normalizer (L : Set G)) ∧
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧
      P ≤ F.U ⊓ c.Uα ∧
      ∀ (Y R : Subgroup G), Y₀ ≤ Y → Y ≤ normalizer (P : Set G) →
        Chapter1.IsSylowIn 2 R Y →
        Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 →
        ChapterE.indexedWeakClosure V R 0 ≤ Y ∧
          Y ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G) := by
  have hC := (local_nonnormal_component_plane_centralizer_at d h hab structural previous
    faithful earlier I K hI hKI hK hnormal).2
  refine ⟨EarlierWeakClosureAt.clause_one h structural F hab hC,?_⟩
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hweak⟩ :=
    local_nonnormal_component_weakClosure_of_plane_core_at d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  exact ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,
    fun Y R hY hN hSylow hcore => hweak Y R hY hN hSylow hcore hC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
