module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# The section kernel and returning-point argument in 14.7.67

Let K = O²(H), M = N_G(L), D = C_{N_G(K)}(K/O₂(K)), and
D₁ = O²(D ∩ M). All these groups are literal ambient subgroups; E is the
conjugate span of the original point V₁ under D.

The actual S₅ marking of H/O₂(H) identifies the K-image with A₅. The
centralizer of A₅ in S₅ is trivial (proved with two three-cycles), giving
D ∩ H ≤ O₂(H) ≤ T. Since D normalizes K, K centralizes E; thus C_D(E) ≤ T.
If V₁ᵍ ≤ E, two-perfectness puts K inside Kᵍ, and equal finite orders give
g ∈ N_G(K). This proves the returning-point step on printed p.1071 without
assuming the normalizer identity which that argument is intended to prove.
The core-transport application retains the earlier U ≤ O₂(K) premise.

We also prove that D₁ = 1 is equivalent to D ∩ M ≤ T when T ≤ M, that a
proper local-component overgroup of K moves V₁, and that K escapes M.
The actual 1.2.7 implication yields uniqueness over H once K ∈ L* is proved.
The final elementary assembly turns N_G(K)=KDT and D a two-group into
N_G(K)=H. These conditional deductions do not establish their remaining
premises: proper-overgroup exclusion, D₁-vanishing, the R₁/dual-chief-factor
analysis, and the full Thompson argument are still required.

Earlier-source producers: qt-1-02-adequate-assembly owns the complete
`Uniqueness127` input (its conditional deduction is already in Section02);
qt-14-05 and qt-14-07-components own the preceding local/module identities.
No conclusion of the remaining normalizer argument is stored in `Data` or
in a new hypothesis record. The ambient fixed-centralizer branch is separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 14.7.67(3–4), printed pp.1070–1071, PDF pp.1087–1088.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace ResidualNormalizer
open Equiv
private theorem commuting_pair : ∀ g : Perm (Fin 5),
    g * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * g →
    g * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * g → g = 1 := by
  intro g ha hb
  have ha2 := congrArg (fun f : Perm (Fin 5) => f 2) ha
  have ha0 := congrArg (fun f : Perm (Fin 5) => f 0) ha
  have hb2 := congrArg (fun f : Perm (Fin 5) => f 2) hb
  have hb3 := congrArg (fun f : Perm (Fin 5) => f 3) hb
  have h20 : g 2 ≠ g 0 := g.injective.ne (by decide)
  have h23 : g 2 ≠ g 3 := g.injective.ne (by decide)
  clear ha hb
  have h2 : g 2 = 2 := by
    generalize h : g 2 = j at *
    fin_cases j <;> simp_all [Perm.mul_apply, swap_apply_def]
  have h0 : g 0 = 0 := by simpa [Perm.mul_apply, swap_apply_def, h2] using ha2
  have h1 : g 1 = 1 := by simpa [Perm.mul_apply, swap_apply_def, h0] using ha0
  have h3 : g 3 = 3 := by simpa [Perm.mul_apply, swap_apply_def, h2] using hb2
  have h4 : g 4 = 4 := by simpa [Perm.mul_apply, swap_apply_def, h3] using hb3
  apply DFunLike.ext
  intro i
  fin_cases i <;> assumption

private theorem symmetricFive_centralizer {g : ChapterJ.S5}
    (hg : g ∈ centralizer (alternatingGroup (Fin 5) : Set ChapterJ.S5)) : g = 1 := by
  apply commuting_pair g
  · exact (hg _ (by simp [Equiv.Perm.mem_alternatingGroup])).symm
  · exact (hg _ (by simp [Equiv.Perm.mem_alternatingGroup])).symm

/-- The kernel of the actual normalizer action on K/O₂(K). -/
def D (F : InvariantFlag T V 3) : Subgroup G := Chapter4.sectionCentralizer (K F)
/-- The source uses the two-residual, not the two-core, of D ∩ M. -/
def D₁ (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G :=
  (pResidual 2 (D F ⊓ normalizer (L : Set G) : Subgroup G)).map
    (D F ⊓ normalizer (L : Set G)).subtype
/-- The conjugate span occurring in Thompson factorization. -/
def E (F : InvariantFlag T V 3) : Subgroup G := conjugateSpanBy (F.Vi 1) (D F)

omit [Finite G] in
theorem D_le_normalizer : D F ≤ normalizer (K F : Set G) :=
  commutatorPreimage_le _ _ _

omit [Finite G] in
theorem D_commutator : ⁅D F, K F⁆ ≤ (K F).pCoreIn 2 :=
  (Chapter4.le_sectionCentralizer_iff _ _).mp le_rfl |>.2

omit [Finite G] in
theorem normalizer_K_normalizes_D : normalizer (K F : Set G) ≤ normalizer (D F : Set G) := by
  apply commutatorPreimage_normalized
  · exact normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))
  · exact (normalizer (K F : Set G)).le_normalizer
  · exact le_rfl
  · exact normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))

omit [Finite G] in
theorem D₁_le : D₁ L F ≤ D F ⊓ normalizer (L : Set G) := map_subtype_le _

theorem D₁_twoPerfect : IsPPerfect 2 (D₁ L F) := isPPerfect_embedded_pResidual 2 _

omit [Finite G] in
theorem D_normalizes_E : D F ≤ normalizer (E F : Set G) :=
  le_normalizer_conjugateSpanBy _ _

omit [Finite G] in
theorem point_le_E : F.Vi 1 ≤ E F := le_conjugateSpanBy _ _
/-- Vanishing of the source residual is equivalent to the required intersection
bound. The reverse implication uses two-perfectness, not a core argument. -/
theorem D₁_eq_bot_iff_inf_le_sylow
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    D₁ L F = ⊥ ↔ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) := by
  let Y := D F ⊓ normalizer (L : Set G)
  constructor
  · intro hz
    have hr : pResidual 2 Y = ⊥ :=
      (map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hz
    have hp : IsPGroup 2 Y := by
      intro y
      obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := Y) 2
        (QuotientGroup.mk' (pResidual 2 Y) y)
      refine ⟨n, ?_⟩
      apply mem_bot.mp
      rw [← hr]
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pResidual 2 Y) (y ^ 2 ^ n) = 1
      rw [map_pow]
      exact hn
    have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
      (le_inf (((F.invariant 1).trans (H_normalizes_K F)).trans normalizer_K_normalizes_D)
        (hTM.trans (normalizer (L : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have he : (T : Subgroup G) ⊔ Y = (T : Subgroup G) :=
      T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hp hTY) le_sup_left
    exact he ▸ (le_sup_right : Y ≤ (T : Subgroup G) ⊔ Y)
  · intro hY
    have hp : IsPGroup 2 (D₁ L F) := T.isPGroup'.to_le (D₁_le.trans hY)
    have he := D₁_twoPerfect (L := L) (F := F) |>.hom_eq_one_of_isPGroup hp
      (MonoidHom.id (D₁ L F))
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)

omit [Finite G] in
/-- A two-group section centralizer is contained in the actual ambient Sylow,
because that Sylow normalizes the section kernel. -/
theorem D_le_sylow_of_isPGroup (hp : IsPGroup 2 (D F)) : D F ≤ (T : Subgroup G) := by
  have hn : (T : Subgroup G) ≤ normalizer (D F : Set G) :=
    ((F.invariant 1).trans (H_normalizes_K F)).trans normalizer_K_normalizes_D
  have he : (T : Subgroup G) ⊔ D F = (T : Subgroup G) :=
    T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hp hn) le_sup_left
  exact he ▸ (le_sup_right : D F ≤ (T : Subgroup G) ⊔ D F)

end ResidualNormalizer

namespace Data
open ResidualNormalizer
variable (d : Data T L V F W)

omit [Finite G] in
theorem K_core_le_H_core : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)

include d

omit d in
/-- A local component contained in H lies in its genuine two-residual. -/
theorem localComponent_le_K_of_le_H {I : Subgroup G}
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hIH : I ≤ F.H) : I ≤ K F := by
  have hr := embedded_pResidual_mono 2 hIH
  rw [(pResidual_eq_top_iff 2 _).mpr
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hI),
    ← MonoidHom.range_eq_map, range_subtype] at hr
  exact hr

/-- The first step of the proper-overgroup exclusion: a strict local overgroup
of K moves the original point. The faithful-family deduction remains separate. -/
theorem proper_local_overgroup_moves_point {I : Subgroup G}
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hKI : K F < I) :
    ¬ I ≤ centralizer (F.Vi 1 : Set G) := by
  intro hc
  have hh : I ≤ F.H := by
    rw [d.centralizer_eq]
    apply hc.trans (centralizer_le (Set.singleton_subset_iff.mpr ?_))
    rw [d.point]
    exact mem_zpowers d.z
  exact hKI.not_ge (localComponent_le_K_of_le_H hI hh)

/-- The earlier singleton H_z statement includes the source escape from M. -/
theorem H_not_le_normalizer_L : ¬ F.H ≤ normalizer (L : Set G) := by
  have hh : F.H ∈ F.Hz L (normalizer (L : Set G)) :=
    d.unique_Hz.symm ▸ Set.mem_singleton F.H
  exact hh.2.2

/-- Hence K also escapes M, since the actual Sylow subgroup lies in M. -/
theorem K_not_le_normalizer_L
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ¬ K F ≤ normalizer (L : Set G) := by
  intro hK
  apply d.H_not_le_normalizer_L
  rw [d.residual_product]
  exact sup_le hK hTM

theorem residualSpan_centralized_by_K : K F ≤ centralizer (E F : Set G) :=
  le_centralizer_conjugateSpanBy_of_normalizes _ _ _ D_le_normalizer
    ((K_le_H F).trans d.H_centralizes_point)

theorem residualSpan_centralizer_le_H : centralizer (E F : Set G) ≤ F.H := by
  rw [d.centralizer_eq]
  apply centralizer_le
  apply Set.singleton_subset_iff.mpr
  apply point_le_E
  rw [d.point]
  exact mem_zpowers d.z

theorem point_le_D : F.Vi 1 ≤ D F := by
  apply (Chapter4.le_sectionCentralizer_iff _ _).mpr
  have hc : F.Vi 1 ≤ centralizer (K F : Set G) :=
    le_centralizer_iff.mp ((K_le_H F).trans d.H_centralizes_point)
  exact ⟨hc.trans (Subgroup.centralizer_le_normalizer _),
    (commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le⟩

theorem residualSpan_le_D : E F ≤ D F := conjugateSpanBy_le_self d.point_le_D

private theorem conjugate_K_le_of_point_le_span (g : G)
    (hg : conjugate (F.Vi 1) g ≤ E F) : K F ≤ conjugate (K F) g := by
  have hc : K F ≤ centralizer (conjugate (F.Vi 1) g : Set G) :=
    d.residualSpan_centralized_by_K.trans (centralizer_le hg)
  have hH : K F ≤ conjugate F.H g := by
    intro k hk
    apply mem_map.mpr
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · rw [d.centralizer_eq]
      apply mem_centralizer_singleton_iff.mpr
      have hz : g⁻¹ * d.z * g ∈ conjugate (F.Vi 1) g := by
        apply mem_map.mpr
        exact ⟨d.z, by rw [d.point]; exact mem_zpowers d.z, by simp⟩
      have he := mem_centralizer_iff.mp (hc hk) _ hz
      have he' := congrArg (fun a : G => g * a * g⁻¹) he
      simpa [mul_assoc] using he'.symm
    · simp [mul_assoc]
  have hr := embedded_pResidual_mono 2 hH
  rw [(pResidual_eq_top_iff 2 _).mpr (K_twoPerfect F),
    ← MonoidHom.range_eq_map, range_subtype] at hr
  exact hr.trans_eq (map_embedded_pResidual 2 F.H (MulAut.conj g⁻¹).toMonoidHom).symm

/-- The returning-point step on printed p.1071 does not use N_G(K)=H. -/
theorem returning_point_conjugator_normalizes_K (g : G)
    (hg : conjugate (F.Vi 1) g ≤ E F) : g ∈ normalizer (K F : Set G) := by
  apply (conjugate_eq_iff _ _).mp
  apply (eq_of_le_of_card_ge (d.conjugate_K_le_of_point_le_span g hg) ?_).symm
  exact (card_map_of_injective (K := K F) (MulAut.conj g⁻¹).injective).le

/-- Application to the actual two-core in the solvable Thompson branch. -/
theorem returning_point_conjugate_U_le_core (g : G)
    (hg : conjugate (F.Vi 1) g ≤ E F) (hU : F.U ≤ (K F).pCoreIn 2) :
    conjugate F.U g ≤ (K F).pCoreIn 2 := by
  have hn := normalizer_le_normalizer_characteristic_image (K F) (pCore 2 (K F))
    (d.returning_point_conjugator_normalizes_K g hg)
  exact (map_mono hU).trans_eq ((conjugate_eq_iff _ _).mpr hn)

/-- The actual S₅ marking kills D ∩ H, already modulo O₂(H). -/
theorem D_inf_H_le_core : D F ⊓ F.H ≤ F.H.pCoreIn 2 := by
  intro a ha
  let aH : F.H := ⟨a, ha.2⟩
  have hc : d.qH aH ∈ centralizer (alternatingGroup (Fin 5) : Set ChapterJ.S5) := by
    intro b hb
    rw [← d.K_image] at hb
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hb
    have hm : ⁅a, (k : G)⁆ ∈ F.H.pCoreIn 2 :=
      K_core_le_H_core (commutator_le.mp D_commutator a ha.1 k hk)
    have hm' : ⁅aH, k⁆ ∈ d.qH.ker := by
      rw [d.qH_ker]
      exact hm
    have he : ⁅d.qH aH, d.qH k⁆ = 1 := by
      simpa only [map_commutatorElement] using MonoidHom.mem_ker.mp hm'
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have he : d.qH aH = 1 := by
    apply ResidualNormalizer.symmetricFive_centralizer hc
  have hk : aH ∈ d.qH.ker := he
  rw [d.qH_ker] at hk
  exact hk

/-- The source D ∩ H bound uses the given Sylow subgroup of H. -/
theorem D_inf_H_le_sylow : D F ⊓ F.H ≤ (T : Subgroup G) :=
  d.D_inf_H_le_core.trans ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
    (map_subgroupOf_eq_of_le (F.invariant 1)))

/-- C_D(E) lies in T because the original point is a subgroup of E. -/
theorem D_inf_centralizer_residualSpan_le_sylow :
    D F ⊓ centralizer (E F : Set G) ≤ (T : Subgroup G) :=
  (inf_le_inf_left _ d.residualSpan_centralizer_le_H).trans d.D_inf_H_le_sylow

/-- Apply the genuine 1.2.7 conclusion to K. Its T-orbit is K because H
normalizes its own residual. Maximal membership is supplied by the separate
proper-overgroup exclusion, not asserted by this deduction. -/
theorem residual_normalizer_unique_of_maximal
    (earlier : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hmax : K F ∈ Chapter1.LStar G (T : Subgroup G)) :
    Chapter4.UniqueMaximalOvergroup F.H (normalizer (K F : Set G)) := by
  have hu := earlier G d.counterexample.qtke T (K F) hmax
  have horbit : Theory.GroupTheory.componentOrbit (K F) (T : Subgroup G) = K F := by
    apply le_antisymm _ (Theory.GroupTheory.le_componentOrbit _ _)
    exact iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      ((F.invariant 1).trans (H_normalizes_K F))
  refine ⟨?_, H_normalizes_K F, ?_⟩
  · simpa only [horbit] using hu.normalizer_maximal
  · intro N hN hHN
    have he := hu.normalizer_unique N hN (d.residual_product ▸ hHN)
    simpa only [horbit] using he

/-- Final residual-normalizer assembly after the genuine automorphism
factorization and the Thompson branch have been proved. -/
theorem normalizer_K_eq_H_of_sectionCentralizer_twoGroup
    (factorization : normalizer (K F : Set G) = K F ⊔ D F ⊔ (T : Subgroup G))
    (hp : IsPGroup 2 (D F)) : normalizer (K F : Set G) = F.H := by
  rw [factorization, sup_assoc, sup_eq_right.mpr (D_le_sylow_of_isPGroup hp),
    ← d.residual_product]

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
