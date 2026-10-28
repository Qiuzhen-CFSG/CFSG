module

public import CFSG.Quasithin.ChapterF.Section08
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.AbelianClauses
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Kernel
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The original F.8 application in the abelian branch of Section 12.8

From the actual invariant flag and the earlier 12.8.1–3 setup facts, the
abelian span condition gives F.8.1(a). The literal quotient-action kernel
of 12.8.4 gives (c), via the normal-core/conjugate-span identity. Uniqueness
of the maximal two-local overgroup of LT and J not contained in M give (d).
Neither clause, G.2.1, nor F.8.2 is an input.

The explicit characteristic-L, reduced-seed, centralizer and natural-marking
inputs belong to the earlier setup constructed by qt-12-08-setup and
qt-12-08; the transitivity and escape inputs are 12.8.3. The abelian branch
is retained. The first four conditions of 12.8.6 are connected here; its
F.9 condition retains its owner. The actual F.8 track and all seven
F.8.7 conclusions are also applied here in the same abelian branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 12.8.4 and 12.8.6, printed pp.850–851; F.8.1–2, printed p.316.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n)

/-- The F.8 data are the original subgroups, without any new witness. -/
abbrev f8SourceSetup (L J : Subgroup G) : ChapterF.Section08.Setup G :=
  { V := V, V₁ := F.Vi 1, L := L, T := (T : Subgroup G), H := J }

/-- The actual tilde-action kernel is precisely F.8's quotient centralizer. -/
theorem f8Source_centralizer_eq_kernel (L J : Subgroup G) (hJ : J ≤ F.H) :
    ChapterF.Section08.Setup.quotientCentralizer (F.f8SourceSetup L J) hJ
      (F.UH J) = (F.localTildeAction J hJ).ker := by
  exact (F.tildeAction_ker J (F.UH J) hJ (le_normalizer_conjugateSpanBy V J)).symm

/-- In the original quotient, the seed-centralizer core is the span-action kernel. -/
theorem f8Source_core_eq_kernel (L J : Subgroup G) (hJ : J ≤ F.H) (hVJ : V ≤ J) :
    (ChapterF.Section08.Setup.quotientCentralizer (F.f8SourceSetup L J) hJ V).normalCore =
      (F.localTildeAction J hJ).ker := by
  exact (ChapterF.Section08.Setup.quotientCentralizer_span
    (F.f8SourceSetup L J) hJ hVJ).symm.trans (F.f8Source_centralizer_eq_kernel L J hJ)

variable [Finite G] [IsElementaryAbelian 2 V]
variable {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M : Subgroup G) (hn : 2 ≤ n)
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hres : pResidual 2 L = ⊤)
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (hM : M = normalizer (L : Set G))
    (hunique : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} = {M})
    (hCV : centralizer (V : Set G) ≤ M)
    (hCL : L ⊓ centralizer (V : Set G) = L.pCoreIn 2)
    (hcharL : generalizedFitting L = pCore 2 L)
    (hreduced : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))))
    (hCLT : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (z : G) (hz : F.Vi 1 = zpowers z) (hz1 : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ a ∈ normalizer (V : Set G), (MulAut.conj a) z = x)

include hG hn hVT hLV hTL hres hnatural hM hunique hCV hCL hcharL hreduced hCLT z hz hz1 htrans

/-- 12.8.6(2) implies (4): construct every original F.8.1 clause for each J∈H_z. -/
theorem f8Source_hypothesis (habelian : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L M) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L J) := by
  have hg := F.localKernel_hypothesis hG L M J hn hVT hLV hTL hres hnatural hJ
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans hg.local_le
  have hVJ := hVT.trans hTJ
  have hk := F.localKernel_eq_pCore hG L M J hn hVT hLV hTL hres hnatural
    hM hunique hCV hCL hJ
  have hcomm := (F.f8a_iff_f9f (by omega)).mpr
    ((F.f9f_iff_abelian_U (by omega) z hz hz1 htrans).mpr habelian)
  have hCT : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).trans_eq hCLT
    · apply le_inf
      · exact (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans
          (map_subgroupOf_eq_of_le le_sup_right).le
      · exact hCLT.symm.le.trans inf_le_right
  refine {
    sylow := ⟨T, rfl⟩
    elementary := hg.elementary
    residual := hres
    T_normalizes_L := hTL
    characteristic_L := hcharL
    V_le_LT := hVT.trans le_sup_right
    reduced := hreduced
    centralizer_eq := hCT
    point_ne_bot := hg.point_ne_bot
    point_le := hg.point_le
    T_normalizes_point := hg.T_normalizes_point
    conjugates_commute := hcomm
    quotient_nonzero := hg.quotient_nonzero
    irreducible := hg.irreducible
    H_le := hJ.2.1
    local_le := hg.local_le
    characteristic_H := hg.characteristic_two
    centralizer_core_le := ?_
    generated_core := ?_ }
  · exact ((F.f8Source_core_eq_kernel L J hJ.2.1 hVJ).trans hk).le
  · apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ J M _ hJ.2.2
    intro R hR hLR
    exact Set.mem_singleton_iff.mp (hunique ▸ (show R ∈
      {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} from ⟨hR, hLR⟩))

/-- Apply all of F.8.2 to the actual Section 12.8 local subgroup and quotient action. -/
theorem f8Source_closure (habelian : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L M) :
    (F.tilde (F.UH J) ≤ omegaOneAmbient
      ((center (F.tilde (J.pCoreIn 2))).map (F.tilde (J.pCoreIn 2)).subtype)) ∧
    pCore 2 (J ⧸ (F.localTildeAction J hJ.2.1).ker) = ⊥ ∧
    IsPGroup 2 (F.UH J) ∧
    (frattini (F.UH J)).map (F.UH J).subtype ≤ F.Vi 1 ∧
    (F.localTildeAction J hJ.2.1).ker = pCore 2 J := by
  have h := F.f8Source_hypothesis hG L M hn hVT hLV hTL hres hnatural hM hunique
    hCV hCL hcharL hreduced hCLT z hz hz1 htrans habelian J hJ
  have hf := ChapterF.Section08.Setup.lemma_F_8_2 h
  have hker := F.f8Source_centralizer_eq_kernel L J hJ.2.1
  refine ⟨hf.2.1, ?_, hf.2.2.2.1, hf.2.2.2.2.1, hker.symm.trans hf.2.2.2.2.2⟩
  let : (ChapterF.Section08.Setup.quotientCentralizer (F.f8SourceSetup L J)
    hJ.2.1 (F.UH J)).Normal := h.quotientCentralizer_U_normal
  have hp := hf.2.2.1
  change pCore 2 (J ⧸ ChapterF.Section08.Setup.quotientCentralizer (F.f8SourceSetup L J)
    hJ.2.1 (F.UH J)) = ⊥ at hp
  let e := QuotientGroup.quotientMulEquivOfEq hker
  calc
    pCore 2 (J ⧸ (F.localTildeAction J hJ.2.1).ker) =
        (pCore 2 (J ⧸ ChapterF.Section08.Setup.quotientCentralizer
          (F.f8SourceSetup L J) hJ.2.1 (F.UH J))).map e.toMonoidHom :=
      (pCore_map_iso 2 e).symm
    _ = ⊥ := by rw [hp, Subgroup.map_bot]

/-- The actual F.8.1 assertions for all local subgroups are equivalent to the
abelian branch; the reverse implication applies F.8.5(2) to the full point normalizer. -/
theorem f8Source_iff_abelian_U (hescape : ¬ F.H ≤ M) :
    IsMulCommutative F.U ↔ ∀ J ∈ F.Hz L M,
      ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L J) := by
  constructor
  · exact F.f8Source_hypothesis hG L M hn hVT hLV hTL hres hnatural hM hunique
      hCV hCL hcharL hreduced hCLT z hz hz1 htrans
  · intro hall
    have h := hall F.H (F.H_mem_Hz (by omega) L M hescape)
    exact (ChapterF.Section08.Setup.lemma_F_8_5_two h).toIsMulCommutative

/-- The first four conditions of 12.8.6, with the original setup inputs still
owned by their earlier source producers. -/
theorem f8Source_lemma_12_8_6_one_through_four (hescape : ¬ F.H ≤ M) :
    ((∀ J ∈ F.Hz L M, IsMulCommutative (F.UH J)) ↔ IsMulCommutative F.U) ∧
    (IsMulCommutative F.U ↔
      ∀ g : G, V ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) ∧
    (IsMulCommutative F.U ↔ ∀ J ∈ F.Hz L M,
      ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L J)) := by
  exact ⟨F.all_local_spans_abelian_iff (by omega) L M hescape,
    F.abelian_U_iff_intersections_commute (by omega) z hz hz1 htrans,
    F.f8Source_iff_abelian_U hG L M hn hVT hLV hTL hres hnatural hM hunique
      hCV hCL hcharL hreduced hCLT z hz hz1 htrans hescape⟩

/-- The actual abelian branch of Section 12.8 has the original odd track and
all seven F.8.7 conclusions. Only the earlier setup inputs listed above remain
with their Section 12.8 producers; no geometric premise is assumed here. -/
theorem f8Source_geometry (habelian : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L M) :
    let D := F.f8SourceSetup L J
    ∃ hF : ChapterF.Section08.Setup.Hypothesis D,
      3 ≤ hF.b ∧ Odd hF.b ∧ IsElementaryAbelian 2 (F.UH J) ∧
      ∃ C : hF.CriticalPath,
        (C.vertexGroup (Subgroup.CosetGeometry.RankTwo.base
            (ChapterF.Section08.Setup.Hypothesis.family (D := D)) false) ⊓
          C.vertexGroup (Subgroup.CosetGeometry.RankTwo.base
            (ChapterF.Section08.Setup.Hypothesis.family (D := D)) true) =
          D.L₁ ⊔ D.T) ∧
        (F.UH J ≤ (C.vertexGroup C.penultimate ⊓ C.vertexGroup C.endpoint).pCoreIn 2 ∧
          C.Ug ≤ (C.vertexGroup (Subgroup.CosetGeometry.RankTwo.base
            (ChapterF.Section08.Setup.Hypothesis.family (D := D)) true) ⊓
            C.vertexGroup C.second).pCoreIn 2) ∧
        ⁅F.UH J, C.Ug⁆ ≤ F.UH J ⊓ C.Ug ∧
        C.Ug ≤ normalizer (F.UH J : Set G) ∧
        (¬ ⁅C.Ug, V⁆ ≤ C.A₁) ∧ F.Vi 1 ⊓ C.A₁ = ⊥ ∧
        (⁅C.Ug, C.DH⁆ ≤ C.A₁ ∧ ⁅F.UH J, C.Dg⁆ ≤ F.Vi 1) ∧
        ⁅C.DH, C.Dg⁆ = ⊥ := by
  let hF := F.f8Source_hypothesis hG L M hn hVT hLV hTL hres hnatural hM hunique
    hCV hCL hcharL hreduced hCLT z hz hz1 htrans habelian J hJ
  obtain ⟨C⟩ := hF.exists_criticalPath
  exact ⟨hF, hF.lemma_F_8_5.1, hF.lemma_F_8_5.2.1, hF.lemma_F_8_5.2.2,
    C, C.lemma_F_8_7⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
