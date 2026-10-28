module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Setup
/-!
# The local closures of Section 12.8

Constructing the G.2 hypothesis gives the literal central omega containment,
Frattini bound, Sylow normality and reducedness of 12.8.4(2--3). Reducedness
also supplies the lower inclusion in the action-kernel equality; its reverse
inclusion uses ambient uniqueness in the separate kernel argument.

Source: Aschbacher--Smith, Lemma 12.8.4, printed p.850.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
variable {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M J : Subgroup G) (hn : 2 ≤ n)
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hres : pResidual 2 L = ⊤)
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (hJ : J ∈ F.Hz L M)

include hG hn hVT hLV hTL hres hnatural hJ

/-- All the literal G.2.2 conclusions for J∈H_z, with G.2.1 discharged. -/
theorem localKernel_closure :
    (F.tilde V ≤ F.tilde (F.UH J) ∧
      F.tilde (F.UH J) ≤ omegaOneAmbient
        ((center (F.tilde (J.pCoreIn 2))).map (F.tilde (J.pCoreIn 2)).subtype)) ∧
    (frattini (F.UH J)).map (F.UH J).subtype ≤ F.Vi 1 ∧
    (F.UH J ≤ (T : Subgroup G) ∧ ((F.UH J).subgroupOf (T : Subgroup G)).Normal) ∧
    IsPReduced 2 ((F.tilde (F.UH J)).subgroupOf (F.tilde J)) :=
  ChapterG.Section02.CentralClosure.parabolic_UH F L J
    (F.localKernel_hypothesis hG L M J hn hVT hLV hTL hres hnatural hJ)

/-- Every local closure is a two-group, including the abelian branch. -/
theorem localKernel_UH_isPGroup : IsPGroup 2 (F.UH J) :=
  (F.localKernel_hypothesis hG L M J hn hVT hLV hTL hres hnatural hJ).U_isPGroup

/-- The actual tilded local closure is elementary abelian. -/
theorem localKernel_tilde_UH_elementary : IsElementaryAbelian 2 (F.tilde (F.UH J)) :=
  (F.localKernel_hypothesis hG L M J hn hVT hLV hTL hres hnatural hJ).tilde_U_elementary

/-- The lower kernel bound follows from the central containment, without uniqueness. -/
theorem localKernel_core_le : pCore 2 J ≤ (F.localTildeAction J hJ.2.1).ker := by
  have hc := (F.localKernel_closure hG L M J hn hVT hLV hTL hres hnatural hJ).1.2
  have hJH : J ≤ F.H := hJ.2.1
  change pCore 2 J ≤ (F.localTildeAction J hJH).ker
  have hJU : J ≤ normalizer (F.UH J : Set G) := le_normalizer_conjugateSpanBy V J
  intro j hj
  change j ∈ (F.tildeAction J (F.UH J) hJH hJU).ker
  rw [F.tildeAction_ker J (F.UH J) hJH hJU]
  change ∀ u ∈ F.tilde (F.UH J), u * F.tildeProjection (inclusion hJH j) =
    F.tildeProjection (inclusion hJH j) * u
  intro u hu
  obtain ⟨z, hz, rfl⟩ := omegaOneAmbient_le _ (hc hu)
  have hq : F.tildeProjection (inclusion hJH j) ∈ F.tilde (J.pCoreIn 2) :=
    ⟨inclusion hJH j, mem_map_of_mem J.subtype hj, rfl⟩
  exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨_, hq⟩)).symm
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
