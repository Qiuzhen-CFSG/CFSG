module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothAbelian
public import Theory.GroupTheory.PGroup.OmegaCenterDetection

/-!
# The center-free vertex in the asymmetric source orientation

If the original Ω₁(Z(S)) centralizes the second vertex, its intersection
with the embedded center of the first vertex is normal in both vertices.
Source faithfulness kills that intersection. Detection of normalized
subgroups in Ω₁(Z(S)) then kills the whole first vertex center.

Source context: Kurzweil–Stellmacher, §10.3, pp.285–299, assumption A5;
Aschbacher–Smith F.1.12, pp.262–264. This is the valid asymmetric consequence
of failure of A5. It does not assert the separate critical-distance theorem
which forces that failure, nor an upper bound on the remaining pair.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

omit [Finite G] in
private theorem center_centralizes (H : Subgroup G) :
    (center H).map H.subtype≤centralizer (H : Set G) := by
  rintro _ ⟨z,hz,rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)

/-- In the asymmetric source orientation, centrality of the original omega
center at the second vertex kills the whole center of the first vertex. -/
theorem left_center_eq_bot_of_right_centralizes_omega
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G))
    (hz : omegaOneAmbient ((center (S : Subgroup G)).map (S : Subgroup G).subtype)≤
      centralizer (B : Set G)) : center A=⊥ := by
  let D := (center A).map A.subtype
  let Z := omegaOneAmbient ((center (S : Subgroup G)).map (S : Subgroup G).subtype)
  have hDQ : D≤(pCore 2 A).map A.subtype :=
    map_mono ((center_le_centralizer _).trans (h.local_core_selfCentralizing hA))
  have hDS : D≤(S : Subgroup G) := hDQ.trans (hS ▸ h.local_twoCore_le_intersection)
  have hDC : D≤centralizer (A : Set G) := center_centralizes A
  have hDN : (S : Subgroup G)≤normalizer (D : Set G) :=
    (hS.symm.le.trans inf_le_left).trans
      ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _))
  have hI : Z⊓D≤A⊓B := inf_le_right.trans (hDS.trans hS.symm.le)
  have hid : Z⊓D=⊥ := by
    apply h.common_normal_eq_bot hcore (Z⊓D) hI
    · exact (normal_subgroupOf_iff_le_normalizer (hI.trans inf_le_left)).mpr
        ((le_centralizer_iff.mp (inf_le_right.trans hDC)).trans
          (Subgroup.centralizer_le_normalizer _))
    · exact (normal_subgroupOf_iff_le_normalizer (hI.trans inf_le_right)).mpr
        ((le_centralizer_iff.mp (inf_le_left.trans hz)).trans
          (Subgroup.centralizer_le_normalizer _))
  have hd : D=⊥ := eq_bot_of_normalized_of_omega_center_disjoint (S : Subgroup G)
    D S.isPGroup' hDS hDN hid
  exact (map_eq_bot_iff_of_injective (center A) A.subtype_injective).mp hd
end CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
