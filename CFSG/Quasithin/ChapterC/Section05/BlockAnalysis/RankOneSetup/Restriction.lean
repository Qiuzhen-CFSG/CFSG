module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Natural
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Cubic
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Transport
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.NormalizerRestriction
/-!
# The rank-one setup for the original Sylow subgroup

Restrict R to N_R(K). The original movement equation and Baumann
normalization preserve J(R) and Baum(R), and the full block Sylow
intersection supplies the actual Sylow of the normalized extension.
The natural and A₃ constructions therefore return the setup on the
original R, with its full central cover and literal conjugation action.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem exists_rankOne_setup (R K : Subgroup G) (hR : IsPGroup 2 R)
    (htype : (∃ n, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 3)
    (hmove : K = ⁅K,elementaryAbelianMaxJ R⁆)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K) :
    ∃ (F : Type) (_ : Field F), Nonempty (Setup R K F) := by
  let T := R ⊓ normalizer (K : Set G)
  obtain ⟨hJeq,hBeq,Q,hQ⟩ := normalizer_restriction R K hR hmove hn P hP
  have hT : IsPGroup 2 T := hR.to_le inf_le_left
  have hm : K = ⁅K,elementaryAbelianMaxJ T⁆ := by rw [hJeq]; exact hmove
  rcases htype with ⟨n,hnat⟩ | ha
  · obtain ⟨F,hF,h⟩ := RankOneSetup.exists_normalized_linear_setup K T hnat hT inf_le_right Q hQ hm
    exact ⟨F,hF,h.elim (setup_of_baumann_eq R T K hBeq)⟩
  · obtain ⟨h⟩ := RankOneSetup.exists_normalized_cubic_setup ha T hT inf_le_right Q hQ hm
    exact ⟨ZMod 2,inferInstance,setup_of_baumann_eq R T K hBeq h⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
