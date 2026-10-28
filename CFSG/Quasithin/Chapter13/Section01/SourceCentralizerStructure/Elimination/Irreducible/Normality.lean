module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Preparation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source

/-!
# Normality of the irreducibly normalized escaping component

The actual full Sylow of C_G(u) normalizes the unique component containing
Ξₚ(L). The proved A.3.8 orbit theorem permits only a normal component or an
orbit of length two. The latter would make two divide that Sylow subgroup's
index. Hence K is normal in C_G(u), the normality needed for the subsequent
A.3.15 model inspection. This is relative normality in C_G(u), not in G.

Source: Aschbacher–Smith, 13.1.12(3), p.874, and A.3.8(3), pp.45–46.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The escaping component is normal in the literal involution centralizer. -/
theorem Context.component_normal (h : Context T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    (K.subgroupOf (centralizer ({u} : Set G))).Normal := by
  let H := centralizer ({u} : Set G)
  have hsq := h.hypothesis.simpleQTKE.involution_centralizer_sqtk (h.involution s.mem s.ne_one)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) :=
    ⟨XiEmbedding.quotient_stronglyQuasithin hsq.stronglyQuasithin,hsq.isKGroup.quotient _⟩
  rcases proposition_1_2_1_three_index_of_A_3_8
      (fun _ _ _ => ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple)
      hQ e.component.2 with hn | ⟨hn,_⟩
  · exact hn
  obtain ⟨S,hS⟩ := e.full_sylow
  have hSN : (S : Subgroup H) ≤ normalizer (K.subgroupOf H : Set H) := by
    intro x hx
    apply K.le_normalizer_comap H.subtype
    apply h.local_normalizes_component s e hi
    have hxT : (x : G) ∈ (T : Subgroup G) ⊓ H := hS ▸ mem_map_of_mem H.subtype hx
    exact ⟨h.sylow_normalizes hxT.1,hxT.2⟩
  have hd := index_dvd_of_le hSN
  rw [hn] at hd
  exact (S.not_dvd_index hd).elim

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
