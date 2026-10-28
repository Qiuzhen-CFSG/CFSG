module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Configuration
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Source.Basic
public import Theory.GroupTheory.CentralizerSylowNormalizerFusion

/-!
# The actual source normalizer mover in Lemma 16.4(c)

The distinguished circle of a subgroup is preserved by its normalizer because
Z is conjugation invariant. For the selected Sylow T₁ of C_G(u), centrality
of z in T₁ makes T₁ centralize uz. Burnside fusion therefore supplies a mover
in N_G(T₁). This mover preserves Q=T₁° and sends u to uz, hence normalizes
Q⟨u⟩. Since Q⟨u⟩ lies in M and contains the distinguished z, its full
normalizer lies in M. These are the literal normalizers in the source proof.

Source: GLS IV, Chapter 2, Lemma 16.4(c), final paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
public theorem source16_normalizer_preserves_localCircle
    (h : IsProductDisconnected Z M) (T : Subgroup G) :
    normalizer (T : Set G) ≤ normalizer (localCircleIn Z T : Set G) := by
  rw [localCircleIn_eq_closure]
  intro g hg
  apply normalizer_le_normalizer_closure
  intro z
  constructor
  · rintro ⟨hz, hzT⟩
    exact ⟨h.invariant g z hz, (mem_normalizer_iff.mp hg z).mp hzT⟩
  · rintro ⟨hz, hzT⟩
    refine ⟨?_, (mem_normalizer_iff.mp hg z).mpr hzT⟩
    have hh := h.invariant g⁻¹ (g * z * g⁻¹) hz
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using hh

private theorem normalizes_root_join_of_conj_mul
    (Q : Subgroup G) {g u z : G} (hg : g ∈ normalizer (Q : Set G))
    (hz : z ∈ Q) (he : MulAut.conj g u = u * z) :
    g ∈ normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [Subgroup.map_sup, MonoidHom.map_zpowers, mem_normalizer_iff_map_conj_eq.mp hg]
    change Q ⊔ zpowers (MulAut.conj g u) ≤ Q ⊔ zpowers u
    rw [he]
    exact sup_le le_sup_left (zpowers_le.mpr ((Q ⊔ zpowers u).mul_mem
      ((show zpowers u ≤ Q ⊔ zpowers u from le_sup_right) (mem_zpowers u))
      ((show Q ≤ Q ⊔ zpowers u from le_sup_left) hz)))
  · exact (card_map_of_injective (K := Q ⊔ zpowers u)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).ge

/-- Burnside's original source mover normalizes Q⟨u⟩ and lies in M.
Only the selected centralizer Sylow and the source fusion u~uz are inputs. -/
public theorem source16_exists_root_join_normalizer_mover
    (h : IsProductDisconnected Z M) {u z : G}
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hSM : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ M)
    (huS : u ∈ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hz : z ∈ Z)
    (hzS : z ∈ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hSz : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ centralizer ({z} : Set G))
    (hconj : IsConj u (u * z)) :
    let T := (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype
    let Q := localCircleIn Z T
    ∃ g ∈ normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G),
      g ∈ M ∧ MulAut.conj g u = u * z := by
  let T := (S : Subgroup (centralizer ({u} : Set G))).map
    (centralizer ({u} : Set G)).subtype
  let Q := localCircleIn Z T
  have hQz : z ∈ Q := by
    change z ∈ localCircleIn Z T
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨hz, hzS⟩
  have hTuz : T ≤ centralizer ({u * z} : Set G) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact ((show Commute x u from mem_centralizer_singleton_iff.mp
      (map_subtype_le (S : Subgroup (centralizer ({u} : Set G))) hx)).mul_right
      (mem_centralizer_singleton_iff.mp (hSz hx))).eq
  obtain ⟨g, hg, he⟩ := exists_normalizer_conjugator_of_centralizer_sylow u (u * z) S hTuz hconj
  have hgQ : g ∈ normalizer (Q : Set G) := source16_normalizer_preserves_localCircle h T hg
  have hgN := normalizes_root_join_of_conj_mul Q hgQ hQz he
  have hRM : Q ⊔ zpowers u ≤ M := sup_le ((localCircleIn_le Z T).trans hSM)
    (zpowers_le.mpr (hSM huS))
  exact ⟨g, hgN, normalizer_le h hRM ⟨z, hz,
    (show Q ≤ Q ⊔ zpowers u from le_sup_left) hQz⟩ hgN, he⟩

end BenderSuzuki.ZD
