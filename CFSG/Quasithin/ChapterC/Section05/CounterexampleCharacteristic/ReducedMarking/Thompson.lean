module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Core
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Thompson escape for the actual reduced Sylow subgroup

If J(T) lay in O₂(KT), Thompson heredity would identify it with the
Thompson subgroup of that characteristic core. It would then be normal
in both KT and the supplied normalizer of T, contradicting C.5.2.
The literal module centralizer theorem turns this escape into the
nontrivial Thompson action needed by the natural Baumann calculations.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizer_thompson (T : Subgroup G) :
    normalizer (T : Set G) ≤ normalizer (elementaryAbelianMaxJ T : Set G) := by
  intro g hg
  have he : T.map (MulAut.conj g).toMonoidHom = T := mem_normalizer_iff_map_conj_eq.mp hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ T).map (MulAut.conj g).toMonoidHom = elementaryAbelianMaxJ T
  rw [← elementaryAbelianMaxJ_map_equiv,he]

theorem thompson_moves_block (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (hSylow : ∃ P : Sylow 2 (K ⊔ T : Subgroup G),
      (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥) :
    ¬ elementaryAbelianMaxJ T ≤ centralizer (U K : Set G) := by
  let A := K ⊔ T
  let C := A.pCoreIn 2
  have hc := reduced_baumann_core K T hK hT hn hSylow
  have hCT : C ≤ T := hc.2.2.2.2.2.ge.trans inf_le_left
  have hUT : U K ≤ T := hc.2.1.trans hc.2.2.1
  have hU : IsElementaryAbelian 2 (U K) := hK.elementary.map K.subtype
  have hUne : U K ≠ ⊥ := by
    intro hz
    exact hK.blockU_ne_bot ((map_injective K.subtype_injective)
      (hz.trans (Subgroup.map_bot K.subtype).symm))
  have hJne : elementaryAbelianMaxJ T ≠ ⊥ := by
    intro hz
    obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty T
    have he : E = ⊥ := bot_unique (hz ▸ le_sSup hE)
    have hh := hE.2.2 (U K) hUT hU
    rw [he,card_bot] at hh
    exact hUne ((U K).eq_bot_of_card_le hh)
  intro hJC
  have hJC' : elementaryAbelianMaxJ T ≤ C := by
    change elementaryAbelianMaxJ T ≤ (K ⊔ T).pCoreIn 2
    rw [← hc.2.2.2.2.2]
    exact le_inf (sSup_le fun _ hE => hE.1) hJC
  have hJeq : elementaryAbelianMaxJ T = elementaryAbelianMaxJ C := by
    obtain ⟨h1,hJ1⟩ := elementaryAbelianMaxOrder_le_and_j_le_of_eq C T hCT
    obtain ⟨h2,hJ2⟩ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le T C hJC'
    exact le_antisymm (hJ2 (le_antisymm h2 h1)) (hJ1 (le_antisymm h1 h2))
  apply hJne
  apply hno _ (sSup_le fun _ hE => hE.1) (normalizer_thompson T)
  change K ⊔ T ≤ normalizer (elementaryAbelianMaxJ T : Set G)
  rw [hJeq]
  exact (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))).trans
    (normalizer_thompson C)

theorem core_le_baumann_of_alpha (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (hSylow : ∃ P : Sylow 2 (K ⊔ T : Subgroup G),
      (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (ha : ChapterB.thompsonAlpha T ≤
      (ChapterB.thompsonAlpha T ⊓ centralizer (K : Set G)) ⊔ U K) :
    (K ⊔ S T).pCoreIn 2 ≤ S T := by
  have hc := reduced_baumann_core K T hK hT hn hSylow
  have hKC : K ≤ centralizer (ChapterB.thompsonAlpha T ⊓ centralizer (K : Set G) : Subgroup G) :=
    le_centralizer_iff.mpr inf_le_right
  have hSC : S T ≤ centralizer (ChapterB.thompsonAlpha T ⊓ centralizer (K : Set G) : Subgroup G) :=
    (show S T ≤ centralizer (ChapterB.thompsonAlpha T : Set G) from inf_le_right).trans
      (centralizer_le inf_le_left)
  have hQC := (pCoreIn_le 2 (K ⊔ S T)).trans (sup_le hKC hSC)
  have hQU := hc.2.2.2.2.1.le.trans inf_le_right
  exact le_inf hc.2.2.1 (le_centralizer_iff.mpr (ha.trans
    (sup_le (le_centralizer_iff.mp hQC) (le_centralizer_iff.mp hQU))))
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
