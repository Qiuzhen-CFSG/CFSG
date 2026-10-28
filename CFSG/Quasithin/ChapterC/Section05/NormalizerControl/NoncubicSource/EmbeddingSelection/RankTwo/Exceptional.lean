module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SylowOvergroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.TwistedExceptional.BinaryG2Core
public import Theory.SpecificGroups.Tits.ProperSylowOvergroups
/-!
# Small exceptional rank-two carriers in the C.5.13 sieve

The actual G₂(2)′ and Tits carriers have self-centralizing two-cores in all
proper full-Sylow overgroups. Hence a quasisimple smaller local component
is the entire containing C-component. All carrier equivalences, full Sylow
subgroups and component inclusions remain literal.
Source: Aschbacher–Smith A.3.12(2) and C.5.13, printed pp.47,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterB.ComponentRecognition.SylowOvergroups
variable {G : Type*} [Group G] [Finite G]
private theorem eq_of_characteristic_two_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {D : Type*} [Group D] [Finite D] (e : L ≃* D)
    (hproper : ∀ (S : Sylow 2 D) (P : Subgroup D), (S : Subgroup D) ≤ P → P ≠ ⊤ →
      centralizer (pCore 2 P : Set P) ≤ pCore 2 P) : B = L := by
  apply eq_of_characteristic_two_sylow_overgroups T hB hL hBL
  intro S P hSP hne
  have him : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [he,map_top_of_surjective _ e.surjective]
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap P)).mpr
    (hproper (S.mapSurjective e.surjective) (P.map e.toMonoidHom) (map_mono hSP) him)

/-- The binary derived G₂ row, preserving the actual commutator carrier. -/
theorem eq_of_binary_g2_derived_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B]
    (hmodel : Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))) : B = L := by
  obtain ⟨e⟩ := hmodel
  exact eq_of_characteristic_two_model T hB hL hBL e
    (fun S P hSP hne => TwistedExceptional.BinaryG2.centralizer_twoCore_le S P hne hSP)

/-- The literal Tits row of the earlier Theorem C list. -/
theorem eq_of_tits_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] (hmodel : Nonempty (L ≃* Tits.ParrottGroup)) : B = L := by
  obtain ⟨e⟩ := hmodel
  exact eq_of_characteristic_two_model T hB hL hBL e
    Tits.ProperSylowOvergroups.centralizer_twoCore_le
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
