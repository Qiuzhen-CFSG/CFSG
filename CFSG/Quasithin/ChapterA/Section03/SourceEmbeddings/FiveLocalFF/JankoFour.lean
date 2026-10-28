module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourFirst
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Excluding a J₄ local A₅ section with its original irreducible module

The normal-elementary catalogue places the actual subgroup and its full
Sylow actor into the first involution centralizer. Pulling that centralizer
back through the actual ambient conjugation keeps the original chosen
module unchanged. Restriction preserves its full movement, core centrality
and invariant-subgroup interval; the native extraspecial-core obstruction
then contradicts its order at least sixteen.

This completes both native placement and local exclusion, with no block
recognition or core-containment premise. The Chapter10 consumer discharges
the chosen-section hypotheses from the original point configuration.
Source: Aschbacher--Smith A.3.12(17) and10.2.9, pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_map_ne_bot {H : Type*} [Group H]
    (f : G ≃* H) (B : Subgroup G) (hb : pCore 2 B ≠ ⊥) :
    pCore 2 (B.map f.toMonoidHom) ≠ ⊥ := by
  intro hz
  apply hb
  apply (map_eq_bot_iff_of_injective (f := (f.subgroupMap B).toMonoidHom) _
    (f.subgroupMap B).injective).mp
  rw [pCore_map_iso 2 (f.subgroupMap B)]
  exact hz

private noncomputable def comapEquiv {H : Type*} [Group H]
    (f : G ≃* H) (C : Subgroup H) : C.comap f.toMonoidHom ≃* C :=
  (f.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective f.surjective C))

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem not_first_overgroup (S : Sylow 2 G) (B E K : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 16 ≤ Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, E ⊓ centralizer (B : Set G) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set G) → N = E ⊓ centralizer (B : Set G) ∨ N = E)
    (hBK : B ≤ K) (hSK : (S : Subgroup G) ≤ K)
    (eK : K ≃* Janko4.InvolutionCentralizers.First.centralizer) : False := by
  have hEK := hEB.trans hBK
  have hfix : ((E.subgroupOf K) ⊓ centralizer (B.subgroupOf K : Set K)).map K.subtype =
      E ⊓ centralizer (B : Set G) := by
    apply le_antisymm
    · rintro x ⟨y,⟨hy,hc⟩,rfl⟩
      refine ⟨hy,?_⟩
      intro b hb
      exact congrArg Subtype.val (hc ⟨b,hBK hb⟩ hb)
    · rintro x ⟨hx,hc⟩
      refine ⟨⟨x,hEK hx⟩,⟨hx,?_⟩,rfl⟩
      intro b hb
      exact Subtype.ext (hc b hb)
  have hirr' (N : Subgroup K)
      (hlo : E.subgroupOf K ⊓ centralizer (B.subgroupOf K : Set K) ≤ N)
      (hhi : N ≤ E.subgroupOf K)
      (hn : B.subgroupOf K ≤ normalizer (N : Set K)) :
      N = E.subgroupOf K ⊓ centralizer (B.subgroupOf K : Set K) ∨ N = E.subgroupOf K := by
    have hlo' := map_mono (f := K.subtype) hlo
    rw [hfix] at hlo'
    have hhi' := map_mono (f := K.subtype) hhi
    rw [map_subgroupOf_eq_of_le hEK] at hhi'
    have hn' := (map_mono (f := K.subtype) hn).trans (N.le_normalizer_map K.subtype)
    rw [map_subgroupOf_eq_of_le hBK] at hn'
    rcases hirr (N.map K.subtype) hlo' hhi' hn' with h | h
    · left
      apply map_injective K.subtype_injective
      rwa [hfix]
    · right
      apply map_injective K.subtype_injective
      rwa [map_subgroupOf_eq_of_le hEK]
  let := hE
  apply not_jankoFour_first (S.subtype hSK) (B.subgroupOf K) (E.subgroupOf K)
    (local_restrict hl hBK) _ _ (IsElementaryAbelian.subgroupOf hEK) (comap_mono hEB)
    _ _ _ hirr' eK
  · intro s hs
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hSB hs) (b : G)
  · intro s hs
    apply mem_normalizer_iff.mpr
    intro e
    exact mem_normalizer_iff.mp (hSE hs) (e : G)
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
  · rw [pCoreIn_subgroupOf 2 B K hBK]
    intro b hb e he
    exact Subtype.ext (hcore hb e he)
  · apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEK,map_subgroupOf_eq_of_le hBK,hmove]

/-- The original fully moved irreducible section excludes the J4 carrier.
All placements and native local rows are discharged. -/
theorem not_section (f : G ≃* Janko4.Model) (S : Sylow 2 G) (B E : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) (hBcore : pCore 2 B ≠ ⊥)
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 16 ≤ Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, E ⊓ centralizer (B : Set G) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set G) → N = E ⊓ centralizer (B : Set G) ∨ N = E) : False := by
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  let S' := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let B' := B.map f.toMonoidHom
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hSB).trans (B.le_normalizer_map f.toMonoidHom)
  have hc' : pCore 2 B' ≠ ⊥ := core_map_ne_bot f B hBcore
  obtain ⟨g,hBg,hSg⟩ := first_centralizer_placement S' B' hl' hn'
    (SolvableQuotients.section_map f.toMonoidHom B hl eB).some hc'
  let c := f.trans (MulAut.conj g)
  let C := Janko4.InvolutionCentralizers.First.centralizer
  let K := C.comap c.toMonoidHom
  have hBK : B ≤ K := map_le_iff_le_comap.mp (by
    change B.map ((MulAut.conj g).toMonoidHom.comp f.toMonoidHom) ≤ _
    rw [←map_map]
    exact hBg)
  have hSK : (S : Subgroup G) ≤ K := map_le_iff_le_comap.mp (by
    change (S : Subgroup G).map ((MulAut.conj g).toMonoidHom.comp f.toMonoidHom) ≤ _
    rw [←map_map]
    exact hSg)
  let eK : K ≃* C := comapEquiv c C
  exact not_first_overgroup S B E K hl hSB hSE hE hEB hc hcore hmove hirr hBK hSK eK
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour
