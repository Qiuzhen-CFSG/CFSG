module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFourPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.Containing
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.SixSection

/-!
# The original order-32 A₆ section is excluded in J₄

The original local C-component and full normalizing Sylow are transported
through an actual J₄ marking and conjugated into its first involution
centralizer. The perfect subgroup lies in the literal triple-cover preimage;
the complete A₆ two-core quotient contradicts the native cubic-cover
obstruction. Nontriviality of the original two-core is sufficient.

The order-32 wrapper and its source consumer retain the supplied B and K,
using exactly B.subgroupOf K and the supplied Sylow intersection. No
module marking, quintic displacement certificate or additional placement
hypothesis is needed. Source: Aschbacher–Smith A.3.12 and 8.2.13,
pp.47–48,722–723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open FiveLocalFF.SolvableQuotients

/-- A nontrivial two-core and a full A6 quotient exclude J4 as the original
carrier of a local C-component normalized by its full Sylow. -/
theorem not_janko_four_of_core {G : Type*} [Group G] [Finite G]
    (e : G ≃* Janko4.Model) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hc : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  let d := e.subgroupMap B
  have hc' : pCore 2 (B.map e.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := d.toMonoidHom) _ d.injective).mp
    rw [pCore_map_iso 2 d]
    exact hz
  obtain ⟨g,hBg,_⟩ := JankoFour.first_centralizer_placement
    (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)
    ((map_mono hn).trans (B.le_normalizer_map e.toMonoidHom))
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans eB) hc'
  let C := Janko4.InvolutionCentralizers.First.centralizer
  let D := (B.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
  let A := D.subgroupOf C
  let a := (subgroupOfEquivOfLe hBg).trans (((MulAut.conj g).subgroupMap
    (B.map e.toMonoidHom)).symm.trans d.symm)
  let := local_perfect hl
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  exact Janko4.InvolutionCentralizers.First.not_six_section A
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eB)

/-- The literal order-32 source row is excluded in J4 with no module premise. -/
theorem not_janko_four {G : Type*} [Group G] [Finite G]
    (e : G ≃* Janko4.Model) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hc : Nat.card (pCore 2 B) = 32)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  apply not_janko_four_of_core e S B hl hn _ eB
  intro hz
  rw [hz,card_bot] at hc
  omega

/-- Apply the J4 exclusion to the same B.subgroupOf K and original Sylow
intersection supplied by A.3.12. No additional point-module marking is used. -/
theorem source_not_janko_four {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    ¬ Nonempty (K ≃* Janko4.Model) := by
  rintro ⟨e⟩
  obtain ⟨S,_,hl,hn,_,hc,ha⟩ := source_sylow_restriction T hB hK hBK hTB hcore hA6
  exact not_janko_four e S (B.subgroupOf K) hl hn hc ha.some

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
