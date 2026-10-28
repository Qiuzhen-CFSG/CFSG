module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSize
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinaryExclusion

/-!
# Literal DGS profile restrictions for the Cartan prime pair

The source's first local group DS contains the whole original S. The
F.1.1 local-Sylow containment therefore identifies O₂ of the full Borel
with this S. Consequently a Chapter 11 elementary-row count on that
literal Borel core contradicts the original strict bound |S| > 64.
The proof below derives the order from the actual conjugate seeds and
left-parabolic core. It does not identify S with an unrelated minimal
Sylow subgroup supplied by another completion.

For type-only rows, inclusion in the actual reduced generated group
transports its starred right core quotient back to R/O₂(R). Any solvable
quotient there contradicts the nonsolvability of the selected R. This
removes the binary linear, dihedral and Suzuki types without constructing
an amalgam isomorphism or assuming that R is a component of H.

The earlier DGS seed geometry and classification remain explicit. These
are conditional restrictions used by the original Chapter 12 consumer.
Source: DGS85 (11.7), p.174, (13.1), p.191, and (15.1), p.226;
Aschbacher–Smith F.1.10–12, pp.262–264, and 5.2.2, pp.647–648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.Source ChapterF.Source.SuzukiContainment
open ChapterF.Source.DGS85.CommutingOneProfile ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]

/-- The core of the WHOLE original Borel is the original S, by its
containment in DS. This says nothing about a different minimal completion. -/
theorem LocalData.zeroCore_borel_core_eq_sourceS
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    (Global.sourceS L H ⊔ (B ⊓ R)).pCoreIn 2 = Global.sourceS L H := by
  let S := Global.sourceS L H
  have hf := d.hypothesisF11 h hH c hd hz
  have he : reducedSylow ![D ⊔ S,R] S = S := by
    apply le_antisymm (reducedSylow_le hf)
    have hh := localSylow_le_reducedSylow hf 0
    change S ⊓ (D ⊔ S) ≤ _ at hh
    simpa only [inf_eq_left.mpr (show S ≤ D ⊔ S from le_sup_right)] using hh
  change (commonBorel ![D ⊔ S,R] S).pCoreIn 2 = S at he
  rwa [d.zeroCore_commonBorel hz] at he

/-- The actual Chapter 11 elementary-row geometry gives order 64 for
the original S and is therefore impossible. Conjugation preserves the
literal left core because its actor belongs to that left parabolic. -/
theorem LocalData.zeroCore_no_elementary_binary_profile
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (Z Z' : Subgroup G) (g : G)
    (hg : g ∈ (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R))
    (hconj : Z.map (MulAut.conj g).toMonoidHom = Z')
    (hn : ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2 ≤ normalizer (Z : Set G))
    (hcore : ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2 =
      pairSpan Z Z' (((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2))
    (hB : (Global.sourceS L H ⊔ (B ⊓ R)).pCoreIn 2 =
      Z ⊔ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2)
    (hZ : Nat.card Z = 16)
    (hindex : (Z ⊓ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2).relIndex Z = 2)
    (hinter : Nat.card ((Z ⊓ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2) ⊓
      (Z' ⊓ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2) : Subgroup G) = 2) : False := by
  let P := (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)
  let Q := P.pCoreIn 2
  have hQ : Q.map (MulAut.conj g).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp
      ((P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))) hg)
  have hsize : Nat.card (Global.sourceS L H) = 64 := by
    rw [← d.zeroCore_borel_core_eq_sourceS h hH c hd hz]
    exact sylow_card_of_pair_core Q Z Z' _ g hQ hconj hn hcore hB
      4 2 (by decide) (by decide) (by norm_num; exact hZ) hindex hinter
  have hbound := d.sourceS_card_gt h hH c hd
  have hlo : 64 ≤ 2^(3*n) := by
    have he := h.exponent
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 6 ≤ 3*n)
  rw [hsize] at hbound
  omega

/-- A solvable type on the reduced generated right starred quotient
pulls back along the actual inclusion to the same original right factor. -/
theorem LocalData.zeroCore_no_solvable_reduced_right_quotient
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {X : Type*} [Group X] [Group.IsSolvable X]
    (e : (reducedGeneratedStarred ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1 ⧸
      pCore 2 (reducedGeneratedStarred ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1)) ≃* X) :
    False := by
  have hf := d.hypothesisF11 h hH c hd hz
  let f := ((reduced_hypothesis hf).generatedStarredQuotientEquiv 1).trans e
  have hq : Group.IsSolvable (R ⧸ pCore 2 R) :=
    Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  let : Group.IsNilpotent (pCore 2 R) := pCore_isNilpotent
  exact d.right_nonsolvable ((Group.isSolvable_iff_subgroup_quotient (pCore 2 R)).mpr
    ⟨inferInstance,hq⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
