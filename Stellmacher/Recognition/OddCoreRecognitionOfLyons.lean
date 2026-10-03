module

public import Stellmacher.Recognition.CatalogueReduction
public import Stellmacher.Recognition.OddCoreRankThree
public import Stellmacher.Recognition.OddCoreComponentTransport
public import Stellmacher.Recognition.RankTwoSylowClassification
public import Stellmacher.Recognition.SemidihedralThreeCharacterBounds
public import Stellmacher.Recognition.SemidihedralCentralizingCore
public import ABG.ChapterIII.Section8.ThreeCoreArithmetic
public import ABG.ChapterII.Section2.SemidihedralInvolutionFour
public import Stellmacher.Recognition.FongWreathed
public import Theory.GroupTheory.InvolutionElementaryEight
public import ABG.ChapterII.Section1.RegularWreathHeightTwo

/-!
# Odd-core recognition from the supplied Lyons endpoint

A finite nonsolvable simple N₂ group with a nontrivial odd core in a full
involution centralizer is a catalogue model, provided the Lyons Sylow case
has trivial involution-centralizer odd cores. This endpoint is assumed only
for the ambient group in question.

An elementary subgroup of rank at least three places the given involution
in such a subgroup; its nontrivial odd-core closure contradicts rank-three
vanishing. The low-rank Sylow classification leaves four cases. Dihedral
recognition gives A₇ or an odd-field PSL₂, with the field bound supplied by
nonsolvability. Semidihedral odd-core vanishing and the supplied Lyons
endpoint exclude two cases. Fong recognizes the wreathed case as PSU₃(3).
In particular the legitimate odd-field PSL₂ branch is retained.

Sources: GLS2 §§21–22 (binary signalizers), Janko–Thompson's rank-two
classification, Gorenstein–Walter, and Fong's wreathed recognition; exact
source references and their proved inputs are in the imported modules.
-/

namespace Stellmacher.Recognition
universe u

-- Use the vanishing inputs directly: RankTwoSemidihedralCore also exports a
-- GL₂ theorem whose name collides with CoreFreeSemidihedralCentralizer in the
-- existing terminal-reduction consumers.
private theorem semidihedral_oddCore_eq_bot
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  obtain ⟨T, hTe, hT, hxT⟩ :=
    (ABG.isQDGroup_of_simple ⟨S, hS⟩).exists_four_containing_involution S hS x hx
  let : IsElementaryAbelian 2 T := hTe
  apply involutionCentralizer_oddCore_eq_bot_of_centralizing_four S hS hN x hx T hT hxT
  exact Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp
    (ABG.threeCore_index_eq_one_of_bounds
      (semidihedral_three_character_bounds S hS hN x hx T hT hxT)))

/-- Recognize the bad odd-core branch from the Lyons vanishing endpoint for
this ambient group. Every catalogue alternative carries an actual model
isomorphism. -/
public theorem isNTwoGroupModel_of_nontrivial_oddCore_of_lyons
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hLyons : ∀ S : Sylow 2 G, LyonsU3Four.SylowStructure S →
      ∀ t : G, orderOf t = 2 →
        pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (t : G) (ht : orderOf t = 2)
    (hbad : pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) :
    IsNTwoGroupModel G := by
  classical
  have hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8 := by
    intro E hE
    let : IsElementaryAbelian 2 E := hE
    by_contra hsmall
    obtain ⟨A, hA, hcard, htA⟩ :=
      Sylow.exists_elementary_eight_of_simple E (by omega) t ht
    let : IsElementaryAbelian 2 A := hA
    exact involutionOddCoreClosure_ne_bot_of_bad_involution A htA ht hbad
      (involutionOddCoreClosure_eq_bot_of_rankThree hns hN A hcard)
  let S : Sylow 2 G := Classical.choice inferInstance
  rcases rank_two_sylow_structure_alternative hns hN hrank S with hd | hs | hw | hl
  · rcases simple_dihedral_recognition hns S hd with hA | hPSL
    · obtain ⟨e⟩ := hA
      exact Or.inl (.alternatingSeven e)
    · obtain ⟨K, hK, hfinite, hodd, ⟨e⟩⟩ := hPSL
      let _ := hK
      let _ := hfinite
      exact isNTwoGroupModel_of_odd_psl2 hns K hodd e
  · exact (hbad (semidihedral_oddCore_eq_bot S hs hN t ht)).elim
  · obtain ⟨e⟩ := hw
    have hS : ABG.IsWreathedOfHeight S 2 :=
      ABG.wreathed_equiv e.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight
    let : Group.IsSolvable (Subgroup.centralizer ({t} : Set G)) :=
      hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer ht)
    exact Or.inl (.unitaryThree ⟨3, 1, Nat.prime_three, by decide,
      by decide, FongWreathed.nonempty_equiv_psu3 S hS t ht⟩)
  · exact (hbad (hLyons S hl t ht)).elim

end Stellmacher.Recognition
