module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightBlock
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalTorusAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Torus

/-!
# The original Cartan, characteristic subgroup and degree-two reduction

For the maximal A₇ component, the original Cartan intersection is its
escaping cubic. The torus displacement argument therefore identifies
Cartan normalization of this component with original field degree two.

When the right residual is not a block, C.1.28 supplies a nontrivial
characteristic subgroup of Baum(T) normalized by H. Cartan normalization
of Baum(T) and generation by H and the cubic put K T in its normalizer.
Local uniqueness then forces the Cartan to normalize K, giving degree two.
The nonblock and Cartan–Baumann normalization premises are explicit here;
the companion LocalBaumann module discharges normalization. The two block
exclusions and the unconditional source theorem remain open.

Source: Aschbacher–Smith 5.1.13, printed p.638, refs/quasithin.pdf.
-/

public noncomputable section
universe u
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type u} [Group G] [Finite G]

/-- In the actual A₇ configuration, normalization of the maximal component
by the original Cartan is equivalent to degree two. -/
theorem LocalA7Configuration.cartan_normalizes_iff_degree_two
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X D) :
    A ≤ normalizer (K : Set G) ↔ n = 2 := by
  constructor
  · intro hn
    apply c.degree_two_of_normalized_component h.sylow_normalizes h.linear
      a.sylow_normalizes hn
      (by rw [a.cartan_intersection_eq_cubic h c d,d.cubic_card])
      (d.cubic_le.trans inf_le_left) d.cubic_card
    obtain ⟨t,ht,hi⟩ := d.cubic_inverted
    exact ⟨t,⟨ht.1,a.contains ht.2⟩,hi⟩
  · intro hn
    rw [d.cartan_eq_cubic_of_exponent_eq_two h c hn]
    exact ((d.cubic_le.trans inf_le_right).trans a.contains).trans K.le_normalizer

/-- The characteristic member produced on the nonblock right side has
its full normalizer in the maximal component normalizer, once the original
Cartan normalizes Baum(T). The escaping cubic gives the necessary generation. -/
theorem LocalA7Configuration.right_nonblock_characteristic_control
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hnb : ¬ ChapterC.IsChiBlockIn (pResidual 2 H))
    (hAB : A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C ≠ ⊥ ∧
      K ⊔ (T : Subgroup G) ≤ normalizer
        (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
      A ≤ normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
      normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤
        normalizer (K : Set G) := by
  have ht : (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hz : W = ⊥ := bot_unique (h.reduced_le_sylow.trans_eq he)
    exact h.noncentral (by rw [hz,commutator_bot_left])
  obtain ⟨P,hP⟩ := ChapterC.RankOne.ChiProduct.SelectedRankOne.exists_baumann_universal_pair.{u,u}
    (T : Subgroup G) T.isPGroup' ht
  have hHC := (a.right_characteristic_or_block h hH hgen c d P hP).resolve_right hnb
  let := P.second_characteristic
  have hAC := hAB.trans (normalizer_le_normalizer_characteristic_image _ P.second)
  have hKC : K ⊔ (T : Subgroup G) ≤ normalizer
      (P.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) := by
    rw [←a.cubic_sup_right h hH hgen c d]
    exact sup_le hHC ((d.cubic_le.trans inf_le_left).trans hAC)
  refine ⟨P.second,P.second_characteristic,P.second_ne_bot,hKC,hAC,?_⟩
  have hq := ((T.isPGroup'.to_le (show ChapterB.baumann (T : Subgroup G) ≤ T from inf_le_left)).to_subgroup
    P.second).map (ChapterB.baumann (T : Subgroup G)).subtype
  have hne : P.second.map (ChapterB.baumann (T : Subgroup G)).subtype ≠ ⊥ := by
    intro hh
    exact P.second_ne_bot ((P.second.map_eq_bot_iff_of_injective
      (ChapterB.baumann (T : Subgroup G)).subtype_injective).mp hh)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T a.maximal
  have he : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl
      a.sylow_normalizes) (le_componentOrbit K T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → K ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (K : Set G) := by
    simpa only [he] using hu.normalizer_unique
  exact normalizer_le_of_unique_maximalTwoLocal huniq hq hne hKC

/-- The source's nonblock characteristic route forces degree two under
the remaining Cartan–Baumann normalization premise. -/
theorem LocalA7Configuration.degree_two_of_right_nonblock
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hnb : ¬ ChapterC.IsChiBlockIn (pResidual 2 H))
    (hAB : A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) : n = 2 := by
  obtain ⟨C,_,_,_,hAC,hCK⟩ := a.right_nonblock_characteristic_control h hH hgen c d hnb hAB
  exact (a.cartan_normalizes_iff_degree_two h c d).mp (hAC.trans hCK)

/-- The literal universal inputs enter the torus reduction through the
proved FF configuration producer. No altered Sylow or chosen module is used. -/
theorem localCartan_noncentral_degree_two_of_right_nonblock
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T)
    (hnb : ¬ ChapterC.IsChiBlockIn (pResidual 2 H))
    (hAB : A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) : n = 2 := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact a.degree_two_of_right_nonblock h hH hgen c d hnb hAB

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
