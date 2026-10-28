module
public import Theory.Representation.BinaryPermutation.SixCoreWeightTwo
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CosetGraph
/-!
# The rank-one returning conjugate in original 13.4.17

Weight-two displacements force an elementary permutation actor to move the
original augmentation core along one line. Apply this to the noncommuting
conjugate constructed by the actual two-type graph. Equal-weight conjugacy
in L moves its commutator to the original escaping point z; normalizer
fusion then replaces the conjugator by an element of C_G(z), preserving
both the subgroup and its containment in N_G(L).

The source application constructs the graph and discharges the weight and
mutual-normalization premises from the retained earlier-source inputs. It
proves 13.4.17(2). Excluding the component's five-dimensional row and
constructing the terminal moving actor remain separate source obligations.
Source: Aschbacher–Smith 13.4.17, printed p.914, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal original commutator is a weight-two line. -/
theorem core_weight_two_commutator_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAM : A ≤ normalizer (L : Set G))
    (hw : ∀ v : V, v.val ∈ ⁅V,A⁆ → v ≠ 1 → m.weight v = 2)
    (hm : ⁅V,A⁆ ≠ ⊥) :
    ∃ w : V, m.weight w = 2 ∧ ⁅V,A⁆ = zpowers w.val := by
  let := D.elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,hq,_,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hAM)
  have hf (a : A) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨a.val,(hAM.trans hn) a.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (f a) (m.coordinate v).toAdd :=
    hq (inclusion hAM a) v
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hdispl (a : A) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨a.val,(hAM.trans hn) a.property⟩ v * v⁻¹)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (f a) (m.coordinate v).toAdd -
          (m.coordinate v).toAdd := by
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    exact congrArg (fun x => x - (m.coordinate v).toAdd) (hf a v)
  have hweights : ∀ a ∈ f.range, ∀ v : BinaryPermutation.core (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a v ≠ v →
      BinaryPermutation.wordWeight (BinaryPermutation.coreRepresentation (Fin 6) a v - v).val = 2 := by
    rintro _ ⟨a,rfl⟩ v hv
    let w := m.coordinate.symm (Multiplicative.ofAdd v)
    let c : V := V.normalizerMonoidHom ⟨a.val,(hAM.trans hn) a.property⟩ w * w⁻¹
    have hc : (m.coordinate c).toAdd = BinaryPermutation.coreRepresentation (Fin 6) (f a) v - v := by
      simpa only [w,m.coordinate.apply_symm_apply,toAdd_ofAdd] using hdispl a w
    have hcV : c.val ∈ ⁅V,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator a.property w.property
    have hc1 : c ≠ 1 := by
      intro he
      rw [he,map_one] at hc
      exact hv (sub_eq_zero.mp hc.symm)
    have hh := hw c hcV hc1
    change BinaryPermutation.wordWeight (m.coordinate c).toAdd.val = 2 at hh
    rwa [hc] at hh
  have hne : f.range ≠ ⊥ := by
    intro he
    have hcard := model_card_range A V (hAM.trans hn)
      (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
      f m.coordinate hf
    rw [inf_relIndex_left,he,card_bot] at hcard
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (relIndex_eq_one.mp hcard.symm)))
  obtain ⟨c,hcw,hc⟩ := BinaryPermutation.SixCoreWeightTwo.common_displacement f.range hne hweights
  let w := m.coordinate.symm (Multiplicative.ofAdd c)
  have hwc : (m.coordinate w).toAdd = c := m.coordinate.apply_symm_apply _
  have hw2 : m.weight w = 2 := by change BinaryPermutation.wordWeight (m.coordinate w).toAdd.val = 2; rwa [hwc]
  have hline : ⁅V,A⁆ ≤ zpowers w.val := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha v hv
    let d : V := V.normalizerMonoidHom ⟨a,(hAM.trans hn) ha⟩ ⟨v,hv⟩ * (⟨v,hv⟩ : V)⁻¹
    have hd := hdispl ⟨a,ha⟩ ⟨v,hv⟩
    rcases hc (f ⟨a,ha⟩) ⟨⟨a,ha⟩,rfl⟩ (m.coordinate ⟨v,hv⟩).toAdd with he | he
    · have hd1 : d = 1 := by
        apply m.coordinate.injective
        change (m.coordinate d).toAdd = (m.coordinate 1).toAdd
        rw [map_one]
        exact hd.trans he
      change d.val ∈ zpowers w.val
      rw [hd1]
      exact one_mem _
    · have hdw : d = w := m.coordinate.injective ((hd.trans he).trans hwc.symm)
      change d.val ∈ zpowers w.val
      rw [hdw]
      exact mem_zpowers _
  have hw1 : w.val ≠ 1 := by
    intro he
    have hew : w = 1 := Subtype.ext he
    rw [hew] at hw2
    change BinaryPermutation.wordWeight (m.coordinate 1).toAdd.val = 2 at hw2
    rw [map_one] at hw2
    have hh : BinaryPermutation.wordWeight (0 : BinaryPermutation.core (Fin 6)).val = 0 := by decide
    change BinaryPermutation.wordWeight (0 : BinaryPermutation.core (Fin 6)).val = 2 at hw2
    omega
  have hcard : Nat.card (zpowers w.val) = 2 := by
    have horder : orderOf w.val = 2 := orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian _ w.property,hw1⟩
    rw [Nat.card_zpowers,horder]
  refine ⟨w,hw2,eq_of_le_of_card_ge hline ?_⟩
  rw [hcard]
  exact (one_lt_card_iff_ne_bot _).mpr hm

/-- Rank one and the literal centralizer transporter for any noncommuting
mutually normalizing returning conjugate with weight-two intersection. -/
theorem weight_two_returning_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hz1 : z ≠ 1) (hwz : m.weight z = 2)
    (g : G) (hAM : V.conjBy g ≤ normalizer (L : Set G))
    (hcomm : ⁅V,V.conjBy g⁆ ≤ V ⊓ V.conjBy g)
    (hm : ⁅V,V.conjBy g⁆ ≠ ⊥)
    (hw : ∀ v : V, v ≠ 1 → v.val ∈ V.conjBy g → m.weight v = 2) :
    ∃ c ∈ centralizer ({z.val} : Set G),
      ⁅V,V.conjBy c⁆ = zpowers z.val ∧ z.val ∈ V.conjBy c ∧
      V.conjBy c ≤ normalizer (L : Set G) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy g) := IsElementaryAbelian.map _
  obtain ⟨w,hw2,he⟩ := core_weight_two_commutator_line h structural D m
    (V.conjBy g) hAM (fun v hv hv1 => hw v hv1 (hcomm hv).2) hm
  obtain ⟨l,hl,hlw⟩ := m.exists_conjugator_of_weight_eq w z (hw2.trans hwz.symm)
  have hlV : V.conjBy l = V := mem_normalizer_iff_map_conj_eq.mp (D.normalizes hl)
  have hc : ⁅V,V.conjBy (l*g)⁆ = zpowers z.val := by
    have hh := congrArg (fun X : Subgroup G => X.conjBy l) he
    change (⁅V,V.conjBy g⁆).map (MulAut.conj l).toMonoidHom =
      (zpowers w.val).map (MulAut.conj l).toMonoidHom at hh
    rw [map_commutator,MonoidHom.map_zpowers] at hh
    change ⁅V.conjBy l,(V.conjBy g).conjBy l⁆ = zpowers (MulAut.conj l w.val) at hh
    rwa [hlV,conjBy_conjBy,hlw] at hh
  have hz : z.val ∈ V.conjBy (l*g) := by
    have hwmem : w.val ∈ V.conjBy g := (hcomm (he.symm ▸ mem_zpowers w.val)).2
    rw [conjBy_mul]
    exact ⟨w.val,hwmem,hlw⟩
  obtain ⟨c,hcC,hcV⟩ := (element_fusion_iff_centralizer_incidence V z.val).mp
    (hfusion z hz1) (l*g) hz
  have hNM : V.conjBy (l*g) ≤ normalizer (L : Set G) := by
    rw [conjBy_mul]
    exact (map_mono hAM).trans (mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (L : Set G)).le_normalizer (L.le_normalizer hl))).le
  exact ⟨c,hcC,hcV.symm ▸ hc,hcV.symm ▸ hz,hcV.symm ▸ hNM⟩
open Stellmacher Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- Original 13.4.17(2), applied to the actual two-type graph pair. Universal
escaping nonsolvability and both genuine amalgam inputs are retained. -/
theorem escaping_original_rank_one_return
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (hpair1347 : PairAmalgamSource1347 T)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    m.weight z = 2 ∧ 3 ≤ ChapterE.globalR V ∧
    ∃ g ∈ centralizer ({z.val} : Set G),
      ⁅V,V.conjBy g⁆ = zpowers z.val ∧ z.val ∈ V.conjBy g ∧
      V.conjBy g ≤ normalizer (L : Set G) := by
  obtain ⟨hw2,hr,hw,K,hK,hfK,hHN,hKM,model,W,hW,hTW,P,hP,hPH,eP,eB,
    hlocal,hXM,hXH,hmixed,hlin,hsecond,he,hcard,hF,hSoc,g,hg,hgout,hg₁,hg₂,hgc,hcomm⟩ :=
    escaping_original_graph_pair hl h₀ h structural modules D m h1332 fixed five covered
      h13316 hindex hM h1347 hpair1347 h1338 hfusion hnonsolvable z hz1 hzT hzout
  refine ⟨hw2,hr,?_⟩
  apply weight_two_returning_centralizer h structural D m hfusion z hz1 hw2 g
    (hg₁.trans ((pCoreIn_le 2 _).trans ?_)) hcomm hgc (hw g hgout)
  rw [hM]
  exact inf_le_left

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
