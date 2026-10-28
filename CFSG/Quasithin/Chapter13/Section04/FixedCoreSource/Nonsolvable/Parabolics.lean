module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Uniqueness
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CentralizerModule
public import CFSG.Quasithin.Chapter13.Section03.LocalSteps
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Theory.Representation.BinaryPermutation.SixCoreSylowFixed

/-!
# Selecting parabolics at the original escaping involutions

Transport the A₆ Sylow fixed-space bound through the literal L/O₂,Z(L)
marking. Thus V∩Ω₁Z(T) has at most four elements, without an extra rank
hypothesis. An escaping involution and the constant vector force equality.
Every subgroup of its centralizer outside M fixes exactly its line in this
four-group: fixing the constant vector would put the subgroup in M.

Finite descent now constructs a member of H*(T,M) inside the actual full
centralizer. The earlier Sylow-normalizer containment makes it a minimal
parabolic, and condition (E) supplies characteristic two. The construction
works separately for every escaping choice; it assumes no solvability of
its centralizer. It does not yet identify this parabolic as the unique one
in 13.4.10(7), or construct the component K and the amalgam alternatives.
Those remain with qt-d-1341-nonsolvable-source. Earlier structural and
Sylow-normalizer inputs retain final discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, 13.4.10(5),(7) and 13.4.12, printed pp.907–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {D : ChosenModule T L V}
namespace CoreMarking

/-- The original Sylow fixed subgroup embeds in the marked A₆ Sylow fixed space. -/
theorem sylow_fixed_card_le_four (m : CoreMarking D) :
    Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ 4 := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨R, hR⟩ := (T.subtype le_sup_right).exists_subgroupOf_eq_of_normal X
  let eL : X ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  let P := R.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have hP : ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
    rintro l ⟨r, hr, rfl⟩
    rw [hR] at hr
    exact hr
  let q : L →* alternatingGroup (Fin 6) := m.quotient.toMonoidHom.comp
    (QuotientGroup.mk' (centralCore L))
  have hq : Function.Surjective q :=
    m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  let f : (V ⊓ centralizer (T : Set G) : Subgroup G) →
      fixedSpace (BinaryPermutation.alternatingCoreRepresentation (Fin 6))
        (S : Subgroup (alternatingGroup (Fin 6))) := fun v =>
    ⟨(m.coordinate ⟨v.val, v.property.1⟩).toAdd, by
      intro a
      obtain ⟨l, hl, he⟩ := a.property
      have hc : V.normalizerMonoidHom ⟨l.val, D.normalizes l.property⟩
          ⟨v.val, v.property.1⟩ = ⟨v.val, v.property.1⟩ := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (v.property.2 l (hP l hl))
      have hh := m.equivariant l ⟨v.val, v.property.1⟩
      rw [hc] at hh
      exact (congrArg (fun b : alternatingGroup (Fin 6) =>
        BinaryPermutation.alternatingCoreRepresentation (Fin 6) b
          (m.coordinate ⟨v.val, v.property.1⟩).toAdd) he.symm).trans hh.symm⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun x : V => x.val)
      (m.coordinate.injective (Multiplicative.toAdd.injective (congrArg Subtype.val he))))
  exact (Nat.card_le_card_of_injective f hf).trans
    (BinaryPermutation.SixCoreSylow.card_fixed_le_four S)

/-- The literal V∩Ω₁Z(T) has order at most four. -/
theorem central_four_card_le (m : CoreMarking D) :
    Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) ≤ 4 := by
  apply (Nat.card_le_card_of_injective
    (inclusion (show V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      V ⊓ centralizer (T : Set G) from fun _ hx =>
        ⟨hx.1, (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx.2 |>.2.2⟩))
    (inclusion_injective _)).trans m.sylow_fixed_card_le_four

/-- The marked fixed generator belongs to the original central seed. -/
theorem constant_mem_central_four (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    m.constant.val ∈ V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
  refine ⟨m.constant.property, (mem_omega_iff (D := D) m.constant).mpr ?_⟩
  intro t ht
  exact (normalizer_component_le_fixed_centralizer h structural D m
    (D.sylow_normalizes_component ht) m.constant.val
    ⟨m.constant.property, m.constant_fixed⟩).symm

/-- An outside subgroup of C_G(z) fixes exactly the line generated by z in V∩Ω₁Z(T). -/
theorem central_four_fixed_of_escape (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (P : Subgroup G) (hPz : P ≤ centralizer ({z.val} : Set G))
    (hPM : ¬ P ≤ normalizer (L : Set G)) :
    (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (P : Set G) = zpowers z.val := by
  let Z := V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let W := Z ⊓ centralizer (P : Set G)
  have hd := m.constant_mem_central_four h structural
  have hdW : m.constant.val ∉ W := by
    intro hh
    apply hPM
    rw [← fixed_generator_centralizer h structural D m
      ⟨m.constant.property, m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    intro p hp
    exact mem_centralizer_singleton_iff.mpr (hh.2 p hp)
  have hWlt : Nat.card W < 4 := by
    by_contra! hcard
    have he : W = Z := eq_of_le_of_card_ge inf_le_left
      (m.central_four_card_le.trans hcard)
    exact hdW (he ▸ hd)
  have hpW : IsPGroup 2 W := T.isPGroup'.to_le
    ((inf_le_left.trans inf_le_left).trans D.le_sylow)
  have hWcard : Nat.card W ≤ 2 := by
    rcases hpW.card_eq_or_dvd with he | hd
    · omega
    · omega
  have hzW : z.val ∈ W := ⟨⟨z.property, hzT⟩,
    fun p hp => mem_centralizer_singleton_iff.mp (hPz hp)⟩
  have hline : zpowers z.val ≤ W := zpowers_le.mpr hzW
  have hc : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
      (fun he => hz1 (Subtype.ext he))
  exact (eq_of_le_of_card_ge hline (hc ▸ hWcard)).symm

/-- An actual escaping involution forces the central seed in V to have order four. -/
theorem central_four_card_eq_four (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) = 4 := by
  let Z := V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let A := zpowers z.val
  have hAZ : A ≤ Z := zpowers_le.mpr ⟨z.property, hzT⟩
  have hAc : Nat.card A = 2 := by
    rw [Nat.card_zpowers]
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
      (fun he => hz1 (Subtype.ext he))
  have hd := m.constant_mem_central_four h structural
  have hnot : ¬ Z ≤ A := by
    intro hZA
    have he := m.central_four_fixed_of_escape h structural z hz1 hzT
      (centralizer ({z.val} : Set G)) le_rfl hzout
    have hdA := hZA hd
    change m.constant.val ∈ zpowers z.val at hdA
    rw [← he] at hdA
    apply hzout
    rw [← fixed_generator_centralizer h structural D m
      ⟨m.constant.property, m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun p hp => mem_centralizer_singleton_iff.mpr (hdA.2 p hp)
  have hm : Nat.card A * A.relIndex Z = Nat.card Z := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hAZ).toEquiv]
    exact (A.subgroupOf Z).card_mul_index
  have hi : A.relIndex Z ≠ 1 := fun he => hnot ((relIndex_eq_one).mp he)
  have hp := Nat.card_pos (α := Z)
  have hu := m.central_four_card_le
  rw [hAc] at hm
  change Nat.card Z ≤ 4 at hu
  change Nat.card Z = 4
  omega

end CoreMarking

namespace Nonsolvable

/-- Distinct central choices have parabolics that do not centralize one
another's chosen involution. This gives the strict centralizer premise in
the pair application of 13.4.7. -/
theorem parabolic_not_le_other_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z w : V) (hz1 : z ≠ 1) (hw1 : w ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hne : w ≠ z) (P : Subgroup G)
    (hPz : P ≤ centralizer ({z.val} : Set G))
    (hPM : ¬ P ≤ normalizer (L : Set G)) :
    ¬ P ≤ centralizer ({w.val} : Set G) := by
  classical
  intro hPw
  have hw : w.val ∈ (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (P : Set G) :=
    ⟨⟨w.property, hwT⟩, fun p hp => mem_centralizer_singleton_iff.mp (hPw hp)⟩
  rw [m.central_four_fixed_of_escape h structural z hz1 hzT P hPz hPM] at hw
  let := D.elementary
  have ho : orderOf z.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
    (fun he => hz1 (Subtype.ext he))
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hw
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hw
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact hw1 (Subtype.ext (by simpa using he.symm))
  · exact hne (Subtype.ext (by simpa using he.symm))

/-- Select an actual minimal parabolic inside C_G(z), with its fixed line and intrinsic characteristic-two bound. -/
theorem exists_escape_parabolic
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T P ∧
      P ≤ centralizer ({z.val} : Set G) ∧
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
        centralizer (P : Set G) = zpowers z.val ∧
      centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
  have ho : orderOf z.val = 2 := by
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
      (fun he => hz1 (Subtype.ext he))
  obtain ⟨P, hP, hPz⟩ := Section03.exists_HStar_le_involution_centralizer
    (T : Subgroup G) (normalizer (L : Set G)) z.val ho
    (Solvable.original_sylow_le_centralizer hzT) hzout
  exact ⟨P, hP, Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hP
      (Or.inl hNT), hPz,
    m.central_four_fixed_of_escape h structural z hz1 hzT P hPz hP.1.2,
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T)
      hP.1.1)⟩

/-- The already proved comparison now yields uniqueness and rank without
assuming a separate bound on the central four-group. Universal nonsolvability
is still supplied at each of the two escaping choices. -/
theorem unique_escape_and_rank_of_marked_comparisons
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (L₂ : Subgroup G)
    (hnonsolvable : ∀ v : V,
      v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      v.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({v.val} : Set G)))
    (comparisons : ∀ v w : V,
      v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      m.weight v = 2 → m.weight w = 4 →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({v.val} : Set G)) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)) →
      Nonempty (ParabolicComparison T (normalizer (L : Set G)) L₂
        (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) v.val w.val))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    (∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z) ∧
      3 ≤ ChapterE.globalR V :=
  unique_escape_and_rank_of_comparisons h structural m L₂ m.central_four_card_le
    hnonsolvable comparisons z hz1 hzT hzout

end Nonsolvable
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
