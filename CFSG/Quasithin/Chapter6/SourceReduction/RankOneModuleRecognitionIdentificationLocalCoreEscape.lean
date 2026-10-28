module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCoreGeometry
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Transporting the terminal pair in the core exclusion

The natural SL₂ action is transitive on nonidentity layer elements. Transport
a point-centralizer core containment simultaneously with that point and its
layer. If a second conjugate centralizes this point, its join with the first
layer lies in a two-group whenever the first layer lies in the centralizer
core. Thus a non-two pair contradicts the original marked core containment.

This proves the final conjugacy step of 6.2.8 and applies it to the actual
core count, leaving orders four and eight. Constructing the pair by the
field-plane graph argument and excluding order four by 6.2.11 remain required.
No later recognition or LocalAnalysis witness is used.

Source: Aschbacher--Smith, 6.2.8, final paragraph, printed p.685.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem natural_point_transporter {B : Subgroup G}
    (hnatural : IsNaturalModule L B n) {v w : G}
    (hv : v ∈ B) (hw : w ∈ B) (hvne : v ≠ 1) (hwne : w ≠ 1) :
    ∃ l ∈ L, l * v * l⁻¹ = w := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  have hfv : (f ⟨v, hv⟩).toAdd ≠ 0 := by
    intro hh
    apply hvne
    exact congrArg Subtype.val (f.injective
      ((Multiplicative.toAdd.injective hh).trans (map_one f).symm))
  have hfw : (f ⟨w, hw⟩).toAdd ≠ 0 := by
    intro hh
    apply hwne
    exact congrArg Subtype.val (f.injective
      ((Multiplicative.toAdd.injective hh).trans (map_one f).symm))
  obtain ⟨a, ha⟩ := Matrix.SL2.exists_mulVec_eq F _ _ hfv hfw
  obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) a
  change e (QuotientGroup.mk' (pCore 2 L) l) = a at hl
  refine ⟨l, l.property, ?_⟩
  have he := hf l ⟨v, hv⟩
  change (f.symm (Multiplicative.ofAdd
    (Matrix.mulVec (e (QuotientGroup.mk' (pCore 2 L) l)).val (f ⟨v, hv⟩).toAdd)) : G) =
    (l : G) * v * (l : G)⁻¹ at he
  rw [hl, ha] at he
  change (f.symm (f ⟨w, hw⟩) : G) = (l : G) * v * (l : G)⁻¹ at he
  rw [f.symm_apply_apply] at he
  exact he.symm

omit [Finite G] in
private theorem map_point_centralizer (g v : G) :
    (centralizer ({v} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * v * g⁻¹} : Set G) := by
  simpa only [Set.image_singleton, MulAut.conj_apply] using
    map_centralizer_equiv ({v} : Set G) (MulAut.conj g)

omit [Finite G] in
/-- Natural point transitivity transports core containment simultaneously
with the layer and the marked involution. This is the last conjugacy step
of source 6.2.8; neither the original nor the conjugate layer is replaced. -/
theorem local_conjugate_layer_le_point_core
    (hnatural : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ layer L R) (hz1 : z ≠ 1)
    (hcore : layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (g : G) {w : G} (hw : w ∈ (layer L R).map (MulAut.conj g).toMonoidHom)
    (hw1 : w ≠ 1) :
    (layer L R).map (MulAut.conj g).toMonoidHom ≤
      (centralizer ({w} : Set G)).pCoreIn 2 := by
  obtain ⟨v, hv, rfl⟩ := hw
  have hv1 : v ≠ 1 := by intro he; simp [he] at hw1
  obtain ⟨l, hl, he⟩ := natural_point_transporter hnatural hz hv hz1 hv1
  have hnL : L ≤ normalizer (layer L R : Set G) := by
    obtain ⟨F, _, _, _, _, hm⟩ := hnatural
    exact hm.normalizes
  have hlB : (layer L R).map (MulAut.conj l).toMonoidHom = layer L R :=
    mem_normalizer_iff_map_conj_eq.mp (hnL hl)
  have hh := map_mono (f := (MulAut.conj l).toMonoidHom) hcore
  rw [hlB, map_pCoreIn_of_injective 2 _ _ (MulAut.conj l).injective,
    map_point_centralizer, he] at hh
  have hg := map_mono (f := (MulAut.conj g).toMonoidHom) hh
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    map_point_centralizer] at hg
  exact hg

omit [Finite G] in
/-- A non-two pair of conjugate layers fixing a nonidentity point of the
first layer contradicts core containment at the original marked point.
Only the second layer must centralize that point; its conjugator need not
fix the point. This is the precise terminal configuration in 6.2.8. -/
theorem local_layer_not_le_point_core_of_non_two_pair
    (hnatural : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ layer L R) (hz1 : z ≠ 1)
    (g c : G) {w : G} (hw : w ∈ (layer L R).map (MulAut.conj g).toMonoidHom)
    (hw1 : w ≠ 1)
    (hc : ((layer L R).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj c).toMonoidHom ≤ centralizer ({w} : Set G))
    (hpair : ¬ IsPGroup 2 ((layer L R).map (MulAut.conj g).toMonoidHom ⊔
      ((layer L R).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj c).toMonoidHom : Subgroup G)) :
    ¬ layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  intro hcore
  let A := (layer L R).map (MulAut.conj g).toMonoidHom
  let C := centralizer ({w} : Set G)
  have hAC : A ≤ C.pCoreIn 2 :=
    local_conjugate_layer_le_point_core hnatural hz hz1 hcore g hw hw1
  have hn : C ≤ normalizer (C.pCoreIn 2 : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hpA : IsPGroup 2 A := (isPGroup_pCoreIn 2 C).to_le hAC
  have hpB : IsPGroup 2 (A.map (MulAut.conj c).toMonoidHom) :=
    hpA.map (MulAut.conj c).toMonoidHom
  have hp := (isPGroup_pCoreIn 2 C).to_sup_of_normal_left' hpB (hc.trans hn)
  exact hpair (hp.to_le (sup_le_sup hAC le_rfl))

/-- The precise terminal pair supplied by the remaining graph argument
removes the order-sixteen alternative in the actual numerical count. -/
theorem local_core_card_dichotomy_of_non_two_pair
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (g c : G) {w : G} (hw : w ∈ (layer L R).map (MulAut.conj g).toMonoidHom)
    (hw1 : w ≠ 1)
    (hc : ((layer L R).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj c).toMonoidHom ≤ centralizer ({w} : Set G))
    (hpair : ¬ IsPGroup 2 ((layer L R).map (MulAut.conj g).toMonoidHom ⊔
      ((layer L R).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj c).toMonoidHom : Subgroup G)) :
    Nat.card (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4 ∨
    Nat.card (layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8 := by
  apply LocalQuotientAction.core_card_dichotomy h hnatural hz ho hT
  exact local_layer_not_le_point_core_of_non_two_pair hnatural.2.1 hz.1
    (by intro he; simp [he] at ho) g c hw hw1 hc hpair

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
