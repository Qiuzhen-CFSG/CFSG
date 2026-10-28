module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Labels.BaseEndpoints
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.BaseOpposite

/-!
# The next original parabolic across the second source reflection

The actual reflection fixes u and its fixed five. Uniqueness of that
five's parabolic label therefore fixes the u-colored endpoint. Its inverse
carries the original first endpoint to a zu-colored neighbor containing
the next five. This is different from the existing zu endpoint: otherwise
the literal opposite SL2(5), of order120, would lie in a parabolic of
order20480. No closure of a chosen set of five-subgroups is used.
Source: the parabolic hexagon argument of J.4.10, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)
  (c : Choices d) (e : first ≃* p.F₁ B5) (hz : (e modelZ : G)=c.z)
  (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
  {D : Type*} [Group D] (q : Completion D) (f : D →* G)
  (hleft : ∀ a : first,f (q.left a)=(e a : G))

/-- Every actual colored parabolic has the order of the original first endpoint. -/
theorem color_member_card {v : G} {E : Subgroup G}
    (hE : E ∈ colorFamily p B5 c.z (sourceU e) v) : Nat.card E=20480 := by
  obtain ⟨g,rfl,_,_⟩ := hE
  change Nat.card ((p.F₁ B5).map (MulAut.conj g).toMonoidHom)=20480
  rw [card_map_of_injective (MulAut.conj g).injective,←Nat.card_congr e.toEquiv,first_card]

include hz hfive q f hleft in
/-- The literal opposite SL2(5) cannot lie in any original colored parabolic. -/
theorem opposite_pair_not_le_color {v : G} {E : Subgroup G}
    (hE : E ∈ colorFamily p B5 c.z (sourceU e) v) :
    ¬oppositePair c B5 (sourceU e)≤E := by
  obtain ⟨hu,hI⟩ := source_inverter c B5 e hz hfive
  obtain ⟨a⟩ := opposite_pair_equiv_SL2 c B5 (sourceU e) hu
    (PathTransport.source_fusion q c e f hleft hz) hI
  intro hle
  have hh := card_dvd_of_le hle
  rw [Theory.SpecificGroups.SL2.PermutationFiveImage.card_source a,
    color_member_card p B5 c e hE] at hh
  norm_num at hh

private theorem fixed_of_card_two {X : Type*} (hcard : Nat.card X=2)
    (a : X) (f : X → X) (hf : Function.Injective f) (ha : f a=a) (x : X) : f x=x := by
  obtain ⟨b,_,hb⟩ := (Nat.card_eq_two_iff' a).mp hcard
  by_cases hxa : x=a
  · subst x; exact ha
  · have hfa : f x≠a := fun hh => hxa (hf (hh.trans ha.symm))
    exact (hb _ hfa).trans (hb _ hxa).symm

include s hi hz hfive q f hleft

/-- For the actual second source reflection, the inverse-conjugate first
endpoint is a new zu-colored neighbor of the fixed u endpoint. -/
theorem inverse_reflection_neighbor
    (t : G) (htu : t*sourceU e*t⁻¹=sourceU e) (htz : t*c.z*t⁻¹=sourceU e*c.z)
    (htB : t ∈ normalizer (fixedFive B5 (sourceU e) : Set G))
    (Eu Ezu : globalFamily p B5 c.z (sourceU e))
    (hEu : (Eu : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (sourceU e))
    (hEzu : (Ezu : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (c.z*sourceU e))
    (hBu : fixedFive B5 (sourceU e)≤Eu) (hBzu : fixedFive B5 (c.z*sourceU e)≤Ezu)
    (hAdj : (sourceGraph p B5 c.z (sourceU e)).Adj (baseVertex p B5 c e hz) Eu) :
    ∃ Et : globalFamily p B5 c.z (sourceU e),
      (Et : Subgroup G)=(p.F₁ B5).conjBy t⁻¹ ∧
      (Et : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) ∧
      nextFive c B5 (sourceU e)≤Et ∧ Et≠Ezu ∧
      (Eu : Subgroup G).conjBy t⁻¹=Eu ∧
      (∀ E ∈ colorFamily p B5 c.z (sourceU e) (sourceU e), E.conjBy t⁻¹=E) ∧
      (sourceGraph p B5 c.z (sourceU e)).Adj Eu Et := by
  obtain ⟨_,_,_,hcomm⟩ := source_pair_marks p B5 c e hz
  have hu2 := (source_involution_marks c e hz).1
  have htzu : t*(c.z*sourceU e)*t⁻¹=c.z := by
    calc
      _ = (t*c.z*t⁻¹)*(t*sourceU e*t⁻¹) := by group
      _ = (sourceU e*c.z)*sourceU e := by rw [htz,htu]
      _ = c.z := by rw [←hcomm.eq,mul_assoc,←pow_two,hu2,mul_one]
  have htiu : t⁻¹*sourceU e*(t⁻¹)⁻¹=sourceU e := by
    calc
      _ = t⁻¹*(t*sourceU e*t⁻¹)*t := by rw [htu,inv_inv]
      _ = sourceU e := by group
  have htiz : t⁻¹*c.z*(t⁻¹)⁻¹=c.z*sourceU e := by
    calc
      _ = t⁻¹*(t*(c.z*sourceU e)*t⁻¹)*t := by rw [htzu,inv_inv]
      _ = c.z*sourceU e := by group
  have htN : t⁻¹ ∈ normalizer (pairSpan c.z (sourceU e) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [pairSpan,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
      apply sup_le
      · apply zpowers_le.mpr
        change t⁻¹*c.z*(t⁻¹)⁻¹ ∈ zpowers c.z ⊔ zpowers (sourceU e)
        rw [htiz]
        exact mul_mem_sup (mem_zpowers c.z) (mem_zpowers (sourceU e))
      · apply zpowers_le.mpr
        change t⁻¹*sourceU e*(t⁻¹)⁻¹ ∈ zpowers c.z ⊔ zpowers (sourceU e)
        rw [htiu]
        exact mem_sup_right (mem_zpowers (sourceU e))
    · rw [card_map_of_injective (MulAut.conj t⁻¹).injective]
  have hEm : (p.F₁ B5).conjBy t⁻¹ ∈
      colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) := by
    have hh := color_conjugate_mem p B5 c.z (sourceU e) t⁻¹ htN (first_mem_color p B5 c e hz)
    rwa [htiz] at hh
  let Et : globalFamily p B5 c.z (sourceU e) :=
    ⟨(p.F₁ B5).conjBy t⁻¹,c.z*sourceU e,by simp [colors],hEm⟩
  have hB0 : B5Image B5≤p.F₁ B5 := by
    rw [←hfive]
    rintro x ⟨a,_,rfl⟩
    exact (e a).property
  have hnext : nextFive c B5 (sourceU e)≤Et := by
    have hh := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hB0
    change (B5Image B5).conjBy t⁻¹≤(p.F₁ B5).conjBy t⁻¹ at hh
    rw [←nextFive_conj_reflection c B5 e hz hfive
      (PathTransport.source_fusion q c e f hleft hz) t htB htu htz,conjBy_inv] at hh
    exact hh
  have hEuFixed : (Eu : Subgroup G).conjBy t⁻¹=Eu := by
    have hEum := color_conjugate_mem p B5 c.z (sourceU e) t⁻¹ htN hEu
    rw [htiu] at hEum
    have hBm : fixedFive B5 (sourceU e)≤(Eu : Subgroup G).conjBy t⁻¹ := by
      have hh := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hBu
      have he : (fixedFive B5 (sourceU e)).map (MulAut.conj t⁻¹).toMonoidHom=
          fixedFive B5 (sourceU e) := mem_normalizer_iff_map_conj_eq.mp (inv_mem htB)
      rwa [he] at hh
    obtain ⟨hu,hI⟩ := source_inverter c B5 e hz hfive
    have hcard := (source_three_fives c B5 (sourceU e) hu
      (PathTransport.source_fusion q c e f hleft hz) hI).1
    exact color_members_eq_of_five p s B5 hi c e hEum hEu hcard hBm hBu
  have hne : Et≠Ezu := by
    intro hh
    have hn : nextFive c B5 (sourceU e)≤Ezu := (congrArg Subtype.val hh) ▸ hnext
    exact opposite_pair_not_le_color p B5 c e hz hfive q f hleft hEzu (sup_le hBzu hn)
  have hall : ∀ E ∈ colorFamily p B5 c.z (sourceU e) (sourceU e), E.conjBy t⁻¹=E := by
    let φ : colorFamily p B5 c.z (sourceU e) (sourceU e) →
        colorFamily p B5 c.z (sourceU e) (sourceU e) := fun E => ⟨E.val.conjBy t⁻¹,by
      have hh := color_conjugate_mem p B5 c.z (sourceU e) t⁻¹ htN E.property
      rwa [htiu] at hh⟩
    have hinj : Function.Injective φ := by
      intro E F hEF
      apply Subtype.ext
      have hh := congrArg (fun H : Subgroup G => H.conjBy t) (congrArg Subtype.val hEF)
      change (E.val.conjBy t⁻¹).conjBy t=(F.val.conjBy t⁻¹).conjBy t at hh
      simpa only [conjBy_inv'] using hh
    have hc := source_color_family_card q p s c B5 hi e f hleft hz hfive (sourceU e) (by simp [colors])
    intro E hE
    exact congrArg Subtype.val (fixed_of_card_two hc ⟨Eu,hEu⟩ φ hinj (Subtype.ext hEuFixed) ⟨E,hE⟩)
  refine ⟨Et,rfl,hEm,hnext,hne,hEuFixed,hall,?_⟩
  have hm := (sourceGraph_action p B5 c e hz ⟨t⁻¹,htN⟩ (baseVertex p B5 c e hz) Eu).mpr hAdj
  have he0 : (normalizerAction p B5 c e hz).smul ⟨t⁻¹,htN⟩ (baseVertex p B5 c e hz)=Et := rfl
  have heu : (normalizerAction p B5 c e hz).smul ⟨t⁻¹,htN⟩ Eu=Eu := Subtype.ext hEuFixed
  rw [he0,heu] at hm
  exact hm.symm

/-- A genuine source reflection extends the two original base edges by a
third edge to the other parabolic of the zu color. -/
theorem source_three_edge_path :
    ∃ (t : G) (Eu Ezu Et : globalFamily p B5 c.z (sourceU e)),
      t ∈ normalizer (sourceI e : Set G) ∧
      t*sourceU e*t⁻¹=sourceU e ∧ t*c.z*t⁻¹=sourceU e*c.z ∧
      (Eu : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (sourceU e) ∧
      (Ezu : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) ∧
      (Et : Subgroup G) ∈ colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) ∧
      fixedFive B5 (sourceU e)≤Eu ∧ fixedFive B5 (c.z*sourceU e)≤Ezu ∧
      nextFive c B5 (sourceU e)≤Et ∧
      (Et : Subgroup G)=(p.F₁ B5).conjBy t⁻¹ ∧
      (Eu : Subgroup G).conjBy t⁻¹=Eu ∧
      (∀ E ∈ colorFamily p B5 c.z (sourceU e) (sourceU e), E.conjBy t⁻¹=E) ∧ Et≠Ezu ∧
      (sourceGraph p B5 c.z (sourceU e)).Adj (baseVertex p B5 c e hz) Eu ∧
      (sourceGraph p B5 c.z (sourceU e)).Adj (baseVertex p B5 c e hz) Ezu ∧
      (sourceGraph p B5 c.z (sourceU e)).Adj Eu Et := by
  obtain ⟨Eu,Ezu,hEu,hEzu,hBu,hBzu,_,hAdj,hAdjzu⟩ :=
    source_base_neighbor_endpoints p s B5 hi c e hz hfive q f hleft
  obtain ⟨_,t,_,ht,_,_,htu,htz,_,htB⟩ := source_two_transvections q c B5 e f hleft hz hfive
  obtain ⟨Et,he,hEt,hnext,hne,hfix,hall,hAdjt⟩ :=
    inverse_reflection_neighbor p s B5 hi c e hz hfive q f hleft t htu htz htB
      Eu Ezu hEu hEzu hBu hBzu hAdj
  exact ⟨t,Eu,Ezu,Et,ht,htu,htz,hEu,hEzu,hEt,hBu,hBzu,hnext,he,hfix,hall,hne,hAdj,hAdjzu,hAdjt⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
