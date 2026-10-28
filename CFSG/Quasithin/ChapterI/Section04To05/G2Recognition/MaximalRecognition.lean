module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalMiddleRigidity
public import Theory.SpecificGroups.G2.TernaryEndpointShifts
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SylowNineLocal

/-!
# Recognition of the original large-core configuration

The two remaining central shifts extend across the actual Atlas endpoints.
Composing those automorphisms with the constructed original maps gives both
commuting squares on the whole order-2916 middle. All maps retain the original
core comparisons, full actors and Sylow aligner, with the displayed endpoint
corrections. The original generating completion now has the untwisted Atlas
marking. Its original endpoint involutions have orders two, two and product
six, so the proved F.4.26 theorem constructs the actual ambient isomorphism.

Thus I.4.5 is proved whenever 27 divides the original group order. The separate
strongly-three-embedded alternative, whose exclusion belongs to
qt-i45-g2-strong-three-exclusion, is retained for final I.4.5 assembly.
Chapter14Recognition applies this theorem to the literal source configuration.
Source: Aschbacher–Smith I.4.5, p.417, and F.4.26, p.288.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace AlignedCubicPair.MiddleAlignment
variable {t : CubicTorus c} {p : AlignedCubicPair t} (d : p.MiddleAlignment)

/-- Actual compatible maps to the untwisted Atlas amalgam. The hypothesis
is the proved normalized coordinate formula on the whole middle. -/
noncomputable def compatibleAtlasIso (j k : ZMod 3)
    (h : ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
      d.difference (Atlas.G2.TernaryBorel.positive v*Atlas.G2.TernaryBorel.diagonal l m)=
        Atlas.G2.TernaryBorel.positive (Atlas.G2.TernaryBorel.twistCoordinates 1 1 j k v)*
          Atlas.G2.TernaryBorel.diagonal l m) :
    RankTwoAmalgam.Iso p.amalgam (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3)) :=
  let e : RankTwoAmalgam.Iso p.amalgam (RankTwoAmalgam.twistRight
      (ChapterF.GreenBook.LieModels.G2.borelAmalgam (F:=ZMod 3)) d.difference) := {
    left := d.leftEndpointEquiv
    right := d.rightEndpointEquiv
    middle := d.leftMiddle
    left_commutes := d.left_commutes
    right_commutes b := by
      change d.rightEndpointEquiv (p.amalgam.right b)=
        inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint true) (d.difference (d.leftMiddle b))
      rw [difference,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      exact d.right_commutes b }
  (e.trans (Atlas.G2.TernaryBorel.shiftUntwistIso d.difference j k h)).trans
    (ChapterF.GreenBook.LieModels.G2.borelIso (F:=ZMod 3)).symm

/-- The corrected left map is the original constructed map followed by the
explicit central shift; its full core and actor comparisons are retained. -/
theorem compatibleAtlasIso_left (j k : ZMod 3) (h) (x : p.leftEndpoint) :
    (d.compatibleAtlasIso j k h).left x=
      Atlas.G2.TernaryLevi.endpointShift false j (d.leftEndpointEquiv x) := rfl

/-- The corrected right map retains the same original Sylow aligner. -/
theorem compatibleAtlasIso_right (j k : ZMod 3) (h) (x : p.rightEndpoint) :
    (d.compatibleAtlasIso j k h).right x=
      Atlas.G2.TernaryLevi.endpointShift true (-k) (d.rightEndpointEquiv x) := rfl

/-- The entire original middle is carried through the literal Atlas overlap equivalence. -/
theorem compatibleAtlasIso_middle (j k : ZMod 3) (h) (b : t.leftCubicBorel) :
    (d.compatibleAtlasIso j k h).middle b=
      (ChapterF.GreenBook.LieModels.G2.borelIso (F:=ZMod 3)).symm.middle
        (Atlas.G2.TernaryLevi.middleShift false j (d.leftMiddle b)) := rfl

/-- The central-shift correction fixes the actual original short core map. -/
theorem compatibleAtlasIso_left_core (j k : ZMod 3) (h) (x : p.leftCore) :
    ((d.compatibleAtlasIso j k h).left (inclusion t.cubicCore_le_normalizer x):
      Atlas.G2.Model (ZMod 3))=
      MulAut.conj (d.leftCorrection:Atlas.G2.Model (ZMod 3))
        (t.cubicAtlasShortEquiv p.core_order d.leftComparison.coordinates d.leftComparison.form x) := by
  let v : Atlas.G2.TernaryLevi.radical false :=
    t.cubicAtlasShortEquiv p.core_order d.leftComparison.coordinates d.leftComparison.form x
  have he : d.leftEndpointEquiv (inclusion t.cubicCore_le_normalizer x)=
      d.leftCorrection*inclusion (Atlas.G2.TernaryLevi.radical_le_endpoint false) v*
          d.leftCorrection⁻¹ := Subtype.ext (d.leftEndpointEquiv_core x)
  rw [d.compatibleAtlasIso_left,he]
  exact (congrArg (fun q : Atlas.G2.TernaryLevi.endpoint false=>(q:Atlas.G2.Model (ZMod 3)))
    (Atlas.G2.TernaryLevi.endpointShift_conjugate_core false j d.leftCorrection v)).trans rfl

/-- The original long core and original Sylow-aligner inclusion are retained. -/
theorem compatibleAtlasIso_right_core (j k : ZMod 3) (h)
    (x : cubicOddCore (swapFactors c) t.swap.x) :
    ((d.compatibleAtlasIso j k h).right
      (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x)):
        Atlas.G2.Model (ZMod 3))=
      MulAut.conj (d.rightCorrection:Atlas.G2.Model (ZMod 3))
        (t.swap.cubicAtlasLongEquiv p.right_core_order d.rightComparison.coordinates d.rightComparison.form x) := by
  let v : Atlas.G2.TernaryLevi.radical true :=
    t.swap.cubicAtlasLongEquiv p.right_core_order d.rightComparison.coordinates d.rightComparison.form x
  have he : d.rightEndpointEquiv (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x))=
      d.rightCorrection*inclusion (Atlas.G2.TernaryLevi.radical_le_endpoint true) v*
          d.rightCorrection⁻¹ := Subtype.ext (d.rightEndpointEquiv_core x)
  rw [d.compatibleAtlasIso_right,he]
  exact (congrArg (fun q : Atlas.G2.TernaryLevi.endpoint true=>(q:Atlas.G2.Model (ZMod 3)))
    (Atlas.G2.TernaryLevi.endpointShift_conjugate_core true (-k) d.rightCorrection v)).trans rfl

/-- The full short actor has the same marking and an explicit central cocycle. -/
theorem compatibleAtlasIso_left_actor (j k : ZMod 3) (h) (a : Atlas.G2.TernaryLevi.GL23) :
    (d.compatibleAtlasIso j k h).left (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv p.core_order).symm a))=
      Atlas.G2.TernaryLevi.endpointShift false j d.leftCorrection*
        (inclusion (Atlas.G2.TernaryLevi.radical_le_endpoint false)
          (Atlas.G2.TernaryLevi.centralRoot false
            (j*Atlas.G2.TernaryLevi.shiftCocycle (d.leftComparison.actor a)))*
          Atlas.G2.TernaryLevi.endpointEmbedding false (d.leftComparison.actor a))*
        (Atlas.G2.TernaryLevi.endpointShift false j d.leftCorrection)⁻¹ := by
  have he : d.leftEndpointEquiv (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv p.core_order).symm a))=
      d.leftCorrection*Atlas.G2.TernaryLevi.endpointEmbedding false (d.leftComparison.actor a)*
        d.leftCorrection⁻¹ := Subtype.ext (d.leftEndpointEquiv_actor a)
  rw [d.compatibleAtlasIso_left,he,map_mul,map_mul,map_inv,Atlas.G2.TernaryLevi.endpointShift_actor]

/-- The full long actor retains the same marking and Sylow conjugator. -/
theorem compatibleAtlasIso_right_actor (j k : ZMod 3) (h) (a : Atlas.G2.TernaryLevi.GL23) :
    (d.compatibleAtlasIso j k h).right (p.rightEndpointEquiv (inclusion t.swap.cubicLevi_le_normalizer
      ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a)))=
      Atlas.G2.TernaryLevi.endpointShift true (-k) d.rightCorrection*
        (inclusion (Atlas.G2.TernaryLevi.radical_le_endpoint true)
          (Atlas.G2.TernaryLevi.centralRoot true
            (-k*Atlas.G2.TernaryLevi.shiftCocycle (d.rightComparison.actor a)))*
          Atlas.G2.TernaryLevi.endpointEmbedding true (d.rightComparison.actor a))*
        (Atlas.G2.TernaryLevi.endpointShift true (-k) d.rightCorrection)⁻¹ := by
  have he : d.rightEndpointEquiv (p.rightEndpointEquiv (inclusion t.swap.cubicLevi_le_normalizer
      ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a)))=
      d.rightCorrection*Atlas.G2.TernaryLevi.endpointEmbedding true (d.rightComparison.actor a)*
        d.rightCorrection⁻¹ := Subtype.ext (d.rightEndpointEquiv_actor a)
  rw [d.compatibleAtlasIso_right,he,map_mul,map_mul,map_inv,Atlas.G2.TernaryLevi.endpointShift_actor]

end AlignedCubicPair.MiddleAlignment
namespace AlignedCubicPair
variable {t : CubicTorus c} (p : AlignedCubicPair t)

/-- Both actual endpoint maps agree on the whole middle, with no remaining
action, twist-extension or compatibility premise. -/
theorem nonempty_atlasAmalgamIso : Nonempty (RankTwoAmalgam.Iso p.amalgam
    (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3))) := by
  obtain ⟨d⟩ := p.nonempty_middleAlignment
  obtain ⟨d,j,k,_,_,_,h⟩ := d.exists_normalized_middle
  exact ⟨d.compatibleAtlasIso j k h⟩

include p in
/-- The original marked large-core completion is the actual Atlas group. -/
theorem nonempty_mulEquiv : Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  obtain ⟨e⟩ := p.nonempty_atlasAmalgamIso
  exact p.nonempty_mulEquiv_of_amalgam_iso e.symm

end AlignedCubicPair

/-- Genuine recognition of the full large-core branch of I.4.5, for the
original nonsimple input statement. Source simplicity is proved upstream. -/
theorem nonempty_mulEquiv_of_cube_dvd (c : G2ThreeConfiguration G)
    (hbig : 3^3∣Nat.card G) : Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨hx,_⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
  obtain ⟨p⟩ := t.nonempty_alignedCubicPair hx
  exact p.nonempty_mulEquiv

/-- The only remaining original I.4.5 branch is the independent strong-three
exclusion. The other branch now concludes an actual model isomorphism. -/
theorem recognition_or_strong_three (c : G2ThreeConfiguration G) :
    (c.H≠⊤ ∧ 3∣Nat.card c.H ∧
      ∀ a : G,a∉c.H → ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  by_cases hbig : 3^3∣Nat.card G
  · exact Or.inr (nonempty_mulEquiv_of_cube_dvd c hbig)
  · obtain ⟨t⟩ := exists_cubic_torus c
    exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
