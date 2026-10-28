module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Colors.Transport
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceReflections

/-!
# The six original colored parabolics

The genuine completion supplies one actor interchanging z,u and another
fixing z and sending u to zu. They normalize the literal four-group span,
so the proved color transport gives cardinality two in all three colors.
Their centers distinguish the colors, and the original union therefore
has cardinality six. The normalizer action is the actual ambient action
constructed in Transport; no six-cycle or recognition output is a premise.
Source: Aschbacher--Smith J.4.7, printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

private theorem normalizes_pairSpan (z u n : G)
    (hz : n*z*n⁻¹ ∈ pairSpan z u) (hu : n*u*n⁻¹ ∈ pairSpan z u) :
    n ∈ normalizer (pairSpan z u : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [pairSpan,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hu)
  · rw [card_map_of_injective (MulAut.conj n).injective]

/-- The global original family is the union of its three explicit colors. -/
theorem globalFamily_eq_union (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H) (z u : G) :
    globalFamily p B5 z u =
      (colorFamily p B5 z u z ∪ colorFamily p B5 z u u) ∪ colorFamily p B5 z u (z*u) := by
  ext E
  simp only [globalFamily,colors,Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff,
    Set.mem_union]
  aesop

variable {D : Type*} [Group D] (q : Completion D)
  (p : Plane d) (s : SourceChoice p) (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)
  (e : first ≃* p.F₁ B5) (f : D →* G)
  (hleft : ∀ a : first,f (q.left a)=(e a : G)) (hz : (e modelZ : G)=c.z)
  (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
include q s hi f hleft hz hfive

/-- Genuine original pair symmetries make each of the three source color families have two members. -/
theorem source_color_family_card (v : G) (hv : v ∈ colors c.z (sourceU e)) :
    Nat.card (colorFamily p B5 c.z (sourceU e) v)=2 := by
  have hcz : Nat.card (colorFamily p B5 c.z (sourceU e) c.z)=2 := by
    rw [colorFamily_z p B5 c e hz]
    exact source_family_card p s B5 hi c e hz hfive
  obtain ⟨a,_,haz,hau⟩ := source_mark_swap q c B5 e f hleft hz hfive
  have haN : a ∈ normalizer (pairSpan c.z (sourceU e) : Set G) :=
    normalizes_pairSpan c.z (sourceU e) a
      (by rw [haz]; exact mem_sup_right (mem_zpowers (sourceU e)))
      (by rw [hau]; exact mem_sup_left (mem_zpowers c.z))
  have hcu : Nat.card (colorFamily p B5 c.z (sourceU e) (sourceU e))=2 := by
    have hh := Nat.card_congr (colorConjugationEquiv p B5 c.z (sourceU e) a haN c.z)
    rw [haz] at hh
    exact hh.symm.trans hcz
  obtain ⟨r,_,_,_,hrz,hru,_,_,_,_⟩ := source_two_transvections q c B5 e f hleft hz hfive
  have hrN : r ∈ normalizer (pairSpan c.z (sourceU e) : Set G) :=
    normalizes_pairSpan c.z (sourceU e) r
      (by rw [hrz]; exact mem_sup_left (mem_zpowers c.z))
      (by rw [hru]; exact mul_mem_sup (mem_zpowers c.z) (mem_zpowers (sourceU e)))
  have hczu : Nat.card (colorFamily p B5 c.z (sourceU e) (c.z*sourceU e))=2 := by
    have hh := Nat.card_congr (colorConjugationEquiv p B5 c.z (sourceU e) r hrN (sourceU e))
    rw [hru] at hh
    exact hh.symm.trans hcu
  simp only [colors,Set.mem_insert_iff,Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact hcz
  · exact hcu
  · exact hczu

/-- The literal original parabolic family has six members. -/
theorem source_global_family_card : Nat.card (globalFamily p B5 c.z (sourceU e))=6 := by
  obtain ⟨hzo,huo,hne,_⟩ := source_pair_marks p B5 c e hz
  have hz1 : c.z≠1 := by intro h;rw [h,orderOf_one] at hzo;omega
  have hu1 : sourceU e≠1 := by intro h;rw [h,orderOf_one] at huo;omega
  have hzzu : c.z≠c.z*sourceU e := by
    intro hh
    exact hu1 (mul_left_cancel (show c.z*sourceU e=c.z*1 by simpa only [mul_one] using hh.symm))
  have huzu : sourceU e≠c.z*sourceU e := by
    intro hh
    exact hz1 (mul_right_cancel (show c.z*sourceU e=1*sourceU e by simpa only [one_mul] using hh.symm))
  have hdu := colorFamily_disjoint p B5 c e hz hne
  have hdzu := colorFamily_disjoint p B5 c e hz hzzu
  have hduzu := colorFamily_disjoint p B5 c e hz huzu
  have hd : Disjoint
      (colorFamily p B5 c.z (sourceU e) c.z ∪ colorFamily p B5 c.z (sourceU e) (sourceU e))
      (colorFamily p B5 c.z (sourceU e) (c.z*sourceU e)) := disjoint_sup_left.mpr ⟨hdzu,hduzu⟩
  have hc (v : G) (hv : v ∈ colors c.z (sourceU e)) :
      (colorFamily p B5 c.z (sourceU e) v).ncard=2 :=
    source_color_family_card q p s c B5 hi e f hleft hz hfive v hv
  rw [globalFamily_eq_union,Nat.card_coe_set_eq,Set.ncard_union_eq hd,Set.ncard_union_eq hdu,
    hc c.z (by simp [colors]),hc (sourceU e) (by simp [colors]),
    hc (c.z*sourceU e) (by simp [colors])]

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
