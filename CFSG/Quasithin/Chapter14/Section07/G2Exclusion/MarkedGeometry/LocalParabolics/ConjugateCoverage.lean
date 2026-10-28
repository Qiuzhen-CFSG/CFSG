module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import Theory.GroupAction.SubgroupQuotientSupportLift

/-!
# Literal pencil preimages and ambient conjugate coverage

Transitivity of the marked quotient pencil lifts through U → U/V₁ to
V^Y, and its span lifts to ⟨V^Y⟩. A subgroup version of the flag-orbit
argument A.1.7 turns the earlier hyperplane transitivity of L on V into
coverage of all ambient conjugates containing V₂. The family fixation
from `FamilyAction` then identifies the local vertex orbit and proves
that the local vertex normalizes the lifted span.

Only relative normality in U is used. The quotient pencil hypotheses are
the explicit inputs from 14.7.55(1),(2),(6); `Models` constructs the actual
natural/Weyl quotient geometries used to instantiate them. This module
does not assert the remaining full linear-image or parabolic conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.56,
printed p.1066; A.1.7, printed p.21.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open Subgroup
open Atlas.G2
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {G : Type*} [Group G]

abbrev conjugate (V : Subgroup G) (g : G) : Subgroup G :=
  V.map (MulAut.conj g).toMonoidHom

private theorem conjugate_mul (V : Subgroup G) (g h : G) :
    conjugate V (g * h) = conjugate (conjugate V h) g := by
  rw [conjugate, conjugate, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem conjugate_one (V : Subgroup G) : conjugate V 1 = V := by
  change V.map (MulAut.conj 1).toMonoidHom = V
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, map_id]

private theorem conjugate_eq {V : Subgroup G} {g : G} (h : g ∈ normalizer V) :
    conjugate V g = V := mem_normalizer_iff_map_conj_eq.mp h

/-- The original line preimage is one of the generators of its Y-span. -/
theorem original_le_generated (V Y : Subgroup G) : V ≤ generatedLineFamily V Y := by
  calc
    V = conjugate V (1 : G) := (conjugate_one V).symm
    _ ≤ generatedLineFamily V Y := le_iSup (fun y : Y => conjugate V (y : G)) 1

/-- The literal preimage in U, embedded in the ambient group. -/
def linePreimage (U Z : Subgroup G) [(Z.subgroupOf U).Normal]
    (B : Subgroup (U ⧸ Z.subgroupOf U)) : Subgroup G :=
  (B.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype

/-- The doubly singular lines through the marked singular point. -/
def markedPencil {Q : Type*} [Group Q] (geom : QuotientGeometry Q)
    (p : SingularPoints (ZMod 2)) : Set (Subgroup Q) :=
  {B | ∃ L, pointOnLine p L ∧ geom.line L = B}

/-- The source family V(V₂), using literal quotient preimages. -/
def pencilPreimages (U Z : Subgroup G) [(Z.subgroupOf U).Normal]
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U))
    (p : SingularPoints (ZMod 2)) : Set (Subgroup G) :=
  linePreimage U Z '' markedPencil geom p

theorem linePreimage_image (U Z V : Subgroup G) [(Z.subgroupOf U).Normal]
    (hVU : V ≤ U) (hZV : Z ≤ V) :
    linePreimage U Z ((V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) = V := by
  unfold linePreimage
  rw [comap_map_eq_self, map_subgroupOf_eq_of_le hVU]
  rw [QuotientGroup.ker_mk']
  exact comap_mono hZV

/-- Lifting the transitivity in 14.7.55(6) gives exactly V^Y. The two
orbit premises concern the quotient pencil, before taking any preimages. -/
theorem pencil_preimages_eq_conjugate_family
    (U Z V Y : Subgroup G) [(Z.subgroupOf U).Normal]
    (hVU : V ≤ U) (hZV : Z ≤ V) (hYU : Y ≤ normalizer U)
    (action : Y →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ y : Y, ∀ u : U,
      action y (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(y : G) * (u : G) * (y : G)⁻¹,
            (mem_normalizer_iff.mp (hYU y.property) u).mp u.property⟩)
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U))
    (p : SingularPoints (ZMod 2)) (L : ZeroProductLine (ZMod 2))
    (hmark : (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = geom.line L)
    (horbit : ∀ y : Y, (geom.line L).map (action y).toMonoidHom ∈ markedPencil geom p)
    (htrans : ∀ B ∈ markedPencil geom p,
      ∃ y : Y, (geom.line L).map (action y).toMonoidHom = B) :
    pencilPreimages U Z geom p = conjugateLineFamily V Y := by
  have hbase : linePreimage U Z (geom.line L) = V := by
    rw [← hmark]
    exact linePreimage_image U Z V hVU hZV
  have hlift (y : Y) :
      linePreimage U Z ((geom.line L).map (action y).toMonoidHom) = conjugate V y := by
    rw [← hbase]
    exact (lift_support_conjugate Y U Z hYU action hact (geom.line L) y).symm
  ext P
  constructor
  · rintro ⟨B,hB,rfl⟩
    obtain ⟨y,rfl⟩ := htrans B hB
    exact ⟨y, (hlift y).symm⟩
  · rintro ⟨y,rfl⟩
    exact ⟨(geom.line L).map (action y).toMonoidHom, horbit y, hlift y⟩

private theorem linePreimage_iSup (U Z : Subgroup G) [(Z.subgroupOf U).Normal]
    {ι : Type*} [Nonempty ι] (F : ι → Subgroup (U ⧸ Z.subgroupOf U)) :
    linePreimage U Z (⨆ i, F i) = ⨆ i, linePreimage U Z (F i) := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  have hk : q.ker ≤ ⨆ i, (F i).comap q := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    apply le_trans _ (le_iSup (fun i => (F i).comap q) i)
    intro x hx
    change q x ∈ F i
    rw [MonoidHom.mem_ker.mp hx]
    exact (F i).one_mem
  have hm : (⨆ i, (F i).comap q).map q = ⨆ i, F i := by
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro i
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  change ((⨆ i, F i).comap q).map U.subtype = _
  rw [← hm, comap_map_eq_self hk, Subgroup.map_iSup]
  rfl

/-- The source U(V₂) is the preimage of the span of the quotient pencil. -/
def pencilSpanPreimage (U Z : Subgroup G) [(Z.subgroupOf U).Normal]
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U))
    (p : SingularPoints (ZMod 2)) : Subgroup G :=
  linePreimage U Z (⨆ B : markedPencil geom p, B.val)

/-- Taking the span commutes with these nonempty literal quotient preimages.
Thus the group on which the local vertex acts is precisely ⟨V^Y⟩. -/
theorem pencil_span_eq_generated (U Z V Y : Subgroup G) [(Z.subgroupOf U).Normal]
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U))
    (p : SingularPoints (ZMod 2))
    (hfamily : pencilPreimages U Z geom p = conjugateLineFamily V Y) :
    pencilSpanPreimage U Z geom p = generatedLineFamily V Y := by
  have hV : V ∈ pencilPreimages U Z geom p := by
    rw [hfamily]
    exact ⟨1,conjugate_one V⟩
  obtain ⟨B,hB,_⟩ := hV
  have : Nonempty (markedPencil geom p) := ⟨⟨B,hB⟩⟩
  unfold pencilSpanPreimage
  rw [linePreimage_iSup]
  unfold generatedLineFamily
  apply le_antisymm
  · apply iSup_le
    intro B
    have hb : linePreimage U Z B.val ∈ conjugateLineFamily V Y := by
      rw [← hfamily]
      exact ⟨B.val,B.property,rfl⟩
    obtain ⟨y,hy⟩ := hb
    rw [← hy]
    exact le_iSup (fun y : Y => conjugate V (y : G)) y
  · apply iSup_le
    intro y
    have hy : conjugate V y ∈ pencilPreimages U Z geom p := by
      rw [hfamily]
      exact ⟨y,rfl⟩
    obtain ⟨B,hB,hB'⟩ := hy
    change conjugate V y ≤ _
    rw [← hB']
    exact le_iSup (fun B : markedPencil geom p => linePreimage U Z B.val) ⟨B,hB⟩

/-- Ambient G-conjugates of V which contain the marked hyperplane. -/
def ambientConjugatesThrough (V V₂ : Subgroup G) : Set (Subgroup G) :=
  {W | V₂ ≤ W ∧ ∃ g : G, conjugate V g = W}

/-- The subgroup version of the flag-transitivity argument A.1.7(1):
transitivity of N_G(V) on the relevant subgroups of V turns ambient fusion
through V₂ into an orbit of N_G(V₂). -/
theorem ambient_conjugates_through_eq_normalizer_orbit
    (V V₂ L : Subgroup G) (hV₂ : V₂ ≤ V) (hLV : L ≤ normalizer V)
    (htrans : ∀ W : Subgroup G, W ≤ V → Nat.card W = Nat.card V₂ →
      ∃ l : L, conjugate V₂ l = W) :
    ambientConjugatesThrough V V₂ = conjugateLineFamily V (normalizer V₂) := by
  ext W
  constructor
  · rintro ⟨hV₂W,g,rfl⟩
    have hback : conjugate V₂ g⁻¹ ≤ V := by
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hV₂W
      change conjugate V₂ g⁻¹ ≤ conjugate (conjugate V g) g⁻¹ at hh
      rw [← conjugate_mul, inv_mul_cancel, conjugate_one] at hh
      exact hh
    have hcard : Nat.card (conjugate V₂ g⁻¹) = Nat.card V₂ :=
      card_map_of_injective (MulAut.conj g⁻¹).injective
    obtain ⟨l,hl⟩ := htrans _ hback hcard
    have hnorm : g * l ∈ normalizer V₂ := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change conjugate V₂ (g * l) = V₂
      rw [conjugate_mul, hl, ← conjugate_mul, mul_inv_cancel, conjugate_one]
    refine ⟨⟨g * l, hnorm⟩, ?_⟩
    change conjugate V (g * l) = conjugate V g
    rw [conjugate_mul, conjugate_eq (hLV l.property)]
  · rintro ⟨g,rfl⟩
    refine ⟨?_,g,rfl⟩
    exact (conjugate_eq g.property).ge.trans (map_mono hV₂)

private theorem conjugate_family_stable (V Y : Subgroup G) (y : Y)
    {W : Subgroup G} (hW : W ∈ conjugateLineFamily V Y) :
    conjugate W y ∈ conjugateLineFamily V Y := by
  obtain ⟨z,rfl⟩ := hW
  exact ⟨y * z, conjugate_mul V y z⟩

private theorem normalizes_family_stable (V Y T : Subgroup G)
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y)
    (t : T) {W : Subgroup G} (hW : W ∈ conjugateLineFamily V Y) :
    conjugate W t ∈ conjugateLineFamily V Y := by
  obtain ⟨y,rfl⟩ := hW
  let z : Y := ⟨(t : G) * y * (t : G)⁻¹,
    (mem_normalizer_iff.mp (hTY t.property) y).mp y.property⟩
  refine ⟨z, ?_⟩
  have ht := mem_normalizer_iff_map_conj_eq.mp (hTV t.property)
  change conjugate V t = V at ht
  calc
    conjugate V z = conjugate (conjugate V t) z := by rw [ht]
    _ = conjugate V ((z : G) * t) := (conjugate_mul V z t).symm
    _ = conjugate V ((t : G) * y) := by congr 1; dsimp [z]; group
    _ = conjugate (conjugate V y) t := conjugate_mul V t y

private theorem stable_sup (A B : Subgroup G) (F : Set (Subgroup G))
    (hA : ∀ a : A, ∀ W ∈ F, conjugate W a ∈ F)
    (hB : ∀ b : B, ∀ W ∈ F, conjugate W b ∈ F) :
    ∀ g : (A ⊔ B : Subgroup G), ∀ W ∈ F, conjugate W g ∈ F := by
  rintro ⟨g,hg⟩
  change ∀ W ∈ F, conjugate W g ∈ F
  rw [sup_eq_iSup] at hg
  refine Subgroup.iSup_induction (fun b : Bool => cond b A B)
    (C := fun g => ∀ W ∈ F, conjugate W g ∈ F) hg ?_ ?_ ?_
  · intro b x hx
    cases b
    · exact hB ⟨x,hx⟩
    · exact hA ⟨x,hx⟩
  · intro W hW
    rwa [conjugate_one]
  · intro x y ihx ihy W hW
    rw [conjugate_mul]
    exact ihx _ (ihy W hW)

/-- L₂ fixes every member; Y permutes its own orbit; T normalizes V and Y.
These facts identify the orbit under the generated local vertex group. -/
theorem local_vertex_orbit (V L₂ Y T : Subgroup G)
    (hfix : ∀ W ∈ conjugateLineFamily V Y, L₂ ≤ normalizer W)
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y) :
    conjugateLineFamily V (L₂ ⊔ Y ⊔ T) = conjugateLineFamily V Y := by
  have hL : ∀ l : L₂, ∀ W ∈ conjugateLineFamily V Y,
      conjugate W l ∈ conjugateLineFamily V Y := by
    intro l W hW
    rw [conjugate_eq (hfix W hW l.property)]
    exact hW
  have hstable := stable_sup (L₂ ⊔ Y) T (conjugateLineFamily V Y)
    (stable_sup L₂ Y _ hL (fun y _ hW => conjugate_family_stable V Y y hW))
    (fun t _ hW => normalizes_family_stable V Y T hTV hTY t hW)
  ext W
  constructor
  · rintro ⟨g,rfl⟩
    apply hstable g V
    exact ⟨1,conjugate_one V⟩
  · rintro ⟨y,rfl⟩
    exact ⟨⟨y, (show Y ≤ L₂ ⊔ Y ⊔ T from le_sup_right.trans le_sup_left) y.property⟩, rfl⟩

/-- The local vertex normalizes the actual span of the conjugate family. -/
theorem local_vertex_normalizes_span (V L₂ Y T : Subgroup G)
    (hfix : ∀ W ∈ conjugateLineFamily V Y, L₂ ≤ normalizer W)
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y) :
    L₂ ⊔ Y ⊔ T ≤ normalizer (generatedLineFamily V Y) := by
  let X := L₂ ⊔ Y ⊔ T
  have hYX : Y ≤ X := le_sup_right.trans le_sup_left
  have horbit := local_vertex_orbit V L₂ Y T hfix hTV hTY
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm : (generatedLineFamily V Y).map (MulAut.conj g).toMonoidHom ≤
      generatedLineFamily V Y := by
    unfold generatedLineFamily
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro y
    change conjugate (conjugate V y) g ≤ _
    rw [← conjugate_mul]
    have hf : conjugate V (g * y) ∈ conjugateLineFamily V Y := by
      rw [← horbit]
      exact ⟨⟨g * y, X.mul_mem hg (hYX y.property)⟩,rfl⟩
    obtain ⟨z,hz⟩ := hf
    rw [← hz]
    exact le_iSup (fun y : Y => conjugate V (y : G)) z
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

/-- Lemma 14.7.56(1)'s ambient coverage, using the family fixation already
proved in `FamilyAction` and the earlier local normalizer/transitivity data. -/
theorem source_ambient_coverage (V V₂ L L₂ Y T : Subgroup G)
    (hV₂ : V₂ ≤ V) (hLV : L ≤ normalizer V)
    (htrans : ∀ W : Subgroup G, W ≤ V → Nat.card W = Nat.card V₂ →
      ∃ l : L, conjugate V₂ l = W)
    (hvertex : normalizer V₂ = L₂ ⊔ Y ⊔ T)
    (hcomm : ⁅V,L₂⁆ = V₂) (hYL : Y ≤ normalizer L₂)
    (hYC : Y ≤ centralizer (V₂ : Set G))
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y) :
    ambientConjugatesThrough V V₂ = conjugateLineFamily V Y := by
  rw [ambient_conjugates_through_eq_normalizer_orbit V V₂ L hV₂ hLV htrans, hvertex]
  exact local_vertex_orbit V L₂ Y T
    (source_family_action V V₂ L₂ Y hV₂ hcomm hYL hYC).1 hTV hTY

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
