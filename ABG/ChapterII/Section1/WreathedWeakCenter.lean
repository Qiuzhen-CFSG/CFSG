module
public import ABG.ChapterII.Section1.WreathedRepresentativeFusion
public import ABG.ChapterII.Section1.WreathedLowNormalizerFusion
public import ABG.ChapterII.Section1.WreathedVNormalizerRestriction

/-!
# Weak closure of the wreathed Sylow center

In a finite group with a wreathed fusion frame, if the abelian base U has
automizer index two, every central element of the chosen Sylow subgroup S
is fused within S only to itself. Consequently every subgroup of the
embedded center is weakly closed in S. No condition on the V automizer
is required. These are the center and weak-closure assertions in
Alperin--Brauer--Gorenstein, Chapter II Section 1 Proposition 2, article
p.13, the final proof paragraph in page-014.tex.

Use the representative fusion theorem with the relation asserting that
a central starting element equals the ending element. This relation is
reflexive and transitive. Sylow conjugation fixes the center. Low base
normalizer action introduces only Sylow conjugacy, while the canonical V
normalizer centralizes the embedded center pointwise. Thus every ambient
fusion chain fixes a central starting element. For a subgroup of the center
whose conjugate lies in S, apply this result to each of its elements; the
conjugation map is pointwise the identity and hence its subgroup image is
unchanged.
-/

open scoped IsMulCommutative
namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G]

/-- A central Sylow element has no distinct ambient conjugate inside the
Sylow subgroup when the base automizer has order two. -/
public theorem central_isConj_eq_of_u_index_two
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hU : automizerIndex U = 2)
    {x y : S} (hx : x ∈ Subgroup.center S) (hxy : IsConj (x : G) (y : G)) :
    x = y := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  have hUP := (hf.presentation_representatives P).1
  have houter : outerAutomizerIndex U = 2 := by
    let := hf.2.2.1
    rw [outerAutomizerIndex, sup_eq_right.mpr (Subgroup.le_centralizer U)]
    exact hU
  have hconj {a b : S} (ha : a ∈ Subgroup.center S) (hab : IsConj a b) : a = b := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hab
    simpa only [Subgroup.mem_center_iff.mp ha g, mul_assoc, mul_inv_cancel, mul_one] using hg
  apply representative_fusion_relation S P (fun a b => a ∈ Subgroup.center S → a = b)
    (fun _ _ => rfl)
    (fun hab hbc ha => (hab ha).trans (hbc ((hab ha) ▸ ha)))
    (fun hab ha => hconj ha hab) ?_ ?_ hxy hx
  · intro g hg a b ha hab hac
    rw [← hUP] at hg ha
    exact hconj hac (low_normalizer_fusion_control S n U V U hf (Or.inl rfl)
      houter g hg a b ha hab)
  · intro g hg a b _ hab hac
    have hNC := (canonical_v_normalizer_structure S P).2.1
    have haC : (a : G) ∈ (Subgroup.center S).map (S : Subgroup G).subtype :=
      Subgroup.mem_map_of_mem _ hac
    have hc := hNC ((Subgroup.normalizer
      (P.V.map (S : Subgroup G).subtype : Set G)).inv_mem hg) (a : G) haC
    rw [← hc, mul_assoc, inv_mul_cancel, mul_one] at hab
    exact Subtype.ext hab

/-- Every subgroup of the embedded Sylow center is weakly closed when the
base automizer has order two. -/
public theorem weaklyClosed_center_subgroups_of_u_index_two (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hU : automizerIndex U = 2) :
    HasWeaklyClosedCenterSubgroups (S : Subgroup G) := by
  intro Z hZ
  have hZS : Z ≤ S := hZ.trans (Subgroup.map_subtype_le _)
  refine ⟨hZS, ?_⟩
  intro g hg
  change Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ S at hg
  change Z.map (MulAut.conj g⁻¹).toMonoidHom = Z
  have hfix (z : G) (hz : z ∈ Z) : (MulAut.conj g⁻¹) z = z := by
    let x : S := ⟨z, hZS hz⟩
    let y : S := ⟨(MulAut.conj g⁻¹) z, hg (Subgroup.mem_map_of_mem _ hz)⟩
    have hxC : x ∈ Subgroup.center S := by
      obtain ⟨a, ha, he⟩ := hZ hz
      have hax : a = x := Subtype.ext he
      rwa [← hax]
    have he := central_isConj_eq_of_u_index_two S n U V hf hU hxC
      (show IsConj (x : G) (y : G) from isConj_iff.mpr ⟨g⁻¹, rfl⟩)
    exact congrArg Subtype.val he.symm
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (MulAut.conj g⁻¹) a ∈ Z
    rwa [hfix a ha]
  · intro hz
    exact ⟨z, hz, hfix z hz⟩

end ABG.Wreathed
