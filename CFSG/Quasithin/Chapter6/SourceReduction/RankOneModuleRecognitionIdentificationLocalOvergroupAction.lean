module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalSylowPair
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Transitivity of the original four-space overgroup

Natural-module transitivity and the point-centralizer identity give
transporters in N_L(T∩L) between all nonidentity elements of Z_S. The
already marked full action on U/⟨z⟩ moves any nonzero quotient vector into
the image of Z_S. Its original lift then lies in Z_S, so the generated
overgroup ⟨N_L(T∩L), C_G(z)⟩ is transitive on U minus its identity.

This uses the actual closure and the original quotient projection. It does
not assume transitivity on the two-element fibers of that projection.
Source: Aschbacher--Smith, 6.2.11, printed p.686, the construction of L₀.
The identification of the faithful image as A₇ and the ambient H-star
contradiction remain to be proved.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

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


/-- Natural point transitivity gives a transporter inside the component
Sylow normalizer for two nonidentity points of the distinguished plane. -/
theorem local_plane_point_transporter
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    {v w : G} (hv : v ∈ ZS (P : Subgroup G) L R) (hw : w ∈ ZS (P : Subgroup G) L R)
    (hvne : v ≠ 1) (hwne : w ≠ 1) :
    ∃ l ∈ L ⊓ normalizer (((P : Subgroup G) ⊓ L : Subgroup G) : Set G), l * v * l⁻¹ = w := by
  obtain ⟨l, hl, he⟩ := natural_point_transporter hnatural.2.1 hv.1 hw.1 hvne hwne
  refine ⟨l, ⟨hl, ?_⟩, he⟩
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  have hmove (k a b : G) (hk : k ∈ L) (hab : k * a * k⁻¹ = b)
      (ha : a ∈ ZS (P : Subgroup G) L R) (hb : b ∈ ZS (P : Subgroup G) L R)
      (ha1 : a ≠ 1) (hb1 : b ≠ 1) (x : G) (hx : x ∈ (P : Subgroup G) ⊓ L) :
      k * x * k⁻¹ ∈ (P : Subgroup G) ⊓ L := by
    have hxa : x ∈ L ⊓ centralizer ({a} : Set G) :=
      (local_component_point_centralizer h hnat ha ha1).ge hx
    have hc : Commute x a := mem_centralizer_singleton_iff.mp hxa.2
    have hc' := hc.map (MulAut.conj k).toMonoidHom
    change Commute (k * x * k⁻¹) (k * a * k⁻¹) at hc'
    rw [hab] at hc'
    exact (local_component_point_centralizer h hnat hb hb1).le
      ⟨L.mul_mem (L.mul_mem hk hx.2) (L.inv_mem hk), mem_centralizer_singleton_iff.mpr hc'⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hmove l v w hl he hv hw hvne hwne x
  · intro hx
    have he' : l⁻¹ * w * (l⁻¹)⁻¹ = v := by rw [← he]; group
    have hh := hmove l⁻¹ w v (L.inv_mem hl) he' hw hv hwne hvne (l * x * l⁻¹) hx
    have hc : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x := by group
    rwa [hc] at hh

/-- The original generated overgroup is transitive on the nonidentity
points of U. Quotient transitivity puts each point into the original plane;
the component Sylow normalizer then moves z to that point. -/
theorem four_generated_overgroup_transitive
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    {u : G} (hu : u ∈ sourceClosure (P : Subgroup G) L R z) (hune : u ≠ 1) :
    ∃ g ∈ (L ⊓ normalizer (((P : Subgroup G) ⊓ L : Subgroup G) : Set G)) ⊔ Centralizer z,
      g * z * g⁻¹ = u := by
  let := (reduced_space h hnatural hz ho hP).elementary
  let U := sourceClosure (P : Subgroup G) L R z
  let S := ZS (P : Subgroup G) L R
  let X := (L ⊓ normalizer (((P : Subgroup G) ⊓ L : Subgroup G) : Set G)) ⊔ Centralizer z
  have hz1 : z ≠ 1 := by intro he; simp [he] at ho
  have hmove (s : G) (hs : s ∈ S) (hs1 : s ≠ 1) : ∃ l ∈ X, l * z * l⁻¹ = s := by
    obtain ⟨l, hl, he⟩ := local_plane_point_transporter h hnatural hz hs hz1 hs1
    exact ⟨l, mem_sup_left hl, he⟩
  let uH : Centralizer z := ⟨u, map_subtype_le _ hu⟩
  have huW : projection z uH ∈ space (P : Subgroup G) L R z := by
    rw [← closure_image]
    exact mem_map_of_mem _ hu
  let w : space (P : Subgroup G) L R z := ⟨projection z uH, huW⟩
  by_cases hw : w = 1
  · have hu0 : projection z uH = 1 := congrArg Subtype.val hw
    have huLine : uH ∈ line z := (QuotientGroup.eq_one_iff uH).mp hu0
    exact hmove u ((zpowers_le.mpr hz) huLine) hune
  · obtain ⟨x, hx, hxs, _⟩ := four_image_G3 h hnatural hz ho hP hplane hcard
    obtain ⟨s, hs, hsp⟩ := hxs
    change projection z s = x.toMul.val at hsp
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hx
      (show Additive.ofMul w ≠ 0 from hw)
    have hfull := four_image_full_linear h hnatural hz ho hP hplane hcard
    obtain ⟨b, hb⟩ := hfull.ge (mem_top g)
    have he : projection z (b * s * b⁻¹) = projection z uH := by
      have hh := congrArg (fun v : Additive (space (P : Subgroup G) L R z) => v.toMul.val) hg
      rw [← hb] at hh
      change projection z b * x.toMul.val * (projection z b)⁻¹ = projection z uH at hh
      rw [← hsp, ← map_inv, ← map_mul, ← map_mul] at hh
      exact hh
    let c := uH / (b * s * b⁻¹)
    have hc : c ∈ line z := QuotientGroup.eq_iff_div_mem.mp he.symm
    have hcS : (c : G) ∈ S := (zpowers_le.mpr hz) hc
    have hcs : (c : G) * (s : G) ∈ S := S.mul_mem hcS hs
    have hbc : Commute b c := mem_center_iff.mp (line_central z hc) b
    have hec : b * (c * s) * b⁻¹ = uH := by
      calc
        _ = c * (b * s * b⁻¹) := by rw [← mul_assoc, hbc.eq]; group
        _ = _ := by simp only [c, div_mul_cancel]
    have hcs1 : (c : G) * (s : G) ≠ 1 := by
      intro hh
      have hh' : c * s = 1 := Subtype.ext hh
      rw [hh', mul_one, mul_inv_cancel] at hec
      exact hune (congrArg (fun a : Centralizer z => (a : G)) hec.symm)
    obtain ⟨l, hl, hel⟩ := hmove ((c : G) * (s : G)) hcs hcs1
    refine ⟨(b : G) * l, X.mul_mem (mem_sup_right b.property) hl, ?_⟩
    calc
      _ = (b : G) * (l * z * l⁻¹) * (b : G)⁻¹ := by group
      _ = _ := by rw [hel]; exact congrArg (fun a : Centralizer z => (a : G)) hec

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
