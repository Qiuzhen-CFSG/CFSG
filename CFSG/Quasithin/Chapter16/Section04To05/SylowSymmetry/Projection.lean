module

public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The inner projection in the relative Sylow argument

In the contrary branch of 16.4.10, write `C = T_C`, `A = R₀`, and
`S = C_C(R) < C`. Uniform centralizers force `A ∩ L = 1` and place the
commuting coordinate of every element of `A` in `S`. Multiplication
coordinates construct an injective homomorphism `A → S/Z(L)`.

The source's `s(B)` is the full inverse image of the projection of `B`.
Its central intersection is **the kernel** `Z(L)`, and its order is
`|B|·|Z(L)|`. The printed assertion that this intersection is trivial before
proving `Z(L)=1` drops the kernel. The corrected equality suffices both for
the elementary-image comparison and the final contradiction. The present
module proves the projection and order comparisons; it does not yet prove
the normal-four/TI contradiction or the Sylow upgrade.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 16.4.10,
printed p.1193. All normality of the quotient kernel is relative to `S`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry
open Subgroup
variable {G : Type*} [Group G]

/-- The local projection configuration in the contrary case of 16.4.10.
Here `C = T_C`, `A = R₀`, and `S = C_C(R)`. -/
structure ProjectionConfiguration (C L A S : Subgroup G) : Prop where
  centralizes : C ≤ centralizer (L : Set G)
  factors : A ≤ C ⊔ L
  nontrivial : A ≠ ⊥
  proper : S < C
  centralizers : ∀ a ∈ A, a ≠ 1 → C ⊓ centralizer ({a} : Set G) = S
  center_le : L ⊓ centralizer (L : Set G) ≤ C

private theorem factorization {C L A : Subgroup G}
    (hc : C ≤ centralizer (L : Set G)) (ha : A ≤ C ⊔ L) (a : A) :
    ∃ c : C, ∃ l : L, (c : G) * l = a := by
  have hx := ha a.property
  change (a : G) ∈ (C ⊔ L : Subgroup G) at hx
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right C L
    (hc.trans (centralizer_le_normalizer _))] at hx
  rcases hx with ⟨c, hc, l, hl, he⟩
  exact ⟨⟨c, hc⟩, ⟨l, hl⟩, he⟩

variable {C L A S : Subgroup G}

/-- A nonidentity element of `A` cannot lie in the discarded factor. -/
theorem ProjectionConfiguration.disjoint (h : ProjectionConfiguration C L A S) :
    Disjoint A L := by
  apply Subgroup.disjoint_def.mpr
  intro a ha hl
  by_contra hn
  have he := h.centralizers a ha hn
  have hle : C ≤ centralizer ({a} : Set G) := by
    intro c hc
    apply mem_centralizer_iff.mpr
    intro x hx
    have hx' : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact mem_centralizer_iff.mp (h.centralizes hc) a hl
  rw [inf_eq_left.mpr hle] at he
  exact h.proper.ne he.symm

/-- Multiplication coordinates of nonidentity elements land in `S`. -/
theorem ProjectionConfiguration.factor_mem (h : ProjectionConfiguration C L A S)
    {a c l : G} (ha : a ∈ A) (hn : a ≠ 1) (hc : c ∈ C) (hl : l ∈ L)
    (he : c * l = a) : c ∈ S := by
  rw [← h.centralizers a ha hn]
  refine ⟨hc, mem_centralizer_iff.mpr ?_⟩
  intro x hx
  obtain rfl : x = a := Set.mem_singleton_iff.mp hx
  rw [← he]
  have hcl := mem_centralizer_iff.mp (h.centralizes hc) l hl
  calc c * l * c = c * (l * c) := mul_assoc _ _ _
       _ = c * (c * l) := by rw [hcl]

/-- The projection uses the centralizer factor, rather than all of `T_C`. -/
theorem ProjectionConfiguration.factors_in_centralizer
    (h : ProjectionConfiguration C L A S) : A ≤ S ⊔ L := by
  intro a ha
  by_cases hn : a = 1
  · simp [hn]
  obtain ⟨c, l, he⟩ := factorization h.centralizes h.factors ⟨a, ha⟩
  change (c : G) * l = a at he
  rw [← he]
  exact mul_mem_sup (h.factor_mem ha hn c.property l.property he) l.property

/-- The overlap in the projection is the actual center of `L`. -/
theorem ProjectionConfiguration.overlap
    (h : ProjectionConfiguration C L A S) :
    S ⊓ L = L ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_right (inf_le_left.trans (h.proper.le.trans h.centralizes))
  · intro z hz
    obtain ⟨⟨a, ha⟩, han⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.nontrivial
    have han : a ≠ 1 := fun he => han (Subtype.ext he)
    obtain ⟨c, l, he⟩ := factorization h.centralizes h.factors ⟨a, ha⟩
    have hzc : (c : G) * z = z * c := (mem_centralizer_iff.mp
      (h.centralizes c.property) z hz.1).symm
    have hzl : (l : G) * z = z * l := mem_centralizer_iff.mp hz.2 l l.property
    change (c : G) * l = a at he
    have hza : a * z = z * a := by
      rw [← he, mul_assoc, hzl, ← mul_assoc, hzc, mul_assoc]
    refine ⟨?_, hz.1⟩
    rw [← h.centralizers a ha han]
    exact ⟨h.center_le hz, mem_centralizer_iff.mpr (by simpa using hza)⟩

/-- Coordinate construction of the source homomorphism. The kernel is killed
only by disjointness with `L`, not by dropping the central overlap. -/
theorem exists_quotient_projection (S L A : Subgroup G)
    (hc : S ≤ centralizer (L : Set G)) (ha : A ≤ S ⊔ L) (hd : Disjoint A L) :
    let := normal_subgroupOf_of_le_normalizer (hc.trans (centralizer_le_normalizer _))
    ∃ π : A →* S ⧸ L.subgroupOf S,
      Function.Injective π ∧
      ∀ (a : A) (s : S) (l : L), (s : G) * l = a →
        π a = QuotientGroup.mk s := by
  let := normal_subgroupOf_of_le_normalizer (hc.trans (centralizer_le_normalizer _))
  choose s l hf using factorization hc ha
  let f : A → S ⧸ L.subgroupOf S := fun a => QuotientGroup.mk (s a)
  have heval (a : A) (b : S) (m : L) (he : (b : G) * m = a) :
      f a = QuotientGroup.mk b := by
    apply QuotientGroup.eq.mpr
    change ((s a : G)⁻¹ * (b : G)) ∈ L
    have he' : (s a : G) * l a = (b : G) * m := (hf a).trans he.symm
    have hid : (s a : G)⁻¹ * (b : G) = (l a : G) * (m : G)⁻¹ := by
      calc
        (s a : G)⁻¹ * (b : G) = (s a : G)⁻¹ * (((s a : G) * l a) * (m : G)⁻¹) := by
          rw [he']; group
        _ = (l a : G) * (m : G)⁻¹ := by group
    rw [hid]
    exact L.mul_mem (l a).property (L.inv_mem m.property)
  let π : A →* S ⧸ L.subgroupOf S :=
    { toFun := f
      map_one' := by simpa using heval 1 1 1 (by simp)
      map_mul' := by
        intro a b
        change f (a * b) = f a * f b
        rw [heval (a * b) (s a * s b) (l a * l b) ?_]
        · rfl
        · change ((s a : G) * s b) * ((l a : G) * l b) = (a : G) * b
          rw [← hf a, ← hf b]
          have hcomm := mem_centralizer_iff.mp (hc (s b).property) (l a) (l a).property
          calc
            ((s a : G) * s b) * ((l a : G) * l b) =
                (s a : G) * ((s b : G) * l a) * l b := by group
            _ = (s a : G) * ((l a : G) * s b) * l b := by rw [← hcomm]
            _ = ((s a : G) * l a) * ((s b : G) * l b) := by group }
  refine ⟨π, ?_, heval⟩
  apply (MonoidHom.ker_eq_bot_iff π).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hs : (s a : G) ∈ L := (QuotientGroup.eq_one_iff (s a)).mp ha
  have hal : (a : G) ∈ L := by
    rw [← hf a]
    exact L.mul_mem hs (l a).property
  have haa : (a : G) = 1 := Subgroup.disjoint_def.mp hd a.property hal
  exact Subtype.ext haa

/-- Normality is relative to `S`; no ambient normality is asserted. -/
theorem ProjectionConfiguration.overlap_normal
    (h : ProjectionConfiguration C L A S) : (L.subgroupOf S).Normal :=
  normal_subgroupOf_of_le_normalizer
    (h.proper.le.trans (h.centralizes.trans (centralizer_le_normalizer _)))

/-- The actual quotient map and its multiplication-coordinate formula. -/
structure Projection (S L A : Subgroup G) [(L.subgroupOf S).Normal] where
  hom : A →* S ⧸ L.subgroupOf S
  injective : Function.Injective hom
  on_factors : ∀ (a : A) (s : S) (l : L), (s : G) * l = a →
    hom a = QuotientGroup.mk s

/-- Construct the source map `R₀ → S/Z(L)`. `overlap` identifies its quotient
kernel with the actual center of `L`. -/
theorem ProjectionConfiguration.exists_projection
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal] :
    Nonempty (Projection S L A) := by
  obtain ⟨π, hi, he⟩ := exists_quotient_projection S L A
    (h.proper.le.trans h.centralizes) h.factors_in_centralizer h.disjoint
  exact ⟨⟨π, hi, he⟩⟩

/-- The source's `s(B)` is the full inverse image; it contains the kernel. -/
def Projection.inverseImage [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A) : Subgroup S :=
  (B.map π.hom).comap (QuotientGroup.mk' (L.subgroupOf S))

theorem Projection.kernel_le_inverseImage [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A) :
    L.subgroupOf S ≤ π.inverseImage B := by
  intro s hs
  change (QuotientGroup.mk s : S ⧸ L.subgroupOf S) ∈ B.map π.hom
  rw [(QuotientGroup.eq_one_iff s).mpr hs]
  exact one_mem _

/-- A centralizing element of the inner subgroup must be trivial. -/
theorem ProjectionConfiguration.centralizing_eq_one
    (h : ProjectionConfiguration C L A S) {a : G} (ha : a ∈ A)
    (hc : a ∈ centralizer (C : Set G)) : a = 1 := by
  by_contra hn
  have hle : C ≤ centralizer ({a} : Set G) := by
    intro c hcc
    apply mem_centralizer_iff.mpr
    intro x hx
    have hx' : x = a := Set.mem_singleton_iff.mp hx
    subst x
    exact (mem_centralizer_iff.mp hc c hcc).symm
  have he := h.centralizers a ha hn
  rw [inf_eq_left.mpr hle] at he
  exact h.proper.ne he.symm

/-- Corrected central-intersection assertion on p.1193. The intersection is
`Z(L)`, not the trivial subgroup: the inverse image retains its kernel. -/
theorem Projection.inverseImage_inf_centralizer
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A) :
    π.inverseImage B ⊓ (centralizer (C : Set G)).subgroupOf S = L.subgroupOf S := by
  apply le_antisymm
  · intro s hs
    obtain ⟨a, _, hea⟩ := hs.1
    obtain ⟨b, l, he⟩ := factorization
      (h.proper.le.trans h.centralizes) h.factors_in_centralizer a
    have hq : (QuotientGroup.mk s : S ⧸ L.subgroupOf S) = QuotientGroup.mk b :=
      hea.symm.trans (π.on_factors a b l he)
    have hsb : (s : G)⁻¹ * (b : G) ∈ L := by
      exact (show s⁻¹ * b ∈ L.subgroupOf S from QuotientGroup.eq.mp hq)
    have hsa : (s : G)⁻¹ * (a : G) ∈ L := by
      rw [← he, ← mul_assoc]
      exact L.mul_mem hsb l.property
    have hac : (a : G) ∈ centralizer (C : Set G) := by
      have hh := (centralizer (C : Set G)).mul_mem hs.2
        (le_centralizer_iff.mp h.centralizes hsa)
      change (s : G) * ((s : G)⁻¹ * (a : G)) ∈ centralizer (C : Set G) at hh
      simpa only [mul_inv_cancel_left] using hh
    have ha1 : a = 1 := Subtype.ext (h.centralizing_eq_one a.property hac)
    change s ∈ L.subgroupOf S
    apply (QuotientGroup.eq_one_iff s).mp
    exact hea.symm.trans (by rw [ha1, map_one])
  · exact le_inf (π.kernel_le_inverseImage B) (by
      intro s hs
      exact le_centralizer_iff.mp h.centralizes hs)

/-- The full inverse image has the kernel factor in its order. -/
theorem Projection.card_inverseImage [Finite G] [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A) :
    Nat.card (π.inverseImage B) = Nat.card B * Nat.card (L.subgroupOf S) := by
  let Z := L.subgroupOf S
  let q := QuotientGroup.mk' Z
  have hmap : (π.inverseImage B).map q = B.map π.hom :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) _
  have hi : Z.relIndex (π.inverseImage B) = Nat.card B := by
    rw [← QuotientGroup.ker_mk' Z, relIndex_ker, hmap,
      card_map_of_injective π.injective]
  have hc := (Z.subgroupOf (π.inverseImage B)).card_mul_index
  change Nat.card (Z.subgroupOf (π.inverseImage B)) *
    Z.relIndex (π.inverseImage B) = Nat.card (π.inverseImage B) at hc
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe (π.kernel_le_inverseImage B)).toEquiv] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

/-- The source order inequality, including the central kernel factor. -/
theorem Projection.card_mul_kernel_le [Finite G] [(L.subgroupOf S).Normal]
    (π : Projection S L A) : Nat.card A * Nat.card (L.subgroupOf S) ≤ Nat.card S := by
  have hc := (π.inverseImage ⊤).card_le_card_group
  rw [π.card_inverseImage, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv] at hc
  exact hc

/-- With outer index at most two and a nontrivial central kernel, the
source order inequalities are all equalities. In particular `s(R₀) = S`. -/
theorem Projection.order_saturation [Finite G] [(L.subgroupOf S).Normal]
    (π : Projection S L A) {R : Subgroup G} (hAR : A ≤ R)
    (hindex : A.relIndex R ≤ 2) (hcard : Nat.card S = Nat.card R)
    (hZ : 2 ≤ Nat.card (L.subgroupOf S)) :
    Nat.card (L.subgroupOf S) = 2 ∧ Nat.card S = 2 * Nat.card A ∧
      π.inverseImage ⊤ = ⊤ := by
  have hprod := (A.subgroupOf R).card_mul_index
  change Nat.card (A.subgroupOf R) * A.relIndex R = Nat.card R at hprod
  rw [Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv] at hprod
  have hupper : Nat.card S ≤ 2 * Nat.card A := by
    rw [hcard, ← hprod, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hindex
  have hlower := π.card_mul_kernel_le
  have hpos : 0 < Nat.card A := Nat.card_pos
  have heZ : Nat.card (L.subgroupOf S) = 2 := by nlinarith
  have heS : Nat.card S = 2 * Nat.card A := by rw [heZ] at hlower; omega
  refine ⟨heZ, heS, eq_of_le_of_card_ge le_top ?_⟩
  rw [π.card_inverseImage, heZ]
  simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv, heS,
    Nat.mul_comm] using (le_refl (2 * Nat.card A))

/-- In the elementary inverse-image branch, comparison with `Ω₁(S)`
really does force the kernel to be trivial. Only after this comparison may
one replace the corrected central intersection by the trivial subgroup. -/
theorem Projection.elementary_inverseImage [Finite G] [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A)
    [IsElementaryAbelian 2 (π.inverseImage B)]
    (hcard : Nat.card B = Nat.card (omega₁ S (p := 2))) :
    L.subgroupOf S = ⊥ ∧ π.inverseImage B = omega₁ S (p := 2) := by
  have hle : π.inverseImage B ≤ omega₁ S (p := 2) := elementaryAbelian_le_omega₁
  have hc := card_le_of_le hle
  rw [π.card_inverseImage, ← hcard] at hc
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hZpos : 0 < Nat.card (L.subgroupOf S) := Nat.card_pos
  have hZcard : Nat.card (L.subgroupOf S) = 1 := by nlinarith
  refine ⟨(L.subgroupOf S).eq_bot_iff_card.mpr hZcard, eq_of_le_of_card_ge hle ?_⟩
  rw [π.card_inverseImage, hZcard, mul_one, hcard]

/-- The repaired terminal contradiction: if the full inverse image is
central in `T_C`, its projected subgroup is trivial, even when `Z(L) ≠ 1`. -/
theorem Projection.eq_bot_of_inverseImage_centralizes [Finite G]
    (h : ProjectionConfiguration C L A S) [(L.subgroupOf S).Normal]
    (π : Projection S L A) (B : Subgroup A)
    (hc : π.inverseImage B ≤ (centralizer (C : Set G)).subgroupOf S) : B = ⊥ := by
  have he := π.inverseImage_inf_centralizer h B
  rw [inf_eq_left.mpr hc] at he
  have hcard := π.card_inverseImage B
  rw [he] at hcard
  have hz : 0 < Nat.card (L.subgroupOf S) := Nat.card_pos
  apply B.eq_bot_iff_card.mpr
  nlinarith

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry
