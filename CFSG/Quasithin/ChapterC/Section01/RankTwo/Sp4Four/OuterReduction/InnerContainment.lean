module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CharacteristicCut
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# The star centralizer lies in the original component modulo the core

Pointwise fixation of the natural field line places every star-centralizer
element in the actual component image in G/O2(G). Pulling back retains the
original quotient map and gives containment in A O2(G). Characteristic
minimality and the source cut then force A O2(G)=G. The field-line and cut
producers remain explicit; this is not a proof of the earlier graph bounds.

Source: MS93 Section7, p.933, using (3.4).
-/

public section

open Subgroup Representation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Theory.SpecificGroups.SymplecticFour

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {G F : Type*} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite G] in
theorem starCentralizer_le_component_core
    (A T : Subgroup G) [A.Normal] (Y : Subgroup T)
    (hcent : centralizer (A.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)) ≤
      A.map (QuotientGroup.mk' (pCore 2 G)))
    (hcard : 2 < Nat.card F)
    (e : A.map (QuotientGroup.mk' (pCore 2 G)) ≃* Sp F)
    (ρ : Representation (ZMod 2) (G ⧸ pCore 2 G) (Vector F))
    (hA : ∀ b : A.map (QuotientGroup.mk' (pCore 2 G)), ∀ w,
      ρ (b : G ⧸ pCore 2 G) w = symplecticNatural 2 (e b) w)
    (v : Vector F) (hv : v ≠ 0)
    (hline : ∀ t : starCentralizer T Y, ∀ c : F,
      ρ (QuotientGroup.mk' (pCore 2 G) ((t:T):G)) (c • v) = c • v) :
    (starCentralizer T Y).map T.subtype ≤ A ⊔ pCore 2 G := by
  rintro t ⟨t,ht,rfl⟩
  have hb := SymplecticNaturalNormalizer.mem_component_of_fixes_field_line
    (A.map (QuotientGroup.mk' (pCore 2 G))) hcent hcard e ρ hA
    (QuotientGroup.mk' (pCore 2 G) (t:G)) v hv (hline ⟨t,ht⟩)
  have hpre : (t:G) ∈ (A.map (QuotientGroup.mk' (pCore 2 G))).comap
      (QuotientGroup.mk' (pCore 2 G)) := hb
  change (t:G) ∈ A ⊔ pCore 2 G
  simpa only [comap_map_eq, QuotientGroup.ker_mk'] using hpre

omit [Finite G] in
theorem component_core_eq_top_of_star_line
    (A T : Subgroup G) [A.Normal] (Y : Subgroup T)
    (hgen : A ⊔ T = ⊤) (hmin : CharacteristicMinimal A T)
    (hcut : (A ⊔ (T ⊓ centralizer ((starSpan T Y).map T.subtype : Set G))) ⊓ pCore 2 G ≤
      T ⊓ centralizer ((starSpan T Y).map T.subtype : Set G))
    (hcent : centralizer (A.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)) ≤
      A.map (QuotientGroup.mk' (pCore 2 G)))
    (hcard : 2 < Nat.card F)
    (e : A.map (QuotientGroup.mk' (pCore 2 G)) ≃* Sp F)
    (ρ : Representation (ZMod 2) (G ⧸ pCore 2 G) (Vector F))
    (hA : ∀ b : A.map (QuotientGroup.mk' (pCore 2 G)), ∀ w,
      ρ (b : G ⧸ pCore 2 G) w = symplecticNatural 2 (e b) w)
    (v : Vector F) (hv : v ≠ 0)
    (hline : ∀ t : starCentralizer T Y, ∀ c : F,
      ρ (QuotientGroup.mk' (pCore 2 G) ((t:T):G)) (c • v) = c • v) :
    A ⊔ pCore 2 G = ⊤ := by
  have he := starCentralizer_eq_top_of_minimal A T hmin Y hcut
  have hinner := starCentralizer_le_component_core A T Y hcent hcard e ρ hA v hv hline
  rw [he, ← MonoidHom.range_eq_map, range_subtype] at hinner
  apply top_unique
  rw [← hgen]
  exact sup_le le_sup_left hinner

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
