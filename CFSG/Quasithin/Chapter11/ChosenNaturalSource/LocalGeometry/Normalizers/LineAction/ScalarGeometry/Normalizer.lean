module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The Cartan image and its Sylow normalizer on the original line

The preceding identity V₁ = C_V(T_L) makes the inner Sylow act trivially
on the literal line. Every odd Hall Cartan complements that Sylow in
N_L(T_L), so both have exactly the same line image. Since T normalizes
N_L(T_L), its line image normalizes the Cartan image. This proves the
normalizer input of 11.2.3 without assuming T normalizes the chosen X.

The fixed-line identity remains with producer
`qt-d-1222-natural-flag-cartan`. Source: Aschbacher--Smith, combined
manuscript, 1 March 2004, Chapter 11 setup and 11.2.3,
printed pp.759--761,768--769.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- The entire inner Sylow normalizer preserves the original fixed line. -/
theorem cartanNormalizer_normalizes_line
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    cartanNormalizer T L ≤ normalizer (f.Vi 0 : Set G) := by
  rw [hfixed]
  exact (le_inf (inf_le_left.trans D.normalizes)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
include D in
/-- T normalizes the original Cartan normalizer, whether or not it normalizes X. -/
theorem sylow_normalizes_cartanNormalizer :
    (T : Subgroup G) ≤ normalizer (cartanNormalizer T L : Set G) := by
  rw [cartanNormalizer_eq_intersection_normalizer]
  exact (le_inf D.sylow_normalizes_component
    (((le_inf (T : Subgroup G).le_normalizer D.sylow_normalizes_component).trans
      inf_normalizer_le_normalizer_inf).trans (normalizer _).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf

/-- The literal inner Sylow, as a Sylow subgroup of the Cartan normalizer. -/
def cartanSylow (c : Coordinates D F) : Sylow 2 (cartanNormalizer T L) :=
  (c.innerSylow.subtype (show (c.innerSylow : Subgroup L) ≤
      (cartanNormalizer T L).subgroupOf L from by
    intro p hp
    have hpT : p.val ∈ T := by rw [c.innerSylow_coe] at hp; exact hp
    exact ⟨p.property, (sourceTL T L).le_normalizer
      (sylow_intersection_le_sourceTL ⟨hpT,p.property⟩)⟩)).mapSurjective
    (f := (subgroupOfEquivOfLe (show cartanNormalizer T L ≤ L from inf_le_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show cartanNormalizer T L ≤ L from inf_le_left)).surjective

/-- Its ambient elements are precisely in the original inner Sylow. -/
theorem cartanSylow_le_intersection (p : cartanNormalizer T L)
    (hp : p ∈ (cartanSylow c : Subgroup (cartanNormalizer T L))) :
    p.val ∈ (T : Subgroup G) ⊓ L := by
  obtain ⟨q,hq,hqp⟩ := hp
  have ht : q.val.val ∈ T := by
    have hq' : q.val ∈ (c.innerSylow : Subgroup L) := hq
    rw [c.innerSylow_coe] at hq'
    exact hq'
  refine ⟨?_,p.property.1⟩
  rw [← hqp]
  exact ht

/-- The inner Sylow lies in the exact kernel of the original line action. -/
theorem cartanSylow_fixes_line
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (p : cartanNormalizer T L)
    (hp : p ∈ (cartanSylow c : Subgroup (cartanNormalizer T L))) :
    lineAction f (inclusion (cartanNormalizer_normalizes_line f hfixed) p) = 1 := by
  apply (show _ ∈ (lineAction f).ker ↔ _ from Iff.rfl).mp
  rw [lineAction_ker]
  intro v hv
  exact ((hfixed ▸ hv : v ∈ V ⊓ centralizer (sourceTL T L : Set G)).2 _
    (sylow_intersection_le_sourceTL (cartanSylow_le_intersection (c := c) p hp))).symm

/-- Every odd Hall Cartan has the same literal line image as its whole normalizer. -/
theorem lineImage_cartan_eq_normalizer {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    lineImage f X = lineImage f (cartanNormalizer T L) := by
  apply le_antisymm (map_mono (comap_mono hX.1))
  rintro _ ⟨n,hn,rfl⟩
  let n' : cartanNormalizer T L := ⟨n,hn⟩
  obtain ⟨⟨p,x⟩,he⟩ := (OddHall.sylow_complement_of_hall (cartanSylow c) hX.2).2 n'
  have he' : n = inclusion (cartanNormalizer_normalizes_line f hfixed) (p.val * x.val) :=
    Subtype.ext (congrArg (fun z : cartanNormalizer T L => (z : G)) he.symm)
  rw [he', map_mul, map_mul, cartanSylow_fixes_line f hfixed p.val p.property, one_mul]
  exact mem_map_of_mem _ x.property

/-- The desired normalizer relation follows from the fixed-line identity and Hall complement. -/
theorem lineImage_sylow_normalizes_cartan {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    lineImage f T ≤ normalizer (lineImage f X : Set _) := by
  rw [lineImage_cartan_eq_normalizer f hX hfixed]
  apply le_trans (map_mono ?_) (((cartanNormalizer T L).subgroupOf
    (normalizer (f.Vi 0 : Set G))).le_normalizer_map (lineAction f))
  intro t ht
  rw [← subgroupOf_normalizer_eq (cartanNormalizer_normalizes_line f hfixed)]
  exact sylow_normalizes_cartanNormalizer (D := D) ht
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
