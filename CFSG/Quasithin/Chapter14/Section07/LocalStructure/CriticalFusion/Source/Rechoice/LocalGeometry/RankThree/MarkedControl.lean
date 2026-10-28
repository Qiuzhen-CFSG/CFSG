module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MarkedControl.Model
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MovedPlane

/-!
# The actual relative normalizer of the selected rank-three commutator

The genuine rank-three cover is injective. The selected commutator image
is its single upper displacement plane, so every normalizing actor with
even S₅ image belongs to the upper four-group. Squaring puts every actor
in that even subgroup. Hence the full image and its two-core pullback
are two-groups. The original Sylow subgroup already normalizes the
commutator, so maximality gives precisely N_H(Fcomm)=T.

This proves the normalizer bound in Aschbacher--Smith 14.7.70, printed
p.1074. The legacy `MarkedPlaneControl` asks additionally for centralization
of the original V₂; that stronger field is neither used nor asserted here.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MarkedControl
open Subgroup Representation Chapter12.Section08
open Representation.SL2FourNatural Representation.SL2FourCentralCover
open Matrix.SpecialLinearGroup MarkedPartitions
open Preparation Preparation.MarkedSpans
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

private theorem image_normalizer (x : F.H)
    (hx : (x : G) ∈ normalizer (Fcomm c : Set G))
    (w : W) (hw : w ∈ tilde d (Fcomm c)) : d.action x w ∈ tilde d (Fcomm c) := by
  obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  let b : F.U := ⟨x * a * (x : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized x.property) a).mp a.property⟩
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr
    ⟨b, (mem_normalizer_iff.mp hx a).mp ha, d.conjugationSection.equivariant x a⟩

/-- Every even-image actor preserving the actual commutator has upper
unipotent image, with the same quotient marking as the source. -/
theorem even_normalizer_image (h : Preliminary d c) (s : d.ActionDescent)
    (mark : UpperMarking d) (x : F.H)
    (hx : (x : G) ∈ normalizer (Fcomm c : Set G))
    (heven : d.qH x ∈ alternatingGroup (Fin 5)) :
    d.qH x ∈ (upperUnipotent SL2FourNatural.F).map (alternatingActor d.naturalQuotient) := by
  obtain ⟨a, ha, t, ht, hat⟩ := exists_upper_actor d c h.earlier mark h.star_card
  have himage := commutator_image d c h.earlier s h.star_card a ha
    (upper_actor_ne_one d a t ht hat)
  obtain ⟨g, hg⟩ := d.naturalQuotient.marking.surjective ⟨d.qH x, heven⟩
  have hg' : d.qH x = alternatingActor d.naturalQuotient g := (congrArg Subtype.val hg).symm
  have hupper : g ∈ upperUnipotent SL2FourNatural.F := by
    apply preserves_displacement_mem_upper g t ht
    intro y
    have hy : cover d s (point (t ^ 2 * y) (t * y)) ∈ tilde d (Fcomm c) := by
      rw [himage]
      exact (mem_displacement_iff d s a t hat _).mpr ⟨y, rfl⟩
    have hm := image_normalizer d c x hx _ hy
    rw [himage, actor_cover d s x g hg'] at hm
    obtain ⟨z, hz⟩ := (mem_displacement_iff d s a t hat _).mp hm
    exact ⟨z, cover_injective d s h.rank_three hz.symm⟩
  exact mem_map.mpr ⟨g, hupper, hg'.symm⟩

def relativeNormalizer : Subgroup F.H := (normalizer (Fcomm c : Set G)).comap F.H.subtype

private theorem image_two_group (h : Preliminary d c) (s : d.ActionDescent)
    (mark : UpperMarking d) : IsPGroup 2 ((relativeNormalizer c).map d.qH) := by
  let U := (upperUnipotent SL2FourNatural.F).map (alternatingActor d.naturalQuotient)
  have hU : IsPGroup 2 U := (upperUnipotentSylow SL2FourNatural.F 2).isPGroup'.map _
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  have hsqeven : d.qH (x ^ 2) ∈ alternatingGroup (Fin 5) := by
    rw [map_pow, Equiv.Perm.mem_alternatingGroup, map_pow, pow_two, Int.units_mul_self]
  have hsqU : d.qH (x ^ 2) ∈ U := even_normalizer_image d c h s mark (x ^ 2)
    ((normalizer (Fcomm c : Set G)).pow_mem hx 2) hsqeven
  obtain ⟨k, hk⟩ := hU ⟨d.qH (x ^ 2), hsqU⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have he : (d.qH x ^ 2) ^ (2 ^ k) = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow] using congrArg Subtype.val hk
  change (y : ChapterJ.S5) ^ (2 ^ (k + 1)) = 1
  rw [← hxy, pow_succ', pow_mul]
  exact he

/-- The relative normalizer is a two-group before invoking maximality of T. -/
theorem normalizer_isPGroup (h : Preliminary d c) (s : d.ActionDescent)
    (mark : UpperMarking d) : IsPGroup 2 (F.H ⊓ normalizer (Fcomm c : Set G) : Subgroup G) := by
  have hker : IsPGroup 2 d.qH.ker := by
    rw [d.qH_ker]
    exact (pCore_isPGroup.map F.H.subtype).comap_subtype
  have hN : IsPGroup 2 (relativeNormalizer c) :=
    ((image_two_group d c h s mark).comap_of_ker_isPGroup d.qH hker).to_le
      (le_comap_map d.qH (relativeNormalizer c))
  have hmap : (relativeNormalizer c).map F.H.subtype =
      F.H ⊓ normalizer (Fcomm c : Set G) := by
    rw [relativeNormalizer, Subgroup.map_comap_eq, F.H.range_subtype]
  exact hmap ▸ hN.map F.H.subtype

/-- Source 14.7.70: the literal H-normalizer of Fcomm is exactly the original
Sylow subgroup. No normalizer or V₂-centralization premise is retained. -/
theorem normalizer_eq_T (h : Preliminary d c) (s : d.ActionDescent)
    (mark : UpperMarking d) :
    F.H ⊓ normalizer (Fcomm c : Set G) = (T : Subgroup G) :=
  T.is_maximal' (normalizer_isPGroup d c h s mark)
    (le_inf (F.invariant 1) h.commutator_normalized)

theorem normalizer_le_T (h : Preliminary d c) (s : d.ActionDescent)
    (mark : UpperMarking d) :
    F.H ⊓ normalizer (Fcomm c : Set G) ≤ (T : Subgroup G) :=
  (normalizer_eq_T d c h s mark).le

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MarkedControl
