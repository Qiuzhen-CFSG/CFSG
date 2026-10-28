module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span.FixedSpaces
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits

/-!
# The literal L₁ action on the opposite point

On the original U/V₁, the checked cubic displacement on V/V₁ proves
[Ṽ ker(p), L₁] = Ṽ. The literal R₁-fixed identity from FixedSpaces therefore
proves the second identity of 14.7.65. T-normalization of E puts Z̃α in that
fixed space, so its L₁ displacements lie in Ṽ. Saturating through the
original V₁ kernel proves the ambient upper bound on its orbit span.

Choose a point of Zα outside U₀. Its displacement by the actual cubic has
nonzero natural projection and lies in both Ṽ and the orbit image. Powers
of that same cubic are transitive on the nonzero natural upper line.
Injectivity of p on Ṽ then puts the whole Ṽ in the original orbit image.
The remaining V₁ recovery and equality of ambient subgroups are in Span.

All inputs and their earlier-source producers are recorded in FixedSpaces.
No pairing commutator identity is needed here. Source: Aschbacher–Smith,
combined manuscript, 1 March 2004, 14.7.65 and proof of 14.7.70,
printed pp.1070, 1074 (PDF pp.1087, 1091).
-/

public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
open Subgroup Representation Chapter12.Section08 Preparation Preparation.MarkedSpans
open Matrix.SpecialLinearGroup MarkedPartitions
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

private theorem image_invariant {A B : Subgroup G}
    (hn : B ≤ normalizer (A : Set G)) (l : F.H) (hl : (l : G) ∈ B)
    (w : W) (hw : w ∈ tilde d A) : d.action l w ∈ tilde d A := by
  obtain ⟨v, hv, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  have hv' : (l : G) * v * (l : G)⁻¹ ∈ A :=
    (mem_normalizer_iff.mp (hn hl) v).mp hv
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr
    ⟨⟨_, (mem_normalizer_iff.mp (d.conjugationSection.normalized l.property) v).mp v.property⟩,
      hv', d.conjugationSection.equivariant l v⟩

omit [Finite G] in
private theorem Li_le_K : F.Li L 1 ≤ K F := by
  intro x hx
  change x ∈ (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype at hx
  obtain ⟨n, hn, rfl⟩ := hx
  let f : (L ⊓ F.H : Subgroup G) →* F.H := inclusion inf_le_right
  exact mem_map.mpr ⟨f n, map_pResidual_le 2 f (mem_map.mpr ⟨n, hn, rfl⟩), rfl⟩

private theorem kernel_L₁_fixed (l : F.H) (hl : (l : G) ∈ F.Li L 1)
    (w : W) (hw : w ∈ d.projection.toLinearMap.ker) : d.action l w = w := by
  rw [d.fixed_kernel] at hw
  exact hw ⟨l, Li_le_K hl⟩

private theorem coords_mem_iff (A : Subgroup G) (hPA : F.Vi 1 ≤ A) (a : F.U) :
    (d.conjugationSection.coordinates a).toAdd ∈ tilde d A ↔ (a : G) ∈ A := by
  constructor
  · intro ha
    obtain ⟨b, hb, he⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp ha
    have hab : (a * b⁻¹ : F.U).val ∈ F.Vi 1 := by
      apply (d.conjugationSection.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, Multiplicative.toAdd.injective he, mul_inv_cancel]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using
      A.mul_mem (hPA hab) hb
  · intro ha
    exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨a, ha, rfl⟩

private theorem upper_zero : SL2FourNatural.upper 0 = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [SL2FourNatural.upper]


variable (s : d.ActionDescent)
include s
/-- The second identity of 14.7.65, with the literal R₁ and L₁ on U/V₁. -/
theorem original_R₁_commutator (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) :
    (⨆ l : (F.Li L 1).subgroupOf F.H,
      ((d.action l.val - LinearMap.id).comp
        (Representation.invariants (d.action.comp
          ((F.Ri L 1).subgroupOf F.H).subtype)).subtype).range) = tilde d V := by
  have hV : F.Li L 1 ≤ normalizer (V : Set G) :=
    (F.Li_le L 1).trans (inf_le_left.trans d.natural.chosen.normalizes)
  have h65 := original_R₁_fixed d s mark sep actors
  apply le_antisymm
  · apply iSup_le
    intro l y hy
    obtain ⟨w, rfl⟩ := hy
    have hw : (w : W) ∈ tilde d V ⊔ d.projection.toLinearMap.ker := by
      rw [← h65]
      exact w.property
    obtain ⟨v, hv, k, hk, he⟩ := Submodule.mem_sup.mp hw
    change d.action l.val w - w ∈ tilde d V
    rw [← he, map_add, kernel_L₁_fixed d l.val l.property k hk]
    simpa only [add_sub_add_right_eq_sub] using
      (tilde d V).sub_mem (image_invariant d hV l.val l.property v hv) hv
  · obtain ⟨l, hl, a, ha, ha1, he⟩ := actors.cubic
    intro y hy
    obtain ⟨v, hv⟩ := (cubic_seed_range d s mark sep actors l hl a ha ha1 he).symm ▸ hy
    apply Submodule.mem_iSup_of_mem (⟨l, hl⟩ : (F.Li L 1).subgroupOf F.H)
    refine ⟨⟨v, ?_⟩, hv⟩
    rw [h65]
    exact Submodule.mem_sup_left v.property
omit s

variable (c : CriticalPath (L := L) F) (h : Preliminary d c)
include s h

/-- All displacements of the opposite point by the actual L₁ lie in V/V₁. -/
theorem opposite_displacement (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G))
    (l : F.H) (hl : (l : G) ∈ F.Li L 1) (w : W) (hw : w ∈ tilde d c.Zα) :
    d.action l w - w ∈ tilde d V := by
  have hwR : w ∈ Representation.invariants
      (d.action.comp ((F.Ri L 1).subgroupOf F.H).subtype) := by
    intro r
    exact opposite_fixed d c h hT hw ⟨r, R₁_le_T r.property⟩
  rw [← original_R₁_commutator d s mark sep actors]
  apply Submodule.mem_iSup_of_mem (⟨l, hl⟩ : (F.Li L 1).subgroupOf F.H)
  exact ⟨⟨w, hwR⟩, rfl⟩

/-- This gives the upper containment of the actual orbit span, before dimensions are used. -/
theorem orbit_le (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    conjugateSpanBy c.Zα (F.Li L 1) ≤ V ⊔ c.Zα := by
  apply (closure_le _).mpr
  rintro x ⟨l, hl, z, hz, rfl⟩
  change l * z * l⁻¹ ∈ V ⊔ c.Zα
  let lH : F.H := ⟨l, (F.Li_le L 1 hl).2⟩
  let zU : F.U := ⟨z, (h.opposite_le.trans (h.commutator_le.trans inf_le_left)) hz⟩
  let b : F.U := ⟨l * z * l⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized lH.property) z).mp zU.property⟩
  have hdelta : ((b * zU⁻¹ : F.U) : G) ∈ V := by
    apply (coords_mem_iff d V (F.le_seed 1) _).mp
    have hd := opposite_displacement d s c h mark sep actors hT lH hl
      (d.conjugationSection.coordinates zU).toAdd
      ((d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨zU, hz, rfl⟩)
    have hb : (d.conjugationSection.coordinates b).toAdd =
        d.action lH (d.conjugationSection.coordinates zU).toAdd :=
      d.conjugationSection.equivariant lH zU
    simpa only [map_mul, map_inv, toAdd_mul, toAdd_inv, hb, sub_eq_add_neg] using hd
  have hm := (V ⊔ c.Zα).mul_mem (mem_sup_left hdelta) (mem_sup_right hz)
  change (l * z * l⁻¹) * z⁻¹ * z ∈ V ⊔ c.Zα at hm
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

/-- The cubic L₁ orbit fills the original V/V₁ inside the actual orbit image. -/
theorem seed_image_le_orbit (mark : UpperMarking d) (sep : d.ModuleSeparation)
    (actors : LocalActors d) (hT : (T : Subgroup G) ≤ normalizer (E c : Set G)) :
    tilde d V ≤ tilde d (conjugateSpanBy c.Zα (F.Li L 1)) := by
  let S := conjugateSpanBy c.Zα (F.Li L 1)
  have hS : F.Li L 1 ≤ normalizer (S : Set G) := le_normalizer_conjugateSpanBy _ _
  have hV : F.Li L 1 ≤ normalizer (V : Set G) :=
    (F.Li_le L 1).trans (inf_le_left.trans d.natural.chosen.normalizes)
  obtain ⟨l, hl, a, ha, ha1, he⟩ := actors.cubic
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ c.Zα, z ∉ d.U₀ := by
    by_contra! hh
    exact h.opposite_not_le hh
  let zU : F.U := ⟨z, (h.opposite_le.trans (h.commutator_le.trans inf_le_left)) hz⟩
  let w : W := (d.conjugationSection.coordinates zU).toAdd
  have hwZ : w ∈ tilde d c.Zα :=
    (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨zU, hz, rfl⟩
  have hwS : w ∈ tilde d S := d.conjugationSection.imageSpace_mono
    (le_conjugateSpanBy _ _) hwZ
  have hwUpper : w ∈ SL2CentralExtension.upperFixed
      (s.action.comp (alternatingActor d.naturalQuotient)) := by
    rw [upper_eq_seed_sup_kernel d s mark sep actors]
    have hf := fixed_eq_plane_sup_kernel d s mark sep actors
    exact (sup_le_sup (d.conjugationSection.imageSpace_mono (F.le_seed 2)) inf_le_left)
      (hf ▸ opposite_fixed d c h hT hwZ)
  obtain ⟨r, x, hx⟩ := (mem_upper_iff_point d s w).mp hwUpper
  have hx0 : x ≠ 0 := by
    intro heq
    apply hz0
    apply (d.mem_U₀ zU).mpr
    change d.projection w = 0
    rw [← hx, cover_projection, point_projection, heq]
    funext i
    fin_cases i <;> rfl
  let v := d.action l w - w
  have hvS : v ∈ tilde d S :=
    (tilde d S).sub_mem (image_invariant d hS l hl w hwS) hwS
  have hvV : v ∈ tilde d V := opposite_displacement d s c h mark sep actors hT l hl w hwZ
  have hvc : v = cover d s (point 0 ((a - 1) * x)) := by
    dsimp [v]
    rw [← hx, cubic_displacement d s l a ha he]
  have hpv : d.projection v ≠ 0 := by
    rw [hvc, cover_projection, point_projection]
    intro hn
    have hh := congrFun hn 0
    exact (mul_ne_zero (sub_ne_zero.mpr ha1) hx0) hh
  have hup (y : W) (hy : y ∈ tilde d V) : d.projection y 1 = 0 :=
    (mem_upper_iff d s y).mp (seed_le_upper d s mark actors hy)
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]
    exact (tilde d S).zero_mem
  have hpy : d.projection y ≠ 0 := by
    intro hh
    exact hy0 (Submodule.disjoint_def.mp (seed_disjoint_kernel d sep) y hy hh)
  obtain ⟨n, hn⟩ := PermittedChoice.ActorOrbits.Cubic.vector_orbit a ha ha1 0
    (d.projection v) (d.projection y) hpv hpy (hup v hvV) (hup y hy)
  have hn' : SL2FourNatural.action ((diag2 a ha)^n) (d.projection v) = d.projection y := by
    simpa only [upper_zero, inv_one, one_mul, mul_one] using hn
  have hln : ((l ^ n : F.H) : G) ∈ F.Li L 1 := (F.Li L 1).pow_mem hl n
  have hp : d.projection (d.action (l^n) v) = d.projection y := by
    rw [show d.projection (d.action (l^n) v) =
      d.naturalQuotient.action (d.qH (l^n)) (d.projection v) from
        LinearMap.congr_fun (d.projection.isIntertwining' (l^n)) v,
      map_pow, he, ← map_pow]
    exact (d.naturalQuotient.restriction _ _).trans hn'
  have hvy : d.action (l^n) v = y := by
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp (seed_disjoint_kernel d sep)
    · exact (tilde d V).sub_mem (image_invariant d hV (l^n) hln v hvV) hy
    · change d.projection (d.action (l^n) v - y) = 0
      rw [map_sub, hp, sub_self]
  exact hvy ▸ image_invariant d hS (l^n) hln v hvS
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
