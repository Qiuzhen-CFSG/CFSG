module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.DualSection

/-!
# Reverse Q_K product placement from the actual 14.7.71 pairing

The natural image of V in U/U₀ has binary rank two by the original module separation.
An actual nontrivial actor in Uα has a two-dimensional dual displacement;
its commutator with Q_K lies in the literal S∩Q_K because Q_K is in the
point two-core and T normalizes S. Therefore the image of S∩Q_K contains
the two-dimensional annihilator image of Q_K∩Q. The easy containment gives
the opposite inclusion, and the exact Q_K-section kernel C_H(U) lifts
image equality to the literal reverse product
Q_K∩Q=(S∩Q_K)C_H(U).

No containment S≤L₁ is used: S≤Q≤LT and the source product is formed with
subgroupOf H conventions throughout. The actor is used only to realize the
rank-two displacement; its existence comes from the earlier 14.7.66/69
placement and compatible upper marking.

Source: Aschbacher–Smith, Lemma 14.7.71, printed p.1075 (PDF p.1092),
equation (**), together with 14.5.21(1) and 14.7.66/69.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem natural_image_eq :
    (naturalSection d).imageSpace V = (tilde d V).map d.projection.toLinearMap := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := ((naturalSection d).mem_imageSpace_iff _ _).mp hv
    exact ⟨_, (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    exact ((naturalSection d).mem_imageSpace_iff _ _).mpr ⟨a, ha, rfl⟩

theorem seed_image_finrank (sep : d.ModuleSeparation) :
    Module.finrank (ZMod 2) ((naturalSection d).imageSpace V) = 2 := by
  let := finite_original d
  let f := d.projection.toLinearMap.comp (tilde d V).subtype
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    apply Subtype.ext
    exact Submodule.disjoint_def.mp (seed_disjoint_kernel d sep) w w.property hw
  have hr : f.range = (tilde d V).map d.projection.toLinearMap := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [natural_image_eq, ← hr, LinearMap.finrank_range_of_inj hi]
  exact seed_tilde_finrank d

private theorem natural_upper_range (t : SL2FourNatural.F) (ht : t ≠ 0) :
    (SL2FourNatural.naturalRepresentation (SL2FourNatural.upper t) - LinearMap.id).range =
      SL2FourNatural.upperFixed := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    rw [SL2FourNatural.mem_upperFixed]
    simp [SL2FourNatural.naturalRepresentation_apply, SL2FourNatural.upper_action]
  · intro hv
    have hv1 := SL2FourNatural.mem_upperFixed v |>.mp hv
    refine ⟨![0, v 0 / t], ?_⟩
    change SL2FourNatural.action (SL2FourNatural.upper t) ![0, v 0 / t] - ![0, v 0 / t] = v
    rw [SL2FourNatural.upper_action]
    funext i
    fin_cases i <;> simp [hv1, mul_div_cancel₀ _ ht]

private theorem upper_finrank : Module.finrank (ZMod 2) SL2FourNatural.upperFixed = 2 := by
  have h := SL2FourNatural.card_upperFixed
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (by decide : 4 = 2 ^ 2))

theorem dual_upper_displacement (a : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (ha : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    Module.finrank (ZMod 2) ((naturalAction d).dual a - 1).range = 2 := by
  have he : (naturalAction d).dual a - 1 =
      (SL2FourNatural.naturalRepresentation (SL2FourNatural.upper t) - LinearMap.id).dualMap := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (d.naturalQuotient.action (d.qH a⁻¹) v) - f v = f (_ - v)
    rw [map_inv, ha, ← map_inv]
    rw [show (SL2FourNatural.upper t)⁻¹ = SL2FourNatural.upper t by
      rw [SL2FourCentralCover.upper_transvection, Matrix.SpecialLinearGroup.transvection_inv,
        CharTwo.neg_eq]]
    change f (d.naturalQuotient.action (d.naturalQuotient.marking _) v) - f v = _
    rw [ChapterJ.L2FourAction.restriction, map_sub]
    rfl
  rw [he, LinearMap.finrank_range_dualMap_eq_finrank_range, natural_upper_range t ht, upper_finrank]

theorem source_commutator_le (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (b : QKDualCoordinates d) :
    ⁅c.Uα, QK F⁆ ≤ S F L ⊓ QK F := by
  apply le_inf
  · apply (commutator_mono (critical_le_S c e.conjugate) le_rfl).trans
    apply le_normalizer_iff_commutator_le_left.mp
    apply (QK_le_QH d e.sectionCentralizer).trans
    have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
      exact (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1))
    exact hQT.trans (SteinbergRecognition.T_normalizes_S d (d.natural.sylow_normalizes structural))
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((c.Uα_le_H e.images).trans b.qSection.normalized)

theorem intersection_image_finrank
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) (b : QKDualCoordinates d) :
    Module.finrank (ZMod 2) (b.qSection.imageSpace (QK F ⊓ Q T L)) = 2 := by
  rw [intersection_image_eq_annihilator d structural sep b]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq ((naturalSection d).imageSpace V)
  rw [seed_image_finrank d sep, SL2FourNatural.finrank_vector] at h
  omega

theorem source_intersection_image
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (b : QKDualCoordinates d) :
    b.qSection.imageSpace (S F L ⊓ QK F) = b.qSection.imageSpace (QK F ⊓ Q T L) := by
  obtain ⟨a, ha, t, ht, he⟩ := exists_upper_actor d c e.images mark e.image_order
  have hdisp := b.qSection.displacement_range_le_imageSpace_of_commutator_le
    c.Uα (S F L ⊓ QK F) (source_commutator_le d structural c e b) a ha
  have hle : b.qSection.imageSpace (S F L ⊓ QK F) ≤
      b.qSection.imageSpace (QK F ⊓ Q T L) :=
    b.qSection.imageSpace_mono (le_inf inf_le_right
      (inf_le_left.trans (S_le_Q d structural e.separation)))
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  calc
    _ = 2 := intersection_image_finrank d structural e.separation b
    _ = _ := (dual_upper_displacement d a t ht he).symm
    _ ≤ _ := Submodule.finrank_mono hdisp

theorem reverse_product
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (b : QKDualCoordinates d) :
    QK F ⊓ Q T L = (S F L ⊓ QK F) ⊔ C F := by
  apply le_antisymm ?_ (product_le_QK_intersection d structural e.separation)
  intro x hx
  let q : QK F := ⟨x, hx.1⟩
  have hmem : (b.qSection.coordinates q).toAdd ∈ b.qSection.imageSpace (S F L ⊓ QK F) := by
    rw [source_intersection_image d structural c e mark b]
    exact (b.qSection.mem_imageSpace_iff _ _).mpr ⟨q, hx, rfl⟩
  obtain ⟨r, hr, he⟩ := (b.qSection.mem_imageSpace_iff _ _).mp hmem
  have hk : (r⁻¹ * q : QK F).val ∈ C F := by
    apply (b.qSection.coordinates_eq_one_iff _).mp
    rw [map_mul, map_inv, Multiplicative.toAdd.injective he, inv_mul_cancel]
  have hq : (r * (r⁻¹ * q) : QK F).val ∈ (S F L ⊓ QK F) ⊔ C F :=
    mul_mem (mem_sup_left hr) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hq

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Equation (**) on the original subgroups, with the compatible dual
coordinates constructed from the earlier 14.5.21 pairing and commutator. -/
theorem source_product
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    QK F ⊓ centralizer (V : Set G) = QK F ⊓ Q T L ∧
    QK F ⊓ Q T L = (S F L ⊓ QK F) ⊔ C F := by
  obtain ⟨b⟩ := HAccounting.exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  exact ⟨QK_centralizer_eq_intersection d structural e.separation,
    reverse_product d structural c e mark b⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
