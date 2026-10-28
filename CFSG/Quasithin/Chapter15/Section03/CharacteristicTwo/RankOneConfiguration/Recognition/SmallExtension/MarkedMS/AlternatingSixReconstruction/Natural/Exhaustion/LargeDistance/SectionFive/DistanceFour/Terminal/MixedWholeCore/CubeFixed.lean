module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds
public import Theory.Representation.BinaryOffender.IrreducibleQuotientDiagonal

/-!
# Cube normalizers preserve the complete mixed-edge fixed subgroup

The mixed plane and its enclosing three-pair cube have the same fixed space
on both permitted moved covers. A cube normalizer therefore preserves the
mixed-plane fixer. With full omega central generation, this preserves the
whole edge omega center, including the central attachment.

This is the full-kernel transport needed by the marked conjugator of
MS93 (5.12)(3); no equality of the mixed plane and cube is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

/-- The marked mixed plane has precisely the full cube's fixed space on
both the natural and augmentation moved covers. -/
theorem cover_mixed_fixed_eq_cube (v : S) :
    fixedSpace (coverAction s) (plus.map (MulAut.conj v).toMonoidHom) =
      fixedSpace (coverAction s) ((D 6).map (MulAut.conj v).toMonoidHom) := by
  have hcodim : fixedCodim (coverAction s) (plus.map (MulAut.conj v).toMonoidHom) =
      fixedCodim (coverAction s) ((D 6).map (MulAut.conj v).toMonoidHom) := by
    rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
    · rw [fixedCodim_map_equivariant (coverAction s) (naturalRepresentation (Fin 6))
          (MonoidHom.id S) E hE,
        fixedCodim_map_equivariant (coverAction s) (naturalRepresentation (Fin 6))
          (MonoidHom.id S) E hE,map_id,map_id,
        fixedCodim_map_conj,fixedCodim_map_conj,fixedCodim_plus.2.2.2,fixedCodim_D.2.2.2]
    · rw [fixedCodim_map_equivariant (coverAction s) (coreRepresentation (Fin 6))
          (MonoidHom.id S) E hE,
        fixedCodim_map_equivariant (coverAction s) (coreRepresentation (Fin 6))
          (MonoidHom.id S) E hE,map_id,map_id,
        fixedCodim_map_conj,fixedCodim_map_conj,fixedCodim_plus.2.2.1,fixedCodim_D.2.2.1]
  symm
  apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone _ (map_mono plus_le_D))
  have h1 := fixedCodim_add_finrank (coverAction s) (plus.map (MulAut.conj v).toMonoidHom)
  have h2 := fixedCodim_add_finrank (coverAction s) ((D 6).map (MulAut.conj v).toMonoidHom)
  omega

/-- A lift of a cube normalizer preserves the full moved-layer fixer of the
mixed plane under the actual quotient action. -/
theorem cube_normalizer_preserves_moved_fixer
    (E : Subgroup d.overgroup) (v : S)
    (hE : E.map s.projection = plus.map (MulAut.conj v).toMonoidHom)
    (g : d.overgroup)
    (hg : s.projection g ∈ normalizer (((D 6).map (MulAut.conj v).toMonoidHom) : Set S)) :
    g ∈ normalizer ((replacementMoved d ⊓ centralizer (E : Set d.overgroup) :
      Subgroup d.overgroup) : Set d.overgroup) := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have he := cover_mixed_fixed_eq_cube s v
  have hn := normalizer_le_fixedSpace_stabilizer (coverAction s)
    ((D 6).map (MulAut.conj v).toMonoidHom) hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨hx,hxc⟩
    have hU : g*x*g⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem x hx g
    let w : Additive U := Additive.ofMul ⟨x,hx⟩
    have hfix : w ∈ fixedSpace (coverAction s) ((D 6).map (MulAut.conj v).toMonoidHom) := by
      rw [←he,←hE]
      exact (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective hker E w).mpr hxc
    have hfix' := (hn w).2 hfix
    rw [←he,←hE] at hfix'
    refine ⟨hU,?_⟩
    have hh := (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective
      hker E ((coverAction s) (s.projection g) w)).mp hfix'
    rw [coverAction_conjugate s] at hh
    change g*x*g⁻¹ ∈ centralizer (E : Set d.overgroup) at hh
    exact hh
  · intro hx
    have hU : x ∈ U := by
      have hh := (inferInstance : U.Normal).conj_mem (g*x*g⁻¹) hx.1 g⁻¹
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_inv,inv_mul_cancel,mul_one] using hh
    let w : Additive U := Additive.ofMul ⟨x,hU⟩
    have hfix : (coverAction s) (s.projection g) w ∈
        fixedSpace (coverAction s) ((D 6).map (MulAut.conj v).toMonoidHom) := by
      rw [←he,←hE]
      apply (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective hker E _).mpr
      rw [coverAction_conjugate s]
      change g*x*g⁻¹ ∈ centralizer (E : Set d.overgroup)
      exact hx.2
    have hfix' := (hn w).1 hfix
    rw [←he,←hE] at hfix'
    exact ⟨hU,(NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective hker E w).mp hfix'⟩

/-- Central generation extends the moved-fixer normalization to the whole
omega center of an actual mixed-plane preimage. -/
theorem cube_normalizer_preserves_edge_omega
    (hsplit : omegaCenter (pCore 2 d.overgroup) = replacementMoved d ⊔
      (omegaCenter (pCore 2 d.overgroup) ⊓ center d.overgroup))
    (E : Subgroup d.overgroup) (hQE : pCore 2 d.overgroup ≤ E) (v : S)
    (hE : E.map s.projection = plus.map (MulAut.conj v).toMonoidHom)
    (g : d.overgroup)
    (hg : s.projection g ∈ normalizer (((D 6).map (MulAut.conj v).toMonoidHom) : Set S)) :
    g ∈ normalizer (omegaCenter E : Set d.overgroup) := by
  let Q := pCore 2 d.overgroup
  let U := replacementMoved d
  let X := omegaCenter Q
  let C := X ⊓ center d.overgroup
  have hUX : U ≤ X := by
    change replacementMoved d ≤ omegaCenter (pCore 2 d.overgroup)
    rw [hsplit]
    exact le_sup_left
  have hXg (k : d.overgroup) : k ∈ normalizer (X : Set d.overgroup) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change X.map (MulAut.conj k).toMonoidHom = X
    dsimp only [X]
    rw [←omegaCenter_map _ _ (MulAut.conj k).injective]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp (show k ∈ normalizer (Q : Set d.overgroup) from
      by dsimp only [Q]; rw [normalizer_eq_top]; exact mem_top k)
  have hCg (k : d.overgroup) : k ∈ normalizer (C : Set d.overgroup) :=
    inf_normalizer_le_normalizer_inf ⟨hXg k, by rw [normalizer_eq_top]; exact mem_top k⟩
  have decomp : omegaCenter E =
      (U ⊓ centralizer (E : Set d.overgroup)) ⊔ C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨_,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
      have hxQ : x ∈ Q := by
        change x ∈ pCore 2 d.overgroup
        rw [←moved_centralizer s]
        exact fun y hy => hxc y (hQE ((omegaCenter_le Q) (hUX hy)))
      have hxX : x ∈ X := mem_omegaCenter_iff.mpr
        ⟨hxQ,hx2,fun y hy => hxc y (hQE hy)⟩
      have hxprod : x ∈ (U : Set d.overgroup) * (C : Set d.overgroup) := by
        rw [←coe_mul_of_left_le_normalizer_right U C (fun k _ => hCg k)]
        exact hsplit ▸ hxX
      obtain ⟨w,hw,c,hc,rfl⟩ := hxprod
      have hcE : c ∈ centralizer (E : Set d.overgroup) :=
        fun y _ => mem_center_iff.mp hc.2 y
      have hwE : w ∈ centralizer (E : Set d.overgroup) := by
        have hh := (centralizer (E : Set d.overgroup)).mul_mem hxc
          ((centralizer (E : Set d.overgroup)).inv_mem hcE)
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem_sup ⟨hw,hwE⟩ hc
    · apply sup_le
      · rintro x ⟨hx,hxc⟩
        obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hUX hx)
        exact mem_omegaCenter_iff.mpr ⟨hQE hxQ,hx2,hxc⟩
      · rintro x ⟨hx,hxc⟩
        obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx
        exact mem_omegaCenter_iff.mpr ⟨hQE hxQ,hx2,
          fun y _ => mem_center_iff.mp hxc y⟩
  rw [decomp]
  exact normalizer_inf_normalizer_le_normalizer_sup _ _
    ⟨cube_normalizer_preserves_moved_fixer s E v hE g hg,hCg g⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
