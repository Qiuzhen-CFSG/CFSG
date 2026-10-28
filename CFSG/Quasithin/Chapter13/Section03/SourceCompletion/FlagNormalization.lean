module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PlaneAction
public import Theory.Representation.G2BinaryFlagNormalization
/-!
# Original source normalization from the marked unitary flag

The literal normalizer action transports the native point-plane incidence,
Sylow plane invariance and point-centralizer seed invariance to subgroups
of the original G. In particular L₁T normalizes V₃ because it centralizes
V₁; these are consequences of the same natural marking, not independent
geometric assumptions.

Source: Aschbacher–Smith 13.3.18(1), printed p.894.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative IsKleinFour
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

/-- Invariant native coordinates give the literal original subgroup normalizer. -/
theorem normalizes_marked_subgroup (A J:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hAV:A≤V) (hJN:J≤normalizer (V:Set G))
    (hpres:∀j:J,∀v∈pointCoordinateSubspace E A,
      Atlas.G2.Restricted.NaturalCoordinates.action F
        (rho (V.normalizerMonoidHom.rangeRestrict (inclusion hJN j))) v∈pointCoordinateSubspace E A) :
    J≤normalizer (A:Set G) := by
  apply le_normalizer_iff.mpr
  intro j hj a ha
  let v:Additive V:=Additive.ofMul ⟨a,hAV ha⟩
  have hh:=hpres ⟨j,hj⟩ (E v) ((mem_pointCoordinateSubspace E A v).mpr ha)
  rw [←he,mem_pointCoordinateSubspace] at hh
  exact hh

/-- The original Sylow normalizes the marked plane. -/
theorem sylow_normalizes_marked_plane (T:Sylow 2 G) (B:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp:pointCoordinateSubspace E B=plane) (hBV:B≤V)
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hT:(inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent) :
    (T:Subgroup G)≤normalizer (B:Set G) := by
  apply normalizes_marked_subgroup B (T:Subgroup G) rho E he hBV hTN
  intro t v hv
  rw [hp] at hv ⊢
  exact unipotent_preserves_plane _ (hT ⟨_,⟨inclusion hTN t,t.prop,rfl⟩,rfl⟩) v hv

/-- An original actor centralizing the marked point normalizes the seed.
This derives the local-invariance clause in F.9.1 from the natural action. -/
theorem point_centralizer_normalizes_marked_seed (U Z J:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E U=seed) (hz:pointCoordinateSubspace E Z=pointLine)
    (hUV:U≤V) (hJN:J≤normalizer (V:Set G)) (hJC:J≤centralizer (Z:Set G)) :
    J≤normalizer (U:Set G) := by
  apply normalizes_marked_subgroup U J rho E he hUV hJN
  intro j v hv
  let a:Automizer V:=V.normalizerMonoidHom.rangeRestrict (inclusion hJN j)
  have hp:rho a∈Atlas.G2.parabolic := by
    apply fixes_first_mem_parabolic
    obtain ⟨w,hw⟩:=E.surjective (Pi.single 0 1)
    have hwZ:w.toMul.val∈Z:=(mem_pointCoordinateSubspace E Z w).mp (by
      rw [hz,hw,mem_pointLine]
      intro i hi;simp [hi])
    rw [←hw,←he]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change j.val*w.toMul.val*j.val⁻¹=w.toMul.val
    rw [←mem_centralizer_iff.mp (hJC j.prop) _ hwZ,mul_inv_cancel_right]
  rw [hs] at hv ⊢
  exact pointParabolic_preserves_seed _ hp v hv

/-- The marked point is contained in the marked plane. -/
theorem marked_point_le_plane (Z B:Subgroup G) (E:Additive V≃ₗ[F]W)
    (hz:pointCoordinateSubspace E Z=pointLine) (hp:pointCoordinateSubspace E B=plane)
    (hZV:Z≤V) : Z≤B := by
  intro z hz'
  let w:Additive V:=Additive.ofMul ⟨z,hZV hz'⟩
  have hh:E w∈plane:=pointLine_le_plane (hz ▸ (mem_pointCoordinateSubspace E Z w).mpr hz')
  exact (mem_pointCoordinateSubspace E B w).mp (hp.symm ▸ hh)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
