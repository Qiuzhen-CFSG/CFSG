module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Quotient
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.Marking
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The full original plane normalizer preserves the cubic preimage

The permutation action of M preserving V restricts to the specified L→A₆
quotient. Consequently N_M(W) normalizes the preimage in L of any subgroup
normalized by the native plane stabilizer. Conversely, fixation of the
coordinate plane by a local image means normalization of the original W.
These statements preserve the ambient subgroup maps and include the
possible central two-kernel of the short block.

Source: Aschbacher–Smith13.5.6, printed p.917.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)


theorem localMap_eq_full (l:L) : localMap d l=
    QuadraticSource.permutation d (inclusion (QuadraticSource.L_le_local d) l) :=
  ((QuadraticSource.local_permutation_extension d).choose_spec.1 l).symm

theorem localMap_conjugation
    (g:QuadraticSource.localModuleNormalizer (M:=M) (V:=V)) (l:L) :
    ∃k:L, k.val=(g:G)*l*(g:G)⁻¹ ∧ localMap d k=
      QuadraticSource.permutation d g*localMap d l*(QuadraticSource.permutation d g)⁻¹ := by
  have hg : (g:G)∈normalizer (L:Set G) := d.local_normalizer ▸ g.property.1
  let k:L:=⟨(g:G)*l*(g:G)⁻¹,(mem_normalizer_iff.mp hg l).mp l.property⟩
  refine ⟨k,rfl,?_⟩
  rw [localMap_eq_full d k,localMap_eq_full d l]
  have he : inclusion (QuadraticSource.L_le_local d) k=
      g*inclusion (QuadraticSource.L_le_local d) l*g⁻¹ := Subtype.ext rfl
  rw [he,map_mul,map_mul,map_inv]

theorem plane_normalizes_preimage
    (hMV:M≤normalizer (V:Set G)) (W:Subgroup G) (hWV:W≤V)
    (D:Subgroup (Equiv.Perm (Fin 6)))
    (hD:Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.flagStabilizer (image d W)≤normalizer (D:Set _)) :
    M⊓normalizer (W:Set G)≤normalizer ((D.comap (localMap d)).map L.subtype : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨l,hl,rfl⟩ := hx
  let gM:QuadraticSource.localModuleNormalizer (M:=M) (V:=V):=⟨g,hg.1,hMV hg.1⟩
  obtain ⟨k,hk,hf⟩:=localMap_conjugation d gM l
  refine ⟨k,?_,hk⟩
  change localMap d k∈D
  rw [hf]
  have hs : QuadraticSource.permutation d gM∈
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.flagStabilizer (image d W) := by
    apply (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.mem_stabilizer_iff_map _ _).mpr
    have he:=QuadraticSource.image_conjugate_by_local d W hWV gM
    change image d (W.map (MulAut.conj g).toMonoidHom)=_ at he
    have hm : W.map (MulAut.conj g).toMonoidHom=W := mem_normalizer_iff_map_conj_eq.mp hg.2
    rw [hm] at he
    exact he.symm
  exact (mem_normalizer_iff.mp (hD hs) (localMap d l)).mp hl

theorem normalizes_plane_of_localMap_stabilizes (P:Subgroup L)
    (W:Subgroup G) (hWV:W≤V)
    (hs:P.map (localMap d)≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.flagStabilizer (image d W)) :
    P.map L.subtype≤normalizer (W:Set G) := by
  rintro _ ⟨p,hp,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hpV:p.val∈normalizer (V:Set G):=d.normalizes_V (mem_sup_left p.property)
  apply QuadraticSource.image_injective_on_subgroups d ?_ hWV
  · have he:=QuadraticSource.image_conjugate_by_local d W hWV
      (inclusion (QuadraticSource.L_le_local d) p)
    have hs':=Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.mem_stabilizer_iff_map
      (image d W) (localMap d p) |>.mp (hs (mem_map_of_mem (localMap d) hp))
    rw [←localMap_eq_full d p] at he
    exact he.trans hs'
  · rintro _ ⟨w,hw,rfl⟩
    exact (mem_normalizer_iff.mp hpV w).mp (hWV hw)

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
