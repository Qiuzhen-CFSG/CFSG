module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.FlagCoordinates
public import Theory.Representation.G2BinaryNaturalNormalizer
/-!
# A compatible unitary action and original Sylow flag

The natural normal derived subgroup determines the full automizer embedding
by the binary G₂ normalizer theorem. A single inner conjugation places the
actual Sylow image in the positive roots and transports the linear action
at the same time. Derived-Sylow uniqueness then identifies the original
chosen invariant line, plane and three-space in that very coordinate frame.

All subgroups and maps are the original induced automizer and normalizer
actions. This removes independent coordinate and Sylow-placement premises
from the unitary point-closure source consumer.

Source: Aschbacher–Smith Notation13.3.3 and13.3.18, pp.885,894–895.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- An actual normal derived unitary action supplies a full natural marking
in which the original Sylow lies in the native positive-root group. -/
theorem exists_unitary_sylow_marking (T:Sylow 2 G) (L:Subgroup G)
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer V L) v,E0 (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v)) :
    ∃(rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W),
      (∀a v,E (automizerRepresentation V a v)=
        Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) ∧
      (inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent ∧
      commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho := by
  let I:=inducedAutomizer V L
  let : (L.subgroupOf (normalizer (V:Set G))).Normal:=
    (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  let : I.Normal:=Subgroup.Normal.map inferInstance V.normalizerMonoidHom.rangeRestrict
    V.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨rho0,_,hl,hfull⟩:=Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    (automizerRepresentation V) I e E0 he0 (automizerRepresentation_injective V)
  let E1:=E0.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv F)
  have he1:∀a v,E1 (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho0 a) (E1 v) := by
    intro a v
    change Atlas.G2.Restricted.NaturalCoordinates.equiv F (E0 (automizerRepresentation V a v))=_
    rw [hfull]
    exact (Atlas.G2.Restricted.NaturalCoordinates.repEquiv F).isIntertwining (rho0 a) (E0 v)
  have hd:commutator (Atlas.G2.Model F)≤I.map rho0 := by
    intro g hg
    obtain ⟨i,hi⟩:=e.surjective ⟨g,hg⟩
    exact ⟨i,i.prop,(hl i).trans (congrArg Subtype.val hi)⟩
  obtain ⟨g,hg⟩:=exists_sylow_image_marking T rho0
  let rho:Automizer V→*Atlas.G2.Model F:=(MulAut.conj g).toMonoidHom.comp rho0
  let α:=Atlas.G2.Restricted.NaturalCoordinates.action F
  let eg:W≃ₗ[F]W:=LinearEquiv.ofBijective (α g) (α.apply_bijective g)
  let E:=E1.trans eg
  have he:∀a v,E (automizerRepresentation V a v)=α (rho a) (E v) := by
    intro a v
    change α g (E1 (automizerRepresentation V a v))=α (g*rho0 a*g⁻¹) (α g (E1 v))
    rw [he1]
    change α g (α (rho0 a) (E1 v))=α (g*rho0 a*g⁻¹) (α g (E1 v))
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  have ht:(inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent:=by
    simpa only [rho,map_map] using hg
  have hd':commutator (Atlas.G2.Model F)≤I.map rho := by
    have hh:=map_mono (f:=(MulAut.conj g).toMonoidHom) hd
    have heq:(commutator (Atlas.G2.Model F)).map (MulAut.conj g).toMonoidHom=
        commutator (Atlas.G2.Model F):=Subgroup.Normal.map_conj_eq _ g
    rw [heq,map_map] at hh
    exact hh
  exact ⟨rho,E,he,ht,hd'⟩

/-- The original chosen Sylow-invariant flag and the entire automizer action
admit one compatible coordinate frame; no positions are independently assumed. -/
theorem exists_unitary_flag_marking (T:Sylow 2 G) (L Z B U0:Subgroup G)
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer V L) v,E0 (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hZV:Z≤V) (hBV:B≤V) (hUV:U0≤V)
    (hTZ:(T:Subgroup G)≤normalizer (Z:Set G))
    (hTB:(T:Subgroup G)≤normalizer (B:Set G))
    (hTU:(T:Subgroup G)≤normalizer (U0:Set G))
    (hZ:Nat.card Z=2) (hB:Nat.card B=4) (hU:Nat.card U0=8) :
    ∃(rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W),
      (∀a v,E (automizerRepresentation V a v)=
        Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) ∧
      (inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent ∧
      commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho ∧
      pointCoordinateSubspace E Z=pointLine ∧ pointCoordinateSubspace E B=plane ∧
      pointCoordinateSubspace E U0=seed := by
  obtain ⟨rho,E,he,ht,hd⟩:=exists_unitary_sylow_marking T L hLN hNL e E0 he0
  exact ⟨rho,E,he,ht,hd,source_flag_coordinates T Z B U0 rho E he hTN ht
    (hd.trans (map_le_range _ _)) hZV hBV hUV hTZ hTB hTU hZ hB hU⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
