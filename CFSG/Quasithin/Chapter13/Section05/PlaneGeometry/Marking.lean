module

public import CFSG.Quasithin.Chapter13.Section05.F9Application.PointCore
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.EvenFlag
/-!
# Simultaneous source flag marking and plane alignment

The original Sylow action marks V₁ and V₂ by one even permutation.
The original central quotient of L lifts every such permutation to an
actual element of L. The literal coordinate-conjugation formula therefore
aligns any compatibly marked plane by an element of L∩G₁.

In particular, the order-four alternative in the quadratic action of Vᵍ
has its actual commutator [V,Vᵍ] carried to V₂ by this source element.
This supplies the conjugation used before applying 13.5.6(3); it does not
assume the plane-fusion or core-identification conclusion of that lemma.

Source: Aschbacher--Smith, Notation 13.2.1 and proof of 13.5.7,
printed pp.877 and 917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_even_flag : ∃a:alternatingGroup (Fin 6),
    image d V₁=move a.val canonicalLine ∧ image d V₂=move a.val canonicalPlane := by
  let f:=Section07.NaturalAction.permutation d
  let Q:=(T.subtype (show (T:Subgroup G)≤L⊔T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ:(Q:Subgroup f.range).map f.range.subtype=
      ((T:Subgroup G).subgroupOf (L⊔T)).map f := by
    rw [Sylow.coe_mapSurjective,map_map,Sylow.coe_subtype]
    rfl
  apply sylow_even_flag_of_between f.range (alternating_le_range d) Q
    (image d V₁) (image d V₂)
    (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
    (image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2 d.plane_card)
  · intro x hx
    rw [hQ] at hx
    exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₁ d.line_stable hx)
  · intro x hx
    rw [hQ] at hx
    exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₂ d.plane_stable hx)

theorem exists_source_even_actor (a:alternatingGroup (Fin 6)) :
    ∃l:L,permutation d (inclusion (L_le_local d) l)=a.val := by
  obtain ⟨q,hq⟩:=d.local_quotient.surjective a
  obtain ⟨l,hl⟩:=QuotientGroup.mk'_surjective _ q
  refine ⟨l,?_⟩
  change (local_permutation_extension d).choose (inclusion (L_le_local d) l)=a.val
  rw [(local_permutation_extension d).choose_spec.1 l,hl,hq]

theorem image_conjugate_by_local (X:Subgroup G) (hX:X≤V)
    (l:localModuleNormalizer (M:=M) (V:=V)) :
    image d (X.map (MulAut.conj l.val).toMonoidHom)=
      move (permutation d l) (image d X) := by
  ext w
  constructor
  · intro hw
    obtain ⟨v,⟨x,hx,he⟩,hv⟩:=(mem_image d _ w).mp hw
    let xV:V:=⟨x,hX hx⟩
    refine ⟨(d.coordinate xV).toAdd,(mem_image d X _).mpr ⟨xV,hx,rfl⟩,?_⟩
    rw [←conjugation d l xV,←hv]
    apply congrArg (fun v:V=>(d.coordinate v).toAdd)
    exact Subtype.ext he
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨v,hv,rfl⟩:=(mem_image d X w).mp hw
    apply (mem_image d _ _).mpr
    refine ⟨V.normalizerMonoidHom ⟨l.val,l.property.2⟩ v,⟨v.val,hv,rfl⟩,?_⟩
    exact conjugation d l v

theorem image_injective_on_subgroups {A B:Subgroup G} (hA:A≤V) (hB:B≤V)
    (he:image d A=image d B) : A=B := by
  apply le_antisymm
  · intro a ha
    have hm:(d.coordinate ⟨a,hA ha⟩).toAdd∈image d B :=
      he ▸ (mem_image d A _).mpr ⟨⟨a,hA ha⟩,ha,rfl⟩
    obtain ⟨b,hb,hba⟩:=(mem_image d B _).mp hm
    have hba':b=⟨a,hA ha⟩:=d.coordinate.injective hba
    have he':b.val=a:=congrArg Subtype.val hba'
    rwa [←he']
  · intro b hb
    have hm:(d.coordinate ⟨b,hB hb⟩).toAdd∈image d A :=
      he.symm ▸ (mem_image d B _).mpr ⟨⟨b,hB hb⟩,hb,rfl⟩
    obtain ⟨a,ha,hab⟩:=(mem_image d A _).mp hm
    have hab':a=⟨b,hB hb⟩:=d.coordinate.injective hab
    have he':a.val=b:=congrArg Subtype.val hab'
    rwa [←he']
theorem exists_source_plane_alignment (W:Subgroup G) (hW:W≤V)
    (a:alternatingGroup (Fin 6)) (hline:image d V₁=move a.val canonicalLine)
    (hplane:image d W=move a.val canonicalPlane) :
    ∃l∈L⊓G₁,W.map (MulAut.conj l).toMonoidHom=V₂ := by
  obtain ⟨b,hbline,hbplane⟩:=source_even_flag d
  let k:alternatingGroup (Fin 6):=b*a⁻¹
  obtain ⟨l,hl⟩:=exists_source_even_actor d k
  let lM:localModuleNormalizer (M:=M) (V:=V):=inclusion (L_le_local d) l
  have hn:l.val∈normalizer (V:Set G):=lM.property.2
  have hnorm {X:Subgroup G} (hX:X≤V) : X.map (MulAut.conj l.val).toMonoidHom≤V := by
    rintro _ ⟨x,hx,rfl⟩
    exact (mem_normalizer_iff.mp hn x).mp (hX hx)
  have hkline:move k.val (image d V₁)=image d V₁ := by
    rw [hline]
    change move (b.val*a.val⁻¹) (move a.val canonicalLine)=_
    rw [move_mul,move_inv,←hbline,hline]
  have hkplane:move k.val (image d W)=image d V₂ := by
    rw [hplane]
    change move (b.val*a.val⁻¹) (move a.val canonicalPlane)=_
    rw [move_mul,move_inv,←hbplane]
  have heLine:V₁.map (MulAut.conj l.val).toMonoidHom=V₁ := by
    apply image_injective_on_subgroups d
      (hnorm (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)))
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
    have he:=image_conjugate_by_local d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) lM
    change image d (V₁.map (MulAut.conj l.val).toMonoidHom)=
      move (permutation d (inclusion (L_le_local d) l)) (image d V₁) at he
    rw [hl] at he
    exact he.trans hkline
  refine ⟨l.val,⟨l.property,?_⟩,?_⟩
  · rw [d.first_normalizer]
    exact mem_normalizer_iff_map_conj_eq.mpr heLine
  · apply image_injective_on_subgroups d (hnorm hW) (d.plane_le_seed.trans d.seed_le)
    have he:=image_conjugate_by_local d W hW lM
    change image d (W.map (MulAut.conj l.val).toMonoidHom)=
      move (permutation d (inclusion (L_le_local d) l)) (image d W) at he
    rw [hl] at he
    exact he.trans hkplane

/-- The order-four alternative is aligned by an actual element of L∩G₁. -/
theorem conjugate_commutator_four_alignment (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hcard:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=4) :
    ∃l∈L⊓G₁,(⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj l).toMonoidHom=V₂ := by
  obtain ⟨a,ha,hp⟩:=conjugate_commutator_four_plane d g hg hc hcomm hs hcard
  exact exists_source_plane_alignment d _ (hcomm.trans inf_le_left) a ha hp

end CFSG.Quasithin.Chapter13.Section05.QuadraticSource
