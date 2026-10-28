module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.SourceEscape
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.IsotropicPlanes
/-!
# The two genuine branches of the original plane-fusion argument

Every isotropic four-subgroup of the original V is carried from V₂ by an
actual element of L. The same even native marking and quotient map produce
that element, and faithfulness of the original coordinates identifies the
literal conjugate subgroup. For a conjugate V₂ˣ≤V, the other branch is the
completed normalizer-escape/C.1.24 reduction, retaining the nondegenerate
plane and its original conjugator for the two-A₃ argument.

Source: Aschbacher--Smith 13.5.6(2), printed p.917. The bad-plane branch is
not eliminated here: its actual two-A₃ product and nonabelian-core
contradiction remain separate source obligations.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing IsotropicPlanes
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem exists_local_plane_conjugate (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hi:∀x∈image d W,∀y∈image d W,form x y=0) :
    ∃l∈L,V₂.map (MulAut.conj l).toMonoidHom=W := by
  obtain ⟨a,ha⟩:=exists_even_plane_marking (image d W) (image_dim d W hWV 2 hcard) hi
  obtain ⟨b,_,hb⟩:=QuadraticSource.source_even_flag d
  let k:alternatingGroup (Fin 6):=a*b⁻¹
  obtain ⟨l,hl⟩:=QuadraticSource.exists_source_even_actor d k
  let lm:QuadraticSource.localModuleNormalizer (M:=M) (V:=V):=
    inclusion (QuadraticSource.L_le_local d) l
  have hV:V₂.map (MulAut.conj l.val).toMonoidHom≤V:=by
    rintro _ ⟨v,hv,rfl⟩
    exact mem_normalizer_iff.mp lm.property.2 v |>.mp (d.plane_le_seed.trans d.seed_le hv)
  refine ⟨l,l.property,QuadraticSource.image_injective_on_subgroups d hV hWV ?_⟩
  have hh:=QuadraticSource.image_conjugate_by_local d V₂ (d.plane_le_seed.trans d.seed_le) lm
  change image d (V₂.map (MulAut.conj l.val).toMonoidHom)=
    move (QuadraticSource.permutation d (inclusion (QuadraticSource.L_le_local d) l)) (image d V₂) at hh
  rw [hl,hb] at hh
  change image d (V₂.map (MulAut.conj l.val).toMonoidHom)=
    move (a.val*b.val⁻¹) (move b.val canonicalPlane) at hh
  rw [move_mul,move_inv] at hh
  exact hh.trans ha.symm

/-- The ordinary branch of the literal plane-fusion calculation. The
separate nonisotropic branch gives the actual block prefix above. -/
theorem source_plane_fusion_or_block
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (x:G)(hWV:V₂.map (MulAut.conj x).toMonoidHom≤V) :
    (∃l∈L,V₂.map (MulAut.conj x).toMonoidHom=V₂.map (MulAut.conj l).toMonoidHom) ∨
    ((¬∀v∈image d (V₂.map (MulAut.conj x).toMonoidHom),
        ∀w∈image d (V₂.map (MulAut.conj x).toMonoidHom),form v w=0) ∧
      ChapterC.IsAlternatingBlock L 6 ∧ (ChapterC.blockU L).map L.subtype=V ∧
      M≤normalizer (V:Set G) ∧ generalizedFitting M=pCore 2 M ∧
      primeRank 3 (M⊓normalizer (V₂.map (MulAut.conj x).toMonoidHom:Set G):Subgroup G)≤2) := by
  by_cases hi:∀v∈image d (V₂.map (MulAut.conj x).toMonoidHom),
      ∀w∈image d (V₂.map (MulAut.conj x).toMonoidHom),form v w=0
  · have hc:Nat.card (V₂.map (MulAut.conj x).toMonoidHom)=4:=by
      rw [card_map_of_injective (MulAut.conj x).injective,d.plane_card]
    obtain ⟨l,hl,he⟩:=exists_local_plane_conjugate d _ hWV hc hi
    exact Or.inl ⟨l,hl,he.symm⟩
  · exact Or.inr ⟨hi,source_block_of_nonisotropic_conjugate d hu x hWV hi⟩
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
