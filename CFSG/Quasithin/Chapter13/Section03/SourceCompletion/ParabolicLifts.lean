module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.F9Application
public import Theory.Representation.G2BinaryParabolicFrame
public import Theory.GroupTheory.SylowNormalizedResidual
/-!
# Lifting the marked point and plane actors from the original component

The point parabolic lifts into the actual point centralizer, which is
covered by its two-residual and the ambient Sylow. The plane cubic lifts
through the actual plane normalizer and then through its two-residual
because its order is odd. No full plane-parabolic image is asserted for
that residual. All actors retain the original natural-module frame.

Source: Aschbacher–Smith 13.3.18, printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- Odd-order elements of the literal action image lift from the actual
two-residual, without assuming an odd-order lift in the original group. -/
theorem odd_actor_mem_induced_residual (K:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (hKN:K≤normalizer (V:Set G))
    (g:Atlas.G2.Model F) (hg:g∈(inducedAutomizer V K).map rho)
    (ho:Nat.Coprime 2 (orderOf g)) :
    g∈(inducedAutomizer V ((pResidual 2 K).map K.subtype)).map rho := by
  let N:=normalizer (V:Set G)
  let A:=K.subgroupOf N
  let f:N→*Atlas.G2.Model F:=rho.comp V.normalizerMonoidHom.rangeRestrict
  let R:Subgroup G:=(pResidual 2 K).map K.subtype
  have hRN:R≤N:=(map_subtype_le _).trans hKN
  have hR:((pResidual 2 A).map A.subtype).map N.subtype=R := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hKN]
  have hRn:R.subgroupOf N=(pResidual 2 A).map A.subtype := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hRN,hR]
  have hgm:g∈A.map f:=by
    change g∈((K.subgroupOf N).map V.normalizerMonoidHom.rangeRestrict).map rho at hg
    rwa [map_map] at hg
  have hh:g∈(pResidual 2 (A.map f)).map (A.map f).subtype :=
    ⟨⟨g,hgm⟩,mem_pResidual_of_orderOf_coprime (by simpa only [Subgroup.orderOf_mk] using ho),rfl⟩
  rw [←map_embedded_pResidual] at hh
  change g∈((R.subgroupOf N).map V.normalizerMonoidHom.rangeRestrict).map rho
  rw [map_map,hRn]
  exact hh

/-- L₁T covers the native point parabolic in the same actual module frame.
The Sylow supplies the two-part; L₁ remains the literal two-residual. -/
theorem source_point_parabolic_covered
    (T:Sylow 2 G) (L Z:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz:pointCoordinateSubspace E Z=pointLine) (hZV:Z≤V)
    (hTC:(T:Subgroup G)≤centralizer (Z:Set G))
    (hTL:(T:Subgroup G)≤normalizer (L:Set G))
    (hderived:commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho) :
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer V (((pResidual 2 (L⊓centralizer (Z:Set G):Subgroup G)).map
        (L⊓centralizer (Z:Set G)).subtype)⊔(T:Subgroup G))).map rho := by
  let K:=L⊓centralizer (Z:Set G)
  have hTK:(T:Subgroup G)≤normalizer (K:Set G):=
    (le_inf hTL ((hTC.trans (Subgroup.centralizer_le_normalizer _)).trans
      (normalizer_le_normalizer_centralizer Z))).trans inf_normalizer_le_normalizer_inf
  have hcover:=le_embedded_pResidual_sup_sylow_of_normalizes T K hTK
  intro g hg
  obtain ⟨i,⟨n,hnL,rfl⟩,hnative⟩:=hderived hg.2
  have hnC:n.val∈centralizer (Z:Set G) := by
    intro z hz'
    let v:Additive V:=Additive.ofMul ⟨z,hZV hz'⟩
    have hv:E v∈pointLine:=hz ▸ (mem_pointCoordinateSubspace E Z v).mpr hz'
    have hf:=pointParabolic_fixes_pointLine g hg.1 (E v) hv
    rw [←hnative,←he] at hf
    have hh:n.val*z*n.val⁻¹=z:=congrArg (fun w:Additive V=>(w.toMul:G)) (E.injective hf)
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact ⟨_,⟨n,hcover ⟨hnL,hnC⟩,rfl⟩,hnative⟩

/-- The actual plane residual supplies its cubic actor. It is not assumed
to cover the whole plane parabolic, whose two-quotient is nontrivial. -/
theorem source_plane_residual_cubic
    (L B:Subgroup G) (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hp:pointCoordinateSubspace E B=plane) (hBV:B≤V)
    (hLN:L≤normalizer (V:Set G))
    (hderived:commutator (Atlas.G2.Model F)≤(inducedAutomizer V L).map rho) :
    Atlas.G2.BinaryParabolicPair.cubicActor∈
      (inducedAutomizer V ((pResidual 2 (L⊓normalizer (B:Set G):Subgroup G)).map
        (L⊓normalizer (B:Set G)).subtype)).map rho := by
  apply odd_actor_mem_induced_residual _ rho (inf_le_left.trans hLN)
  · obtain ⟨i,⟨n,hnL,rfl⟩,hnative⟩:=hderived Atlas.G2.BinaryParabolicPair.cubicActor_mem_derived
    have hnB:n.val∈normalizer (B:Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hmap:B.map (MulAut.conj n.val).toMonoidHom≤B := by
        rintro _ ⟨b,hb,rfl⟩
        let v:Additive V:=Additive.ofMul ⟨b,hBV hb⟩
        have hv:E v∈plane:=hp ▸ (mem_pointCoordinateSubspace E B v).mpr hb
        have hf:=plane_cubic_preserves (E v) hv
        rw [←hnative,←he,←hp,mem_pointCoordinateSubspace] at hf
        exact hf
      apply eq_of_le_of_card_ge hmap
      rw [card_map_of_injective (MulAut.conj n.val).injective]
    exact ⟨_,⟨n,⟨hnL,hnB⟩,rfl⟩,hnative⟩
  · rw [Atlas.G2.BinaryParabolicPair.cubicActor_order]
    decide
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
