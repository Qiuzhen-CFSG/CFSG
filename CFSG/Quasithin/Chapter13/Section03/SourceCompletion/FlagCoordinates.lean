module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SylowImage
public import Theory.Representation.G2BinarySylowThreeSpace
/-!
# Coordinates of the original chosen binary unitary flag

The marked original Sylow image contains the actual derived Sylow.
Transporting invariance through the literal normalizer action puts each
chosen flag subgroup into its unique native invariant line, plane or
three-space. The original subgroup cardinalities determine the dimensions;
all coordinate equalities use the same linear equivalence.

Source: Aschbacher–Smith Notation13.3.3, printed p.885, as used in13.3.18.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Natural.OrthogonalCover.SylowFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem natural_coordinate_invariant (T:Sylow 2 G) (A:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hTA:(T:Subgroup G)≤normalizer (A:Set G))
    (hS:Atlas.G2.unipotent⊓commutator (Atlas.G2.Model F)≤
      (inducedAutomizer V (T:Subgroup G)).map rho) :
    ∀g:U F,(pointCoordinateSubspace E A).comap (coord F).toLinearMap≤
      ((pointCoordinateSubspace E A).comap (coord F).toLinearMap).comap
        (Atlas.G2.Natural.derivedAction F g.val) := by
  intro g x hx
  obtain ⟨i,⟨n,hnT,rfl⟩,hnative⟩:=hS ⟨g.prop,g.val.prop⟩
  change rho (V.normalizerMonoidHom.rangeRestrict n)=g.val.val at hnative
  change coord F (Atlas.G2.Natural.derivedAction F g.val x)∈pointCoordinateSubspace E A
  rw [coordinates_action]
  obtain ⟨v,hv⟩:=E.surjective (coord F x)
  rw [←hnative,←hv,←he,mem_pointCoordinateSubspace]
  have hvA:v.toMul.val∈A:=(mem_pointCoordinateSubspace E A v).mp (hv.symm ▸ hx)
  exact (mem_normalizer_iff.mp (hTA hnT) v.toMul.val).mp hvA

omit [Finite G] in
private theorem natural_coordinate_finrank (A:Subgroup G)
    (E:Additive V≃ₗ[F]W) (hAV:A≤V) (n:ℕ) (hc:Nat.card A=2^n) :
    Module.finrank F ((pointCoordinateSubspace E A).comap (coord F).toLinearMap)=n := by
  have hd:Module.finrank F (pointCoordinateSubspace E A)=n := by
    have hh:=Module.natCard_eq_pow_finrank (K:=F) (V:=pointCoordinateSubspace E A)
    rw [card_pointCoordinateSubspace E A hAV,Nat.card_zmod,hc] at hh
    exact (Nat.pow_right_injective (by decide:1<(2:ℕ)) hh).symm
  have hh:=(coord F).finrank_map_eq ((pointCoordinateSubspace E A).comap (coord F).toLinearMap)
  rw [Submodule.map_comap_eq_of_surjective (coord F).surjective] at hh
  exact hh.symm.trans hd

private theorem N1_eq_coordinate_point : N1 F=pointLine.comap (coord F).toLinearMap := by
  ext x
  rw [mem_N1,Submodule.mem_comap,mem_pointLine]
  simp only [LinearEquiv.coe_coe]
  constructor
  · rintro ⟨a,ha⟩ i hi
    rw [ha]
    fin_cases i <;>simp_all
  · intro h
    refine ⟨coord F x 0,?_⟩
    ext i;fin_cases i
    · rfl
    · exact h 1 (by decide)
    · exact h 2 (by decide)
    · exact h 3 (by decide)
    · exact h 4 (by decide)
    · exact h 5 (by decide)

private theorem naturalPlane_eq_coordinate_plane :
    Atlas.G2.Natural.OrthogonalCover.naturalPlane F=plane.comap (coord F).toLinearMap := by
  ext x
  rw [mem_naturalPlane,Submodule.mem_comap,mem_plane]
  simp only [LinearEquiv.coe_coe]
  constructor
  · rintro ⟨a,b,ha⟩;rw [ha];simp
  · rintro ⟨h2,h3,h4,h5⟩
    refine ⟨coord F x 0,coord F x 1,?_⟩
    ext i;fin_cases i
    · rfl
    · rfl
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-- The original chosen T-invariant subgroups of orders two, four and eight
have the required coordinates in the same positive-root action marking. -/
theorem source_flag_coordinates (T:Sylow 2 G) (Z B U0:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hT:(inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent)
    (hd:commutator (Atlas.G2.Model F)≤rho.range)
    (hZV:Z≤V) (hBV:B≤V) (hUV:U0≤V)
    (hTZ:(T:Subgroup G)≤normalizer (Z:Set G))
    (hTB:(T:Subgroup G)≤normalizer (B:Set G))
    (hTU:(T:Subgroup G)≤normalizer (U0:Set G))
    (hZ:Nat.card Z=2) (hB:Nat.card B=4) (hU:Nat.card U0=8) :
    pointCoordinateSubspace E Z=pointLine ∧ pointCoordinateSubspace E B=plane ∧
      pointCoordinateSubspace E U0=seed := by
  have hS:=derived_sylow_le_induced_sylow T rho hTN hT hd
  have hZi:=natural_coordinate_invariant T Z rho E he hTZ hS
  have hBi:=natural_coordinate_invariant T B rho E he hTB hS
  have hUi:=natural_coordinate_invariant T U0 rho E he hTU hS
  have hZe:=invariant_line_unique F _ hZi (natural_coordinate_finrank Z E hZV 1 (by simpa using hZ))
  have hBe:=invariant_plane_unique F _ hBi (natural_coordinate_finrank B E hBV 2 (by simpa using hB))
  have hUe:=invariant_three_unique_binary _ hUi (natural_coordinate_finrank U0 E hUV 3 (by simpa using hU))
  rw [N1_eq_coordinate_point] at hZe
  rw [naturalPlane_eq_coordinate_plane] at hBe
  exact ⟨Submodule.comap_injective_of_surjective (coord F).surjective hZe,
    Submodule.comap_injective_of_surjective (coord F).surjective hBe,
    Submodule.comap_injective_of_surjective (coord F).surjective hUe⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
