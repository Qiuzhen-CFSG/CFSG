module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AllComponentPlanes
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.PlaneChoice
public import Theory.SpecificGroups.SymplecticFour.SylowPlaneChoice
/-! # An original component plane whose normalizer escapes M
The source component lies outside M. The actual two parabolics generate its
model quotient, and the proved elementary full preimages give an intrinsic
maximum plane of S∩L whose component normalizer escapes M. The Sylow and
quotient witnesses are constructed in each surviving source branch.
Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.linear_simple_component_plane_escapes
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ¬L⊓normalizer (V:Set G)≤M := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩:=MathieuSourceSetup.exists_relative_component_sylow c
  have hk:IsPGroup 2 e.toMonoidHom.ker:=by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    exact IsPGroup.of_bot
  have hlift (W:Subgroup PSL(3,F)) (hW:IsElementaryAbelian 2 W):
      IsElementaryAbelian 2 (W.comap e.toMonoidHom):=by
    let :=hW
    exact IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective W
  have h:=Matrix.PSL3Even.ThompsonCentralCover.exists_maximum_escaping_normalizer_of_sylow
    L M (c.localSetup hG structural115Input localC129Input_knownSimple).outside
    e.toMonoidHom e.surjective hk P (by omega) hF hlift
  rwa [hP,subgroupOf_map_subtype] at h

theorem MathieuSourceSetup.linear_four_component_plane_escapes
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ¬L⊓normalizer (V:Set G)≤M := by
  obtain ⟨P,hP⟩:=MathieuSourceSetup.exists_relative_component_sylow c
  let q:=Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have hk:IsPGroup 2 q.ker:=by
    rw [Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker,
      MathieuSourceSetup.center_eq_twoCore c hG localC129Input_knownSimple hempty]
    exact pCore_isPGroup
  have hlift (W:Subgroup Matrix.PSL3Four.PSL) (hW:IsElementaryAbelian 2 W):
      IsElementaryAbelian 2 (W.comap q):=by
    let :=hW
    exact MathieuSourceSetup.linear_four_elementary_preimage c hG localC129Input_knownSimple hempty e W
  have h:=Matrix.PSL3Even.ThompsonCentralCover.exists_maximum_escaping_normalizer_of_sylow
    L M (c.localSetup hG structural115Input localC129Input_knownSimple).outside
    q (Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e) hk P
    (by decide : 0<2) (by simpa using Matrix.PSL3Four.card_F) hlift
  rwa [hP,subgroupOf_map_subtype] at h

theorem MathieuSourceSetup.derived_symplectic_component_plane_escapes
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ¬L⊓normalizer (V:Set G)≤M := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩:=MathieuSourceSetup.exists_relative_component_sylow c
  let e':=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  have hk:IsPGroup 2 e'.toMonoidHom.ker:=by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e'.injective]
    exact IsPGroup.of_bot
  have hlift (W:Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) (hW:IsElementaryAbelian 2 W):
      IsElementaryAbelian 2 (W.comap e'.toMonoidHom):=by
    let :=hW
    exact IsElementaryAbelian.comap_of_injective e'.toMonoidHom e'.injective W
  have h:=Theory.SpecificGroups.SymplecticFour.ThompsonInner.exists_maximum_escaping_normalizer_of_sylow
    L M (c.localSetup hG structural115Input localC129Input_knownSimple).outside
    e'.toMonoidHom e'.surjective hk P hn hF hlift
  rwa [hP,subgroupOf_map_subtype] at h
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
