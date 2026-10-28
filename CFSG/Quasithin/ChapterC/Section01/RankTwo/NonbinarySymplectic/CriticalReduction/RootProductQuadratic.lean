module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.FullNaturalCoordinates
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticLifting
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductAction

/-!
# Quadraticity of the original root-product small-mover join

Keep one whole-vertex quotient marking together with its exact natural
indices and its central-cover quadratic lifting property. Align a containing
Sylow by inner conjugation and apply the root-product classification using
this same marking. The actual small-mover join is a full root pair, so its
second commutator on the entire U-alpha vanishes, including every fixed
central attachment. The original field degree is retained.

This is the quadratic input to the Baumann-Sylow construction in
RootProductBaumannSylow. Source: MS93 (5.1), printed p.913.
-/

public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original root-product premise gives quadratic action on the full U-layer. -/
theorem Input.replacement_root_product_quadratic
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ⁅⁅U d.radical a,Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2)⁆,
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2)⁆ = ⊥ := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hglobal,hidx,hquad⟩ := h.replacement_small_mover_quadratic_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier ^ 2)
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hJsub : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2)).subgroupOf S = J := by
    rw [←hjoin]
    exact comap_map_eq_self (by rw [S.subtype.ker_eq_bot S.subtype_injective]; exact bot_le)
  have hES₁ := hE₁.trans hTS
  have hES₂ := hE₂.trans hTS
  have hc (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ S) :
      f.ker.relIndex (A.subgroupOf S) = (Q d.radical a).relIndex A := by
    rw [hQeq,relIndex_subgroupOf hAS]
  have hi (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ S) :
      (centralizer (A.subgroupOf S : Set S)).relIndex U₀ =
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective,
      hUT,map_subgroupOf_eq_of_le hAS]
  have hp : (J : Set S) ⊆ (E₁.subgroupOf S : Set S) * (E₂.subgroupOf S : Set S) := by
    intro x hx
    obtain ⟨y,hy,z,hz,he⟩ := hprod (hjoin ▸ mem_map_of_mem S.subtype hx)
    exact ⟨⟨y,hES₁ hy⟩,hy,⟨z,hES₂ hz⟩,hz,Subtype.ext he⟩
  obtain ⟨s₁,s₂,hs₁,hs₂,hJ,heq⟩ := Degree.Quotient.root_product_join_eq U₀ T f
    unipotent.subtype Subtype.val_injective hkT hUK
    (by simpa only [range_subtype] using hTf) hidx
    (E₁.subgroupOf S) (E₂.subgroupOf S) (comap_mono hE₁) (comap_mono hE₂)
    (by rw [hc E₁ hES₁,hcard,hc₁]) (by rw [hi E₁ hES₁,hcard,hi₁])
    (by rw [hc E₂ hES₂,hcard,hc₂]) (by rw [hi E₂ hES₂,hcard,hi₂]) hp
  have hm (A : Subgroup S) (hAT : A ≤ T) :
      (Degree.Quotient.coordinates f unipotent.subtype A).map unipotent.subtype = A.map f :=
    Degree.Quotient.coordinates_map f unipotent.subtype A
      (by simpa only [range_subtype] using (map_mono hAT).trans hTf)
  have hJimage : J.map f = rootImage s₁ ⊔ rootImage s₂ := by
    rw [←hm _ (Subgroup.SmallMover.join_le _ _ _ _),hJ,Subgroup.map_sup]
  have hq := hquad J (hJimage.symm ▸ root_pair_quadratic s₁ s₂)
  have hh := congrArg (Subgroup.map S.subtype) hq
  rwa [map_commutator,map_commutator,hUT,hjoin,Subgroup.map_bot] at hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
