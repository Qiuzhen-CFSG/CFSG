module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Six
public import Theory.Representation.BinaryNormalizerResidual.AlternatingNatural
public import Theory.Representation.BinaryNormalizerResidual

/-!
# Reducing the ambient six-space normalizer to its centralizer

The actual L₆ action is the natural A₈ action on the deleted eight-point
module. Relative normality in G₆ puts the whole G₆ action in its linear
normalizer, whose two-residual lies in the A₈ image. The original Sylow T
already acts through L₆, so Sylow supplementation gives equality of the
G₆ and L₆ action images. Returning through the original wedge coordinates
then gives G₆ = L₆ C_G(V₆), including an actual element factorization.

This proves the initial reduction in 12.5.4. It does not yet establish
C_G(V₆) ≤ N_G(L); that uses the point-component alternatives in the
remaining local argument. Sylow supplementation is retained explicitly,
so no equality between the full linear normalizer and the A₈ image is
asserted. Final assembly remains with qt-d-1251-local and qt-d-1251-source.

Source: Aschbacher--Smith, 12.5.4, printed p.819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Representation.SL5ExteriorSquare
open Representation.BinaryOffender Representation.BinaryNormalizerResidual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)
private def sixNaturalCoordinates : V₆ ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8) :=
  v6QuadraticIsometry.toLinearEquiv.trans
    Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv.symm
private def sixNaturalActor : a.Gi 6 →* (Module.End (ZMod 2) (BinaryPermutation.natural (Fin 8)))ˣ :=
  (unitConj sixNaturalCoordinates).toMonoidHom.comp a.sixAction.asGroupHom
omit [Finite G] in
private theorem sixNaturalActor_residual (l : a.Li 6) :
    a.sixNaturalActor (inclusion (a.Li_le_Gi 6) l) =
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)).asGroupHom
        (a.Li₆AlternatingActor l) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  change sixNaturalCoordinates (a.sixAction (inclusion (a.Li_le_Gi 6) l)
    (sixNaturalCoordinates.symm v)) =
      BinaryPermutation.naturalRepresentation (Fin 8) (a.Li₆AlternatingActor l) v
  apply Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv.injective
  change Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv
    (Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv.symm
      (v6QuadraticIsometry (a.sixAction (inclusion (a.Li_le_Gi 6) l)
        (sixNaturalCoordinates.symm v)))) = _
  rw [LinearEquiv.apply_symm_apply,
    Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv_permutation,
    a.sixAction_orthogonal]
  change Representation.BinaryLinearRecognition.orthogonalEightAction (a.Li₆AlternatingActor l)
    (v6QuadraticIsometry (sixNaturalCoordinates.symm v)) =
    Representation.BinaryLinearRecognition.orthogonalEightAction (a.Li₆AlternatingActor l)
      (Representation.BinaryLinearRecognition.naturalEightOrthogonalEquiv v)
  apply congrArg (Representation.BinaryLinearRecognition.orthogonalEightAction (a.Li₆AlternatingActor l))
  exact v6QuadraticIsometry.toLinearEquiv.apply_symm_apply _

private theorem sixNaturalActor_image :
    ((a.Li 6).subgroupOf (a.Gi 6)).map a.sixNaturalActor =
      actionImage (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨a.Li₆AlternatingActor ⟨l,hl⟩, (a.sixNaturalActor_residual ⟨l,hl⟩).symm⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨l,rfl⟩ := a.Li₆AlternatingActor_surjective g
    exact ⟨inclusion (a.Li_le_Gi 6) l, l.property, a.sixNaturalActor_residual l⟩
end ExteriorMarking

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original Sylow action on V₆ is already realized by L₆. -/
theorem sylow_sixAction (t : T) : ∃ l : s.marking.Li 6,
    s.marking.sixAction ⟨(t : G), s.sylow_le_Gi 6 (Or.inr (Or.inr (Or.inr rfl))) t.property⟩ =
      s.marking.sixAction (inclusion (s.marking.Li_le_Gi 6) l) := by
  let tH : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨t, (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) t.property⟩
  have ht : s.actor tH ∈ parabolicResidual 4 := by
    rw [parabolicResidual_four]
    exact flagGroup_le_parabolic 4 (by decide) (s.sylow_flag t)
  obtain ⟨l,hl⟩ := s.marking.residualActor_surjective 6
    (Or.inr (Or.inr (Or.inr rfl))) ⟨s.actor tH,ht⟩
  refine ⟨l, LinearMap.ext ?_⟩
  intro v
  let w := s.marking.V₆Coordinates.symm (Multiplicative.ofAdd v)
  have heT := s.equivariant tH ⟨w, s.marking.subspace_le _ w.property⟩
  have heL := s.marking.equivariant ⟨l, s.marking.Li_le_L 6 l.property⟩
    ⟨w, s.marking.subspace_le _ w.property⟩
  have heA : s.marking.quotientEquiv (QuotientGroup.mk' _ ⟨l,s.marking.Li_le_L 6 l.property⟩) =
      s.actor tH := (s.marking.residualActor_apply 6 _ l).symm.trans (congrArg Subtype.val hl)
  let tN : s.marking.Gi 6 :=
    ⟨t, s.sylow_le_Gi 6 (Or.inr (Or.inr (Or.inr rfl))) t.property⟩
  let lN : normalizer (s.marking.Vi 6 : Set G) := inclusion (s.marking.Li_le_Gi 6) l
  have heV : (s.marking.Vi 6).normalizerMonoidHom tN w =
      (s.marking.Vi 6).normalizerMonoidHom lN w := by
    apply Subtype.ext
    change (t : G) * (w : G) * (t : G)⁻¹ = (l : G) * (w : G) * (l : G)⁻¹
    exact congrArg (fun z : V => (z : G)) (s.marking.coordinates.injective
      (heT.trans (by rw [heA] at heL; exact heL.symm)))
  have heC := congrArg s.marking.V₆Coordinates heV
  rw [s.marking.sixAction_original, s.marking.sixAction_original] at heC
  have hw : s.marking.V₆Coordinates w = Multiplicative.ofAdd v :=
    s.marking.V₆Coordinates.apply_symm_apply _
  rw [hw] at heC
  exact congrArg Multiplicative.toAdd heC

private theorem sixNaturalActor_range_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.sixNaturalActor.range ≤
      actionImage (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) := by
  let H := s.marking.Gi 6
  let B := (s.marking.Li 6).subgroupOf H
  let A := actionImage (BinaryPermutation.alternatingNaturalRepresentation (Fin 8))
  let N := linearNormalizer (BinaryPermutation.alternatingNaturalRepresentation (Fin 8))
  let f := s.marking.sixNaturalActor
  let : B.Normal := (s.local_six_component_source h).2
  have hb : B.map f = A := s.marking.sixNaturalActor_image
  have hN : ∀ x, f x ∈ N := by
    intro x
    change f x ∈ normalizer (A : Set _)
    rw [←hb]
    exact B.le_normalizer_map f (mem_map_of_mem f (le_normalizer_of_normal (mem_top x)))
  let fN : H →* N := f.codRestrict N hN
  have hrN : (pResidual 2 N).map N.subtype ≤ A :=
    Representation.BinaryNormalizerResidual.alternating_natural_residual_le
      8 (Or.inr (Or.inr rfl))
  have hr : pResidual 2 H ≤ A.comap f := by
    intro x hx
    have hxN : f x ∈ (pResidual 2 N).map N.subtype :=
      mem_map_of_mem N.subtype
        (map_pResidual_le 2 fN (mem_map_of_mem fN hx))
    exact hrN hxN
  let S := T.subtype (s.sylow_le_Gi 6 (Or.inr (Or.inr (Or.inr rfl))))
  have ht : (S : Subgroup H) ≤ A.comap f := by
    intro t ht
    obtain ⟨l,hl⟩ := s.sylow_sixAction ⟨t,ht⟩
    have he : f t = f (inclusion (s.marking.Li_le_Gi 6) l) := by
      apply congrArg (unitConj ExteriorMarking.sixNaturalCoordinates)
      apply Units.ext
      exact hl
    rw [mem_comap, he, ←hb]
    exact mem_map_of_mem f l.property
  have hle : pResidual 2 H ⊔ (S : Subgroup H) ≤ A.comap f := sup_le hr ht
  have htop : pResidual 2 H ⊔ (S : Subgroup H) = ⊤ := pResidual_sup_sylow_eq_top S
  rw [htop] at hle
  rintro x ⟨g,rfl⟩
  exact hle (mem_top g)

/-- Every G₆ action on the original six-space is induced by L₆. -/
theorem sixAction_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (g : s.marking.Gi 6) :
    ∃ l : s.marking.Li 6, s.marking.sixAction g =
      s.marking.sixAction (inclusion (s.marking.Li_le_Gi 6) l) := by
  have hg := s.sixNaturalActor_range_le h ⟨g,rfl⟩
  rw [←s.marking.sixNaturalActor_image] at hg
  obtain ⟨l,hl,he⟩ := hg
  refine ⟨⟨l,hl⟩, ?_⟩
  exact (congrArg Units.val ((unitConj ExteriorMarking.sixNaturalCoordinates).injective he)).symm

/-- Actual element factorization in the ambient six-space normalizer. -/
theorem G₆_factorization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (g : G) (hg : g ∈ s.marking.Gi 6) :
    ∃ l ∈ s.marking.Li 6, ∃ c ∈ centralizer (s.marking.Vi 6 : Set G), l * c = g := by
  let gN : normalizer (s.marking.Vi 6 : Set G) := ⟨g,hg⟩
  obtain ⟨l,hl⟩ := s.sixAction_factorization h gN
  let lN : normalizer (s.marking.Vi 6 : Set G) := inclusion (s.marking.Li_le_Gi 6) l
  have ha : (s.marking.Vi 6).normalizerMonoidHom lN =
      (s.marking.Vi 6).normalizerMonoidHom gN := by
    apply MulEquiv.ext
    intro v
    apply s.marking.V₆Coordinates.injective
    have heL := s.marking.sixAction_original lN v
    have heG := s.marking.sixAction_original gN v
    rw [hl] at heG
    exact heL.trans heG.symm
  have hc : lN⁻¹ * gN ∈ (s.marking.Vi 6).normalizerMonoidHom.ker := by
    change (s.marking.Vi 6).normalizerMonoidHom (lN⁻¹ * gN) = 1
    rw [map_mul, map_inv, ha, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hc
  exact ⟨l, l.property, (l : G)⁻¹ * g, hc, mul_inv_cancel_left _ _⟩

/-- The first reduction in source 12.5.4 at i = 6. -/
theorem G₆_eq_L₆_sup_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.Gi 6 = s.marking.Li 6 ⊔ centralizer (s.marking.Vi 6 : Set G) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨l,hl,c,hc,rfl⟩ := s.G₆_factorization h g hg
    exact mul_mem (mem_sup_left hl) (mem_sup_right hc)
  · exact sup_le (s.marking.Li_le_Gi 6) (Subgroup.centralizer_le_normalizer _)

/-- Controlling the actual centralizer suffices for the ambient G₆ containment. -/
theorem G₆_le_M_iff (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.Gi 6 ≤ s.marking.M ↔ centralizer (s.marking.Vi 6 : Set G) ≤ s.marking.M := by
  rw [s.G₆_eq_L₆_sup_centralizer h, sup_le_iff]
  exact and_iff_right ((s.marking.Li_le_L 6).trans L.le_normalizer)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
