module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.Thompson
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CocodeContainment

/-!
# The original cocode contains the source three-space

Let U be the common Sylow already constructed for the original Mathieu
inputs. Its Thompson subgroup W is the conjugate of the original cocode
under the retained conjugator fixing z. Mutual normalization of W and
the three-space Z puts every displacement of Z on W in Z. The native
cocode involution bound then gives Z ≤ C_G(W)=W, hence W ≤ S=C_G(Z).

Each original point core at a nonzero point of Z normalizes W, because
its product with W is a two-group containing the Sylow Thompson subgroup.
Thus K U ≤ N_G(W). The same conjugator identifies N_G(W) with the original
component, and self-centralization identifies its literal quotient by W
with M24. The quotient formula, cocode coordinates and image of the same U
are retained together. No new premise is added to the original inputs.

This supplies the three-space containment and normalization clauses used
by the earlier local geometry. The original alternating Sylow image,
compatible Todd splitting, hexad overlaps and unconditional recognition
still require their source proofs.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.6)--(4.8), pp.598--599, DOI 10.1007/BF01232280;
the original Aschbacher--Smith 8.2.12--14 marked Mathieu application.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- The original self-centralizing cocode subgroup stays self-centralizing under the same conjugation. -/
theorem sourceOrbit_m24_conjugate_selfCentralizing (g : G) :
    centralizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) =
      D.sourceOrbit.map (MulAut.conj g).toMonoidHom := by
  have hh := Theory.GroupTheory.map_centralizer_equiv (D.sourceOrbit : Set G) (MulAut.conj g)
  rw [sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot] at hh
  exact hh.symm

/-- The original cocode marking forces the three-space inside the same Thompson subgroup,
and every original point core normalizes that subgroup. -/
theorem sourceOrbit_m24_common_thompson_contains_space
    {cubic : Recognition.JankoFour.CubicAutomorphismQuotient
      (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G))}
    {X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)}
    (d : ThreeSpaceData (z : G) cubic X) (U : Sylow 2 G) (g : G)
    (hUN : (U : Subgroup G) ≤ normalizer (d.space : Set G))
    (hZU : d.space ≤ (U : Subgroup G))
    (hJ : D.sourceOrbit.map (MulAut.conj g).toMonoidHom =
      elementaryAbelianMaxJ (U : Subgroup G)) :
    d.space ≤ elementaryAbelianMaxJ (U : Subgroup G) ∧
      elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S ∧
      d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) := by
  let W := D.sourceOrbit.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 d.space := d.elementary
  let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj g)).symm.trans a
  let E' := (automizerModuleEquiv D.sourceOrbit (MulAut.conj g)).symm.trans E
  let f : normalizer (W : Set G) →* M24 :=
    a'.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hm : ∀ b v, E' (elementaryRepresentation (p := 2) W.normalizerMonoidHom b v) =
      cocodeRepresentation (f b) (E' v) := by
    intro b v
    exact sourceOrbit_m24_conjugate_cocode D a E hE g
      (W.normalizerMonoidHom.rangeRestrict b) v
  have hJU : elementaryAbelianMaxJ (U : Subgroup G) ≤ (U : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hWN : W ≤ normalizer (d.space : Set G) := (hJ.le.trans hJU).trans hUN
  have hZN : d.space ≤ normalizer (W : Set G) := by
    dsimp only [W]
    rw [hJ]
    exact hZU.trans ((U : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  have hZC := cocode_small_normalized_centralizes W d.space f E' hm hZN hWN
    (by have hc : Nat.card d.space = 8 := d.card; omega)
  have hCW : centralizer (W : Set G) = W :=
    sourceOrbit_m24_conjugate_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot g
  have hZW : d.space ≤ W := hZC.trans_eq hCW
  have hWS : W ≤ d.S :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hZW)
  refine ⟨hZW.trans_eq hJ, hJ ▸ hWS, ?_⟩
  change (⨆ t : {t : G // t ∈ d.space ∧ t ≠ 1}, Recognition.JankoFour.ambientCore t.val) ≤ _
  apply iSup_le
  intro t
  apply ambientCore_le_normalizer_thompson
    (d.point_type (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)
      t.property.1 t.property.2) U
  rw [←hJ]
  exact hZC t.property.1

/-- The literal quotient of the transported full normalizer by its cocode subgroup,
with its original M24 marking retained on every normalizer element. -/
theorem sourceOrbit_m24_conjugate_normalizer_quotient (g : G) :
    let W := D.sourceOrbit.map (MulAut.conj g).toMonoidHom
    let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj g)).symm.trans a
    ∃ e : (normalizer (W : Set G) ⧸ W.subgroupOf (normalizer (W : Set G))) ≃* M24,
      ∀ n : normalizer (W : Set G),
        e (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) n) =
          a' (W.normalizerMonoidHom.rangeRestrict n) := by
  let W := D.sourceOrbit.map (MulAut.conj g).toMonoidHom
  let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj g)).symm.trans a
  let f : normalizer (W : Set G) →* M24 :=
    a'.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a'.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a'.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,
      sourceOrbit_m24_conjugate_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot g]
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), ?_⟩
  intro n
  rfl

/-- The same original three-space, common Sylow, conjugator and cocode marking
supply Z ≤ J(U) ≤ S, K U ≤ N_G(J(U)), and the actual marked M24 quotient. -/
theorem sourceOrbit_m24_three_space_thompson_overlap :
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X)
      (U : Sylow 2 G) (g : centralizer ({(z : G)} : Set G)),
      (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G) ⊓ normalizer (d.space : Set G) ∧
      d.R ≤ (U : Subgroup G) ∧
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (U : Subgroup G) ∧
      D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom = elementaryAbelianMaxJ (U : Subgroup G) ∧
      d.space ≤ elementaryAbelianMaxJ (U : Subgroup G) ∧
      elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S ∧
      IsElementaryAbelian 2 (elementaryAbelianMaxJ (U : Subgroup G)) ∧
      Nat.card (elementaryAbelianMaxJ (U : Subgroup G)) = 2048 ∧
      centralizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        elementaryAbelianMaxJ (U : Subgroup G) ∧
      normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        L.map (MulAut.conj (g : G)).toMonoidHom ∧
      d.K ⊔ (U : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) ∧
      let W := D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom
      letI : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
      let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans a
      let E' := (automizerModuleEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans E
      (∀ b v, E' (automizerRepresentation W b v) = cocodeRepresentation (a' b) (E' v)) ∧
      ∃ e : (normalizer (W : Set G) ⧸ W.subgroupOf (normalizer (W : Set G))) ≃* M24,
        (∀ n : normalizer (W : Set G),
          e (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) n) =
            a' (W.normalizerMonoidHom.rangeRestrict n)) ∧
        ∃ P : Sylow 2 M24,
          ((U : Subgroup G).subgroupOf (normalizer (W : Set G))).map
            (e.toMonoidHom.comp (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))) =
              (P : Subgroup M24) := by
  obtain ⟨cubic,X,d,U,g,hU,hR,hZ,hT,hJ,he,hc,_,_,hN,_,hm⟩ :=
    sourceOrbit_m24_three_space_thompson D h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨hZJ,hJS,hK⟩ := sourceOrbit_m24_common_thompson_contains_space D h hmany hV hq hnon
    a E hE z hz hne hquot d U (g : G) (hU.trans inf_le_right) hZ hJ
  have hCJ : centralizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
      elementaryAbelianMaxJ (U : Subgroup G) := by
    rw [←hJ]
    exact sourceOrbit_m24_conjugate_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot g
  obtain ⟨q,hqmark⟩ := sourceOrbit_m24_conjugate_normalizer_quotient D h hmany hV hq hnon
    a E hE z hz hne hquot g
  let W := D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))
  have hf : Function.Surjective f := q.surjective.comp (QuotientGroup.mk'_surjective _)
  have hUN : (U : Subgroup G) ≤ normalizer (W : Set G) := by
    dsimp only [W]
    rw [hJ]
    exact (U : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  refine ⟨cubic,X,d,U,g,hU,hR,hT,hJ,hZJ,hJS,he,hc,hCJ,hN,
    sup_le hK ((U : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)),
    hm,q,hqmark,(U.subtype hUN).mapSurjective hf,?_⟩
  rw [Sylow.coe_mapSurjective,Sylow.coe_subtype]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
