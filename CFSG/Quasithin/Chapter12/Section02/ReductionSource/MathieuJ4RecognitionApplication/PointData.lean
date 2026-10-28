module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.ToddSplitting
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Hexad
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Intersection

/-!
# Constructing PointData in the original marked Mathieu branch

The original cocode image in the cubic design quotient is exactly the
hexad translation group. The invariant point-preimage construction is
therefore transverse to Q intersect E, removing the last extra premise
from ToddSplitting. The order-2160 actor and its elementary complement
split the actual overlap; Gaschütz then splits the whole cocode normalizer.

The constructed PointData retains the original cubic quotient, the actual
normalizer, both original Todd markings, and the equality of its elementary
subgroup with the original source orbit. No invariant-preimage, intersection,
splitting, or local-data hypothesis is added. The compatible line data and
full ambient recognition remain separate assembly obligations in this family.

Source: Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280; the original Aschbacher--Smith 8.2.12--14 application.
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

/-- Construct the original point subgroup with the literal Todd splitting,
retaining both the original cocode inclusion and its M24 quotient. -/
theorem sourceOrbit_m24_pointData :
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G))),
      ∃ data : Recognition.JankoFour.LocalGeometry.LocalSubgroups.PointData (z : G),
        data.cubic=cubic ∧ data.E=D.sourceOrbit ∧ ∃ hm : data.M=normalizer (D.sourceOrbit : Set G),
          (∀ x, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
            (MulEquiv.subgroupCongr hm (data.toddEquiv x)))=x.right) ∧
          (∀ w : D.sourceOrbit,
            (data.toddEquiv (SemidirectProduct.inl
              (Multiplicative.ofAdd (E (Additive.ofMul w))))).val=w.val) := by
  intro cubic
  obtain ⟨X⟩ := (inferInstance : Nonempty
    (Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)))
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨B,hB,hpre,A,v,t,hAc,_,_,him,_,_,_,htp,hvt,hv,hvo,hvA,hJc,_,_,hJN,hXJ,hJM⟩ :=
    D.sourceOrbit_m24_full_cubic_hexad_outer h hmany hV hq hnon a E hE z hz hne hquot cubic X
  let J := A.map (fullCubicCentralizer cubic X).subtype ⊔ zpowers v.val
  let C := centralizer ({(z : G)} : Set G)
  let W := D.sourceOrbit
  let W0 := W.subgroupOf C
  let N := W0 ⊔ Recognition.JankoFour.core (z : G)
  have hW0 : IsPGroup 2 W0 :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := W)).comap_subtype
  let := ht.extraspecial
  have hN : IsPGroup 2 N := hW0.to_sup_of_normal_right
    (IsExtraspecial.isPGroup 2 (Recognition.JankoFour.core (z : G)))
  have hJW : J ≤ normalizer (W0 : Set C) :=
    hJM.trans (Subgroup.le_normalizer_comap C.subtype)
  have hJnorm : J ≤ normalizer (N : Set C) :=
    (le_inf hJW le_normalizer_of_normal).trans
      (normalizer_inf_normalizer_le_normalizer_sup W0 (Recognition.JankoFour.core (z : G)))
  have hdis := fullCubic_hexad_disjoint_normal_two ht cubic X hB A hAc him v hv hvo hvA N hN hXJ hJnorm
  have hWC : W ≤ C := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr
      (((Commute.all (⟨w,hw⟩ : W) z).map W.subtype).eq)
  let ec := subgroupOfEquivOfLe hWC
  let : IsElementaryAbelian 2 W0 := IsElementaryAbelian.of_injective ec.toMonoidHom ec.injective
  have hWc : Nat.card W0=2048 := by
    rw [Nat.card_congr ec.toEquiv]
    change Nat.card (Additive W)=_
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hZU : center C ≤ W0 := by
    intro x hx
    have hh : x.val ∈ (center C).map C.subtype := mem_map_of_mem _ hx
    rw [←core_center_eq_centralizer_center ht,Recognition.JankoFour.LocalGeometry.core_center_image ht] at hh
    exact (zpowers_le.mpr z.property) hh
  let f := a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hc := sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hc]
  have hF : ∀ n w, E (Additive.ofMul (W.normalizerMonoidHom n w)) =
      cocodeRepresentation (f n) (E (Additive.ofMul w)) := by
    intro n w
    exact hE (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul w)
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  obtain ⟨hle,_,hkc,_⟩ := marked_cocode_core_image_and_lifts W f hf hk E hF z S hS ht cubic
  let q := f.comp (coreNormalizerInclusion W hle)
  have hker : q.ker=(W0 ⊓ Recognition.JankoFour.core (z : G)).subgroupOf
      (Recognition.JankoFour.core (z : G)) := by
    ext x
    change f (coreNormalizerInclusion W hle x)=1 ↔
      x.val ∈ W0 ⊓ Recognition.JankoFour.core (z : G)
    rw [←MonoidHom.mem_ker,hk]
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hIc : Nat.card (W0 ⊓ Recognition.JankoFour.core (z : G) : Subgroup C)=128 := by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at hkc
    exact hkc
  have hWim := InvariantPoint.cocode_design_image cubic W0
    ((normalizer (W : Set G)).subgroupOf C) hW0 hWc hIc
    (fun w hw => W.le_normalizer hw) (Subgroup.le_normalizer_comap C.subtype) hB hpre
  obtain ⟨P,hPQ,hP,hPc,_,hJP,hEP⟩ := InvariantPoint.exists_original_pointCore_transverse
    ht cubic X W0 J hZU hB hWim _
    (Classical.choose_spec (exists_m22Hexad_complementary_point hB))
    (InvariantPoint.hexad_actor_fixes_point ht cubic X hB A him v t htp hvt)
  let := hP
  obtain ⟨equiv,heq,hew⟩ := marked_cocode_todd_of_invariant_preimage W f hf hk E hF z S hS ht
    cubic X J P hJc hXJ hJN hJM hdis hPQ hPc hEP hJP
  let data : Recognition.JankoFour.LocalGeometry.LocalSubgroups.PointData (z : G) := {
    cubic := cubic
    M := normalizer (W : Set G)
    toddEquiv := equiv
    hexad := B
    hexad_mem := hB
    overlap := hpre }
  have hew' (w : W) : data.vectorEmbedding
      (Multiplicative.ofAdd (E (Additive.ofMul w)))=w.val := hew w
  have hEW : data.E=W := by
    apply le_antisymm
    · rintro x ⟨u,rfl⟩
      obtain ⟨w,hw⟩ := E.surjective u.toAdd
      have heu : Multiplicative.ofAdd (E w)=u := congrArg Multiplicative.ofAdd hw
      rw [←heu]
      have hew0 := hew' (Additive.toMul w)
      change data.vectorEmbedding (Multiplicative.ofAdd (E w))=(Additive.toMul w).val at hew0
      rw [hew0]
      exact (Additive.toMul w).property
    · intro w hw
      exact ⟨Multiplicative.ofAdd (E (Additive.ofMul (⟨w,hw⟩ : W))),hew' ⟨w,hw⟩⟩
  exact ⟨data,rfl,hEW,rfl,heq,hew⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
