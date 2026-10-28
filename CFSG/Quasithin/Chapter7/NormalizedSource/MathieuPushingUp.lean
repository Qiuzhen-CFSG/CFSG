module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCentralizers
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute.Irreducibility

/-!
# Original Mathieu point cores and pushing-up residuals

A faithful cocode marking identifies the entire action image of a distinguished
vector centralizer. Its trivial two-core forces the local centralizer to retain
O₂(J). Taking the actual solvable residual gives a normal C-component with M22
as its intrinsic two-core quotient. For M24 the point image is the full Aut(M22);
only its solvable residual is replaced by its inner subgroup.

The original chosen-orbit applications are in NonFFSourceMathieuPushingUp.
The section centralizer centralizes the whole cocode: its native image
centralizes the point stabilizer residual and hence is trivial. These
construct C.2.8 in the companion application, not the C.4.8 exclusion
or the ambient containment.
Source: Aschbacher--Smith, 8.1.1 and H.15.1, printed pp.712 and398,
refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]

omit [Finite G] [Finite X] in
/-- The point centralizer in a normalizing group retains its original two-core. -/
private theorem pointCentralizer_core (W J : Subgroup G)
    (hJN : J ≤ normalizer (W : Set G))
    (hQ : J.pCoreIn 2 ≤ centralizer (W : Set G)) (x : W)
    (f : (J ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* X)
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (W : Set G)).subgroupOf
      (J ⊓ centralizer ({(x : G)} : Set G)))
    (hp : pCore 2 X = ⊥) :
    (J ⊓ centralizer ({(x : G)} : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  let K := J ⊓ centralizer ({(x : G)} : Set G)
  let C := J ⊓ centralizer (W : Set G)
  have hc : centralizer (W : Set G) ≤ centralizer ({(x : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr x.property)
  have hm : (pCore 2 K).map f ≤ pCore 2 X :=
    le_sSup ⟨(inferInstance : (pCore 2 K).Normal).map f hf,pCore_isPGroup.map f⟩
  have hk : K.pCoreIn 2 ≤ centralizer (W : Set G) := by
    rintro y ⟨k,hk,rfl⟩
    have he : f k ∈ (⊥ : Subgroup X) := hp ▸ hm (mem_map_of_mem f hk)
    have he' : k ∈ f.ker := he
    rw [hker] at he'
    exact he'
  have hCK : C ≤ K := inf_le_inf_left J hc
  have hJC : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer (hJN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hKC : K.pCoreIn 2 ≤ C := le_inf ((pCoreIn_le 2 K).trans inf_le_left) hk
  apply le_antisymm
  · exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hKC
      (hCK.trans (K.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K))))).trans
      (pCoreIn_mono_of_normalizes inf_le_left hJC)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
      (le_inf (pCoreIn_le 2 J) (hQ.trans hc))
      (inf_le_left.trans (J.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

/-- The same original quotient identifies the residual's intrinsic two-core quotient. -/
private def residualQuotientEquiv [Group.IsPerfect X]
    (K : Type*) [Group K] [Finite K]
    (e : (K ⧸ pCore 2 K) ≃* X) :
    (solvableResidual K ⧸ pCore 2 (solvableResidual K)) ≃* X := by
  let : Group.IsPerfect (K ⧸ pCore 2 K) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact (solvableResidualPCoreQuotientEquiv 2).trans e

omit [Finite X] in
/-- A simple perfect two-core quotient makes the actual residual a C-component. -/
private theorem residual_isCComponent [IsQuasisimple X]
    (K : Type*) [Group K] [Finite K]
    (e : (K ⧸ pCore 2 K) ≃* X) :
    (solvableResidual K).IsCComponent := by
  let : IsQuasisimple (solvableResidual K ⧸ pCore 2 (solvableResidual K)) :=
    IsQuasisimple.of_mulEquiv (residualQuotientEquiv K e).symm
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2)
    (inferInstance : (solvableResidual K).Normal).isSubnormal
    (by
      intro N hN hquot
      let := hN
      let : Group.IsNilpotent ((solvableResidual K) ⧸ N) := hquot.isNilpotent
      exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N))
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
open Sporadic.Mathieu MathieuCode ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem m22_core_eq_bot : pCore 2 M22 = ⊥ := by
  let := m22_isSimpleGroup
  let : IsQuasisimple M22 :=
    { toIsPerfect := pairResidual_m22_perfect
      simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  exact le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans_eq m22_center_eq_bot)

/-- The original point centralizer has the same core in the M23 cocode action. -/
theorem m23_pointCentralizer_core (W L J : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G)) (hLJ : L ≤ J)
    (hJN : J ≤ normalizer (W : Set G))
    (hQ : J.pCoreIn 2 ≤ centralizer (W : Set G))
    (a : Automizer W ≃* M23)
    (hq : Function.Surjective (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = m23CocodeRepresentation (a b) (E v))
    (x : W) (hx : E (Additive.ofMul x) ∈ m23WeightTwoOrbit) :
    (J ⊓ centralizer ({(x : G)} : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  let q : J →* M23 := a.toMonoidHom.comp
    (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hJN))
  have hqJ : Function.Surjective q := by
    intro b
    obtain ⟨l,hl⟩ := hq (a.symm b)
    refine ⟨⟨l,hLJ l.property⟩,?_⟩
    change a (W.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = b
    exact (congrArg a hl).trans (a.apply_symm_apply b)
  obtain ⟨f,hf,_,hk,_⟩ := pair_residual_lift W J hJN m23CocodeRepresentation q hqJ E
    (fun j v => hE (W.normalizerMonoidHom.rangeRestrict (inclusion hJN j)) v)
    m23Cocode_faithful x (ChapterH.Section13To16.CocodeLocal.m23_pair_residual_commutator hx)
  obtain ⟨b⟩ := ChapterH.Section13To16.CocodeLocal.m23_pair_stabilizer hx
  apply pointCentralizer_core W J hJN hQ x (b.toMonoidHom.comp f)
    (b.surjective.comp hf) _ m22_core_eq_bot
  rw [MonoidHom.ker_comp_of_injective _ _ b.injective,hk]

/-- The original residual is normal in the local intersection and is a C-component there. -/
theorem embedded_residual_component
    {C A : Subgroup G} (hCA : C ≤ A) (hn : A ≤ normalizer (C : Set G))
    (e : (C ⧸ pCore 2 C) ≃* M22) :
    let B := (solvableResidual C).map C.subtype
    (B.subgroupOf A).Normal ∧ (B.subgroupOf A).IsCComponent ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* M22) ∧ conjugateSpanBy B A = B := by
  let := m22_isSimpleGroup
  let : IsQuasisimple M22 :=
    { toIsPerfect := pairResidual_m22_perfect
      simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let B := (solvableResidual C).map C.subtype
  have hBA : B ≤ A := (map_subtype_le _).trans hCA
  have hNB : A ≤ normalizer (B : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
  have hnormal : (B.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hNB
  let eB : solvableResidual C ≃* B :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let eQ : (B ⧸ pCore 2 B) ≃* M22 :=
    (QuotientGroup.congr _ _ eB.symm (pCore_map_iso 2 eB.symm)).trans (residualQuotientEquiv C e)
  have hcomp : (B.subgroupOf A).IsCComponent := by
    let eCA := (subgroupOfEquivOfLe hCA).symm
    have hh := ((residual_isCComponent C e).map_equiv eCA).map_subtype
      (normal_subgroupOf_of_le_normalizer hn).isSubnormal
    have he : ((solvableResidual C).map eCA.toMonoidHom).map (C.subgroupOf A).subtype = B.subgroupOf A := by
      apply map_injective A.subtype_injective
      rw [map_subgroupOf_eq_of_le hBA,map_map,map_map]
      rfl
    exact he ▸ hh
  exact ⟨hnormal,hcomp,⟨eQ⟩,le_antisymm (conjugateSpanBy_le le_rfl hNB)
    (le_conjugateSpanBy B A)⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
open Sporadic.Mathieu MathieuCode ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem autM22_core_eq_bot : pCore 2 (MulAut M22) = ⊥ := by
  have hc := automorphism_core_eq_bot 2 (conj_injective_of_center_eq_bot m22_center_eq_bot)
    m22_core_eq_bot (⊤ : Subgroup (MulAut M22)) (fun _ => mem_top _)
  have he := pCore_map_iso 2 (topEquiv : (⊤ : Subgroup (MulAut M22)) ≃* MulAut M22)
  rw [hc,Subgroup.map_bot] at he
  exact he.symm

private theorem autM22_residual_eq : solvableResidual (MulAut M22) = MulAut.innerSubgroup M22 := by
  let := pairResidual_m22_perfect
  let : Group.IsPerfect (MulAut.innerSubgroup M22) := Group.IsPerfect.range MulAut.conj
  let : Group.IsNilpotent (MulAut.Outer M22) :=
    (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
      (by simpa only [pow_one] using
        M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

private def autM22ResidualEquiv : solvableResidual (MulAut M22) ≃* M22 :=
  (MulEquiv.subgroupCongr autM22_residual_eq).trans
    (MonoidHom.ofInjective (conj_injective_of_center_eq_bot m22_center_eq_bot)).symm

/-- The original full Aut(M22) point quotient gives an M22 residual quotient.
The outer involution remains in the point quotient before taking the residual. -/
theorem embedded_outer_residual_component
    {C A : Subgroup G} (hCA : C ≤ A) (hn : A ≤ normalizer (C : Set G))
    (e : (C ⧸ pCore 2 C) ≃* MulAut M22) :
    let B := (solvableResidual C).map C.subtype
    (B.subgroupOf A).Normal ∧ (B.subgroupOf A).IsCComponent ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* M22) ∧ conjugateSpanBy B A = B := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let eR := f.solvableResidualMap.pCoreQuotientEquiv
    (f.solvableResidualMap_surjective hf) (f.solvableResidualMap_ker_isPGroup hk)
  let eRC : (solvableResidual C ⧸ pCore 2 (solvableResidual C)) ≃* M22 :=
    eR.trans ((QuotientGroup.congr _ _ autM22ResidualEquiv
      (pCore_map_iso 2 autM22ResidualEquiv)).trans
        ((QuotientGroup.quotientMulEquivOfEq m22_core_eq_bot).trans QuotientGroup.quotientBot))
  let := m22_isSimpleGroup
  let : IsSimpleGroup (solvableResidual C ⧸ pCore 2 (solvableResidual C)) := eRC.isSimpleGroup
  let : IsQuasisimple M22 :=
    { toIsPerfect := pairResidual_m22_perfect
      simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (solvableResidual C ⧸ pCore 2 (solvableResidual C)) :=
    IsQuasisimple.of_mulEquiv eRC.symm
  have hres : (solvableResidual C).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2)
      (inferInstance : (solvableResidual C).Normal).isSubnormal (by
        intro N hN hquot
        let := hN
        let : Group.IsNilpotent (solvableResidual C ⧸ N) := hquot.isNilpotent
        exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N))
  let B := (solvableResidual C).map C.subtype
  have hBA : B ≤ A := (map_subtype_le _).trans hCA
  have hNB : A ≤ normalizer (B : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
  have hnormal : (B.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hNB
  let eB : solvableResidual C ≃* B :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let eQ : (B ⧸ pCore 2 B) ≃* M22 :=
    (QuotientGroup.congr _ _ eB.symm (pCore_map_iso 2 eB.symm)).trans eRC
  have hcomp : (B.subgroupOf A).IsCComponent := by
    let eCA := (subgroupOfEquivOfLe hCA).symm
    have hh := (hres.map_equiv eCA).map_subtype
      (normal_subgroupOf_of_le_normalizer hn).isSubnormal
    have he : ((solvableResidual C).map eCA.toMonoidHom).map (C.subgroupOf A).subtype = B.subgroupOf A := by
      apply map_injective A.subtype_injective
      rw [map_subgroupOf_eq_of_le hBA,map_map,map_map]
      rfl
    exact he ▸ hh
  exact ⟨hnormal,hcomp,⟨eQ⟩,le_antisymm (conjugateSpanBy_le le_rfl hNB)
    (le_conjugateSpanBy B A)⟩

/-- The M24 calculation retains the whole Aut(M22) point stabilizer. -/
theorem m24_pointCentralizer_core (W L J : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G)) (hLJ : L ≤ J)
    (hJN : J ≤ normalizer (W : Set G))
    (hQ : J.pCoreIn 2 ≤ centralizer (W : Set G))
    (a : Automizer W ≃* M24)
    (hq : Function.Surjective (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = cocodeRepresentation (a b) (E v))
    (x : W) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    (J ⊓ centralizer ({(x : G)} : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  let q : J →* M24 := a.toMonoidHom.comp
    (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hJN))
  have hqJ : Function.Surjective q := by
    intro b
    obtain ⟨l,hl⟩ := hq (a.symm b)
    refine ⟨⟨l,hLJ l.property⟩,?_⟩
    change a (W.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = b
    exact (congrArg a hl).trans (a.apply_symm_apply b)
  obtain ⟨f,hf,_,hk,_⟩ := pair_residual_lift W J hJN cocodeRepresentation q hqJ E
    (fun j v => hE (W.normalizerMonoidHom.rangeRestrict (inclusion hJN j)) v)
    cocode_faithful x (ChapterH.Section13To16.CocodeLocal.m24_pair_residual_commutator hx)
  obtain ⟨b⟩ := ChapterH.Section13To16.CocodeLocal.m24_pair_stabilizer hx
  apply pointCentralizer_core W J hJN hQ x (b.toMonoidHom.comp f)
    (b.surjective.comp hf) _ autM22_core_eq_bot
  rw [MonoidHom.ker_comp_of_injective _ _ b.injective,hk]
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
variable {G : Type*} [Group G]

/-- A normal subgroup joined with the ambient two-core has that same two-core. -/
theorem normal_core_join (B K : Subgroup G) (hBK : B ≤ K)
    (hn : K ≤ normalizer (B : Set G)) :
    (B ⊔ K.pCoreIn 2).pCoreIn 2 = K.pCoreIn 2 := by
  have hQK := pCoreIn_le 2 K
  have hKQ : K ≤ normalizer (K.pCoreIn 2 : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hJK : B ⊔ K.pCoreIn 2 ≤ K := sup_le hBK hQK
  exact le_antisymm
    (pCoreIn_mono_of_normalizes hJK
      ((le_inf hn hKQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)))
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) le_sup_right (hJK.trans hKQ))
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]

omit [Finite G] [Finite X] in
private theorem section_le_kernel {A B : Subgroup G}
    (hBA : B ≤ A) (hAB : A ≤ normalizer (B : Set G))
    (f : A →* X) (hf : Function.Surjective f) (hp : pCore 2 X = ⊥)
    (hc : centralizer ((B.subgroupOf A).map f : Set X) = ⊥) :
    ChapterA.Section04.twoSectionCentralizer B A ≤ f.ker.map A.subtype := by
  have hcore : B.pCoreIn 2 ≤ A.pCoreIn 2 := pCoreIn_mono_of_normalizes hBA hAB
  have hfcore : (pCore 2 A).map f ≤ pCore 2 X :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf,pCore_isPGroup.map f⟩
  intro g hg
  have hgA : g ∈ A := hg.1
  refine ⟨⟨g,hgA⟩,?_,rfl⟩
  change f ⟨g,hgA⟩ = 1
  apply mem_bot.mp
  rw [←hc]
  apply mem_centralizer_iff.mpr
  rintro y ⟨b,hb,rfl⟩
  have hm := hcore (hg.2.2 b hb)
  obtain ⟨c,hc',he⟩ := hm
  have hcc : f c = 1 := mem_bot.mp (hp ▸ hfcore (mem_map_of_mem f hc'))
  have hh : ⁅(⟨g,hgA⟩ : A),b⁆ = c := Subtype.ext he.symm
  have hh' := congrArg f hh
  rw [map_commutatorElement,hcc,commutatorElement_eq_one_iff_mul_comm] at hh'
  exact hh'.symm

omit [Finite X] in
private theorem residual_image {C A : Subgroup G} (hCA : C ≤ A)
    (f : A →* X) (hf : Function.Surjective (f.comp (inclusion hCA))) :
    (((solvableResidual C).map C.subtype).subgroupOf A).map f = solvableResidual X := by
  have hh := map_solvableResidual_eq (f.comp (inclusion hCA)) hf
  rw [←map_map] at hh
  rw [←hh]
  congr 1
  apply map_injective A.subtype_injective
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hCA),map_map]
  rfl

open Representation Representation.BinaryOffender MathieuCode

omit [Finite X] in
private theorem pair_section_le {Y : Type*} [Group Y] [Finite Y] (W L A : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G))
    (hAN : A ≤ normalizer (W : Set G))
    (σ : Representation (ZMod 2) X Cocode)
    (q : normalizer (W : Set G) →* X)
    (hq : Function.Surjective (q.comp (inclusion hLN)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (elementaryRepresentation (p := 2) W.normalizerMonoidHom n v) =
      σ (q n) (E v))
    (hσ : Function.Injective σ) (x : W)
    (hAH : A ≤ centralizer ({(x : G)} : Set G))
    (hCA : L ⊓ centralizer ({(x : G)} : Set G) ≤ A)
    (hAB : A ≤ normalizer (((solvableResidual
      (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
      (L ⊓ centralizer ({(x : G)} : Set G)).subtype) : Set G))
    (hm : subspaceCommutator σ ⊤
      ((solvableResidual (cocodeVectorStabilizer σ (E (Additive.ofMul x)))).map
        (cocodeVectorStabilizer σ (E (Additive.ofMul x))).subtype) = ⊤)
    (b : cocodeVectorStabilizer σ (E (Additive.ofMul x)) ≃* Y)
    (hp : pCore 2 Y = ⊥)
    (hc : centralizer (solvableResidual Y : Set Y) = ⊥) :
    ChapterA.Section04.twoSectionCentralizer
      ((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype) A ≤ centralizer (W : Set G) := by
  let N := normalizer (W : Set G)
  let H := centralizer ({(x : G)} : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  have hqN : Function.Surjective q := by
    intro y
    obtain ⟨l,hl⟩ := hq y
    exact ⟨inclusion hLN l,hl⟩
  obtain ⟨fN,hfN,hfNval,hfNker,_⟩ := pair_residual_lift W N le_rfl σ q hqN E
    (fun n v => hE n v) hσ x hm
  obtain ⟨fL,hfL,hfLval,_,_⟩ := pair_residual_lift W L hLN σ
    (q.comp (inclusion hLN)) hq E (fun l v => hE (inclusion hLN l) v) hσ x hm
  let f := b.toMonoidHom.comp (fN.comp (inclusion (le_inf hAN hAH)))
  have hcompat : f.comp (inclusion hCA) = b.toMonoidHom.comp fL := by
    ext c
    apply congrArg b
    apply Subtype.ext
    exact (hfNval _).trans (hfLval c).symm
  have hfC : Function.Surjective (f.comp (inclusion hCA)) :=
    hcompat.symm ▸ (b.surjective.comp hfL)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c,hc⟩ := hfC y
    exact ⟨inclusion hCA c,hc⟩
  have hBc : centralizer ((B.subgroupOf A).map f : Set Y) = ⊥ := by
    rw [residual_image hCA f hfC]
    exact hc
  have hs := section_le_kernel ((map_subtype_le _).trans hCA) hAB f hf hp hBc
  intro g hg
  obtain ⟨a,ha,rfl⟩ := hs hg
  have hk : inclusion (le_inf hAN hAH) a ∈ fN.ker :=
    b.injective (ha.trans (map_one b).symm)
  rw [hfNker] at hk
  exact hk

open Sporadic.Mathieu ChapterE

/-- The section centralizer of the M23 point residual centralizes the whole cocode. -/
theorem m23_pair_section_le (W L A : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G)) (hAN : A ≤ normalizer (W : Set G))
    (a : Automizer W ≃* M23)
    (hq : Function.Surjective (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = m23CocodeRepresentation (a b) (E v))
    (x : W) (hx : E (Additive.ofMul x) ∈ m23WeightTwoOrbit)
    (hAH : A ≤ centralizer ({(x : G)} : Set G))
    (hCA : L ⊓ centralizer ({(x : G)} : Set G) ≤ A)
    (hAB : A ≤ normalizer (((solvableResidual
      (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
      (L ⊓ centralizer ({(x : G)} : Set G)).subtype) : Set G)) :
    ChapterA.Section04.twoSectionCentralizer
      ((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype) A ≤ centralizer (W : Set G) := by
  obtain ⟨b⟩ := ChapterH.Section13To16.CocodeLocal.m23_pair_stabilizer hx
  apply pair_section_le W L A hLN hAN m23CocodeRepresentation
    (a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict) (a.surjective.comp hq) E
    (fun n v => hE (W.normalizerMonoidHom.rangeRestrict n) v) m23Cocode_faithful x hAH hCA hAB
    (ChapterH.Section13To16.CocodeLocal.m23_pair_residual_commutator hx) b m22_core_eq_bot
  let := pairResidual_m22_perfect
  rw [solvableResidual_eq_top,coe_top,centralizer_univ,m22_center_eq_bot]

/-- The M24 section uses the full Aut(M22) point image and its inner residual. -/
theorem m24_pair_section_le (W L A : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G)) (hAN : A ≤ normalizer (W : Set G))
    (a : Automizer W ≃* M24)
    (hq : Function.Surjective (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hLN)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = cocodeRepresentation (a b) (E v))
    (x : W) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit)
    (hAH : A ≤ centralizer ({(x : G)} : Set G))
    (hCA : L ⊓ centralizer ({(x : G)} : Set G) ≤ A)
    (hAB : A ≤ normalizer (((solvableResidual
      (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
      (L ⊓ centralizer ({(x : G)} : Set G)).subtype) : Set G)) :
    ChapterA.Section04.twoSectionCentralizer
      ((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype) A ≤ centralizer (W : Set G) := by
  obtain ⟨b⟩ := ChapterH.Section13To16.CocodeLocal.m24_pair_stabilizer hx
  apply pair_section_le W L A hLN hAN cocodeRepresentation
    (a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict) (a.surjective.comp hq) E
    (fun n v => hE (W.normalizerMonoidHom.rangeRestrict n) v) cocode_faithful x hAH hCA hAB
    (ChapterH.Section13To16.CocodeLocal.m24_pair_residual_commutator hx) b autM22_core_eq_bot
  rw [autM22_residual_eq]
  exact MulAut.centralizer_innerSubgroup_eq_bot m22_center_eq_bot

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
