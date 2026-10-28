module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosurePointComponent
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralPointRestriction
public import Theory.SpecificGroups.Alternating.EightComponent

/-!
# Excluding degree five in the original inner central-closure source

The actual point-centralizer A8 component is the prime-to-three residual
of N_G(V1), by its full cubic rank and two-group outer automorphisms.
The original scalar residual has an unchanged central-cubic image even
after taking its prime-to-three residual. That residual must centralize
V1, hence lies in O2(K) by the original scalar character. Its cubic image
would therefore be trivial, a contradiction.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The unchanged original W cannot have order 64, excluding the binary
five-dimensional quotient without a scalar or action-kernel premise. -/
theorem original_tripleSix_central_closure_not_card_sixtyFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≠ 64 := by
  intro h64
  let V1 := tripleSixPoint D a z
  let N := normalizer (V1:Set G)
  let X := tripleSixScalarResidual K
  obtain ⟨B,hBbound,hB,⟨eB⟩⟩ := original_tripleSix_central_closure_point_component
    h structural D a z hz hzT hnot hinner h64
  have hBC : B≤centralizer (V1:Set G) := hBbound.trans inf_le_right
  have hp := tripleSixPoint_properties D a z hz
  let : IsElementaryAbelian 2 V1 := hp.2.2.2.1
  have hVne : V1≠⊥ := by intro he; have hc:=hp.2.2.1; change Nat.card V1=4 at hc; rw [he,card_bot] at hc; omega
  have hN : IsSQTK KnownSimple.IsKnownSimple N := h.simpleQTKE.twoLocal_sqtk
    ⟨V1,hVne,IsElementaryAbelian.isPGroup 2 V1,rfl⟩
  have hrN : primeRank 3 N≤2 := hN.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hBN : B≤N := hBC.trans (Subgroup.centralizer_le_normalizer _)
  let L := B.subgroupOf N
  let e := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBN)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hBN))).trans eB
  let A := alternatingGroup (Fin 8)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple A := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv e.symm
  have hcenter : center (L ⧸ pCore 2 L)=⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x∈center A at he
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrL : 2≤primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : IsPGroup 2 (MulAut.Outer (L ⧸ pCore 2 L)) :=
    alternatingGroup.EightComponent.outer_two.of_equiv (MulAut.outerCongr e).symm
  have hLres : L=primeToResidual 3 N :=
    hB.eq_primeToResidual_three_of_rank_outer_two hcenter hrL hrN ho
  have hXN : X≤N := (tripleSixScalarResidual_point_transitive D a z).1
  have hXK : X≤K := map_subtype_le _
  let X0 := X.subgroupOf K
  let q := a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let ι : X0 →* N := {
    toFun := fun x => ⟨(x:K),hXN x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hresmem (x:X0) (hx:x∈primeToResidual 3 X0) : (x:K)∈pCore 2 K := by
    have hxN : ι x∈primeToResidual 3 N :=
      map_primeToResidual_le_of_hom 3 ι (mem_map_of_mem ι hx)
    have hxL : ι x∈L := hLres.symm ▸ hxN
    have hxB : ((x:K):G)∈B := hxL
    have hxC : ((x:K):G)∈centralizer ({(z:G)}:Set G) :=
      mem_centralizer_singleton_iff.mpr (hBC hxB z hp.1).symm
    have hk := tripleSixScalarResidual_point_centralizer_le_core D a z hz ⟨x.property,hxC⟩
    change (x:K)∈((pCore 2 K).map K.subtype).comap K.subtype at hk
    rwa [comap_map_eq_self_of_injective K.subtype_injective] at hk
  let Y := (primeToResidual 3 X0).map X0.subtype
  have hYzero : Y.map q=⊥ := by
    apply (Subgroup.map_eq_bot_iff Y).mpr
    rintro _ ⟨x,hx,rfl⟩
    change a.groupEquiv (QuotientGroup.mk' (pCore 2 K) (x:K))=1
    have hh : QuotientGroup.mk' (pCore 2 K) (x:K)=1 :=
      (QuotientGroup.eq_one_iff (x:K)).mpr (hresmem x hx)
    rw [hh,map_one]
  have hZres : primeToResidual 3 (center HexEvenAutomorphisms)=⊤ := by
    apply top_unique
    intro x _
    exact mem_primeToResidual_of_pow (n:=1) (by
      simpa only [pow_one,Hexacode.even_center_card] using pow_card_eq_one' (x:=x))
  have hYimage : Y.map q=center HexEvenAutomorphisms := by
    rw [show Y=(primeToResidual 3 X0).map X0.subtype from rfl,
      map_embedded_primeToResidual_of_hom,tripleSixScalarResidual_image D a,hZres,
      ←MonoidHom.range_eq_map,range_subtype]
  have hb : center HexEvenAutomorphisms=⊥ := hYimage.symm.trans hYzero
  have hc := Hexacode.even_center_card
  rw [hb,card_bot] at hc
  omega

end CFSG.Quasithin.Chapter12.Section07
