module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawComponent
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# A cubic-centralizer obstruction on the actual quintic outside component

The original order-five marked quotient makes its embedded prime-to-three
residual centralize V. The same selected component is moved nontrivially by
W=[V,O²(C_M(Z₁))], and W lies in the original Sylow centralizer S. Thus the
literal cubic-centralizer identity of the constrained catalogue fails on
that same component. Whole-M generation is not assumed or encoded.

Source: Aschbacher--Smith 15.1.20--23, printed pp.1094--1100.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem quintic_quotient_cubic_residual
    {M V Z1 L : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hL : L ≤ centralizer (Z1 : Set G))
    (hc : letI := caseI_module_centralizer_normal (Z1 := Z1) hn
      Nat.card (pResidual 2 ((M ⊓ centralizer (Z1 : Set G) : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ centralizer (Z1 : Set G)))) = 5) :
    (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
      centralizer (V : Set G) := by
  let C := M ⊓ centralizer (Z1 : Set G)
  let K := (M ⊓ centralizer (V : Set G)).subgroupOf C
  let : K.Normal := caseI_module_centralizer_normal (Z1 := Z1) hn
  have hcop : Nat.Coprime 3 (Nat.card (C ⧸ K)) := by
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := C ⧸ K) 2).exists_card_eq
    rw [←(pResidual 2 (C ⧸ K)).card_mul_index,hc,index_eq_card,hn]
    exact (by decide : Nat.Coprime 3 5).mul_right ((by decide : Nat.Coprime 3 2).pow_right n)
  have hk : primeToResidual 3 C ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using primeToResidual_le_ker (QuotientGroup.mk' K) hcop
  have hr : (primeToResidual 3 C).map C.subtype ≤ centralizer (V : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    exact (hk hy).2
  exact (embedded_primeToResidual_mono 3 (inf_le_inf_left M hL)).trans hr

/-- One actual outside component in the full quintic order-four partner
branch violates the literal constrained cubic-centralizer identity. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_cubic_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let W := ⁅V,R⁆
      ∃ L : Subgroup G,
        L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ G1 ⊓ Mc ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
          centralizer (V : Set G) ∧
        S ⊓ centralizer (((primeToResidual 3 (M ⊓ L : Subgroup G)).map
          (M ⊓ L).subtype) : Set G) ≠ S ⊓ centralizer (L : Set G) ∧
        (IsComponent G1 (L.subgroupOf G1) ∨ generalizedFitting L = pCore 2 L) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
  let G1 := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ G1
  let C := M ⊓ G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  obtain ⟨L,hZ,_,hcard,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLc,hout,hqL,hloc,hSyl,houtM,hnL,hmove,hcases⟩ :=
    h.decomposable_five_partner_four_raw_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hres := quintic_quotient_cubic_residual h.normalized hLc.1 hcard
  refine ⟨L,hLc,hout,hqL,hloc,hSyl,houtM,hnL,hmove,hres,?_,hcases⟩
  intro he
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hWS : W ≤ S := hWV.trans (le_inf hVT
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left))))
  have hWC := hWV.trans (le_centralizer_iff.mp hres)
  have hWL : W ≤ centralizer (L : Set G) := ((le_inf hWS hWC).trans he.le).trans inf_le_right
  apply hmove
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hWL

end CFSG.Quasithin.Chapter15.Section01
