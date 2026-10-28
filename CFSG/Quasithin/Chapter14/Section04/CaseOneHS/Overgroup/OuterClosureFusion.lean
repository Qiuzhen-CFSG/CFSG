module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterFusion
public import Theory.GroupTheory.CyclicFourCenterInvolutionFusion

/-!
# Fusion in the original closure and the transfer placement

The marked H-action is transitive on nonzero vectors of U/Z(U).
 Within one noncentral central coset, two involutions are conjugate by U:
 their difference and a nontrivial commutator are the same unique central
 involution. Thus every involution of U is ambient-conjugate into V.
 The previously constructed outer involution avoids V, so its actual
 transfer conjugate in PU lies outside U as well as outside P.

This discharges the source placement rᵍ∈PU−U. The comparison of the
 Sylow centralizers and the extremal-fusion contradiction remain open.
Source: Aschbacher--Smith, 14.3.32(2), 14.3.33(3), printed pp.1003--1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The actual H action is transitive on the nonzero hatted module. -/
theorem point_hat_transitive
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (u v : F.Uhat) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ k : F.H, F.uhatAction k u = v := by
  obtain ⟨e,b,he⟩ := s.natural
  have hu' : (b u).toAdd ≠ 0 := fun hh => hu (b.injective
    ((Multiplicative.toAdd.injective hh).trans b.map_one.symm))
  have hv' : (b v).toAdd ≠ 0 := fun hh => hv (b.injective
    ((Multiplicative.toAdd.injective hh).trans b.map_one.symm))
  obtain ⟨A,hA⟩ := Representation.SL2FourNatural.transitive_nonzero (b u).toAdd (b v).toAdd hu' hv'
  let a : Representation.SL2FourNatural.SemilinearNormalizer.specialField :=
    ⟨Representation.SL2FourNatural.action A, (show Representation.SL2FourNatural.action.range ≤
      Representation.SL2FourNatural.SemilinearNormalizer.specialField from le_sup_left) ⟨A,rfl⟩⟩
  obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 F.H))) a
  change e (QuotientGroup.mk' (pCore 2 F.H) k) = a at hk
  refine ⟨k,?_⟩
  apply b.injective
  apply Multiplicative.toAdd.injective
  rw [he,hk]
  exact hA

/-- Involutions in one noncentral coset of U/Z(U) are conjugate inside U. -/
theorem closure_involutions_same_hat_fused
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (u v : F.U) (hu : u ∉ center F.U) (hu2 : u^2=1) (hv2 : v^2=1)
    (huv : QuotientGroup.mk' (center F.U) u = QuotientGroup.mk' (center F.U) v) :
    IsConj u v := by
  obtain ⟨e⟩ := s.core_shape.center_model
  let := e.isCyclic.mpr inferInstance
  have hZ : Nat.card (center F.U) = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  have hd : _root_.commutator F.U ≤ centralSquares F.U := by
    let : Fact (IsPGroup 2 F.U) := ⟨IsPGroup.of_card (n:=6) s.core_shape.card⟩
    have he : frattini F.U = centralSquares F.U := by
      apply map_injective F.U.subtype_injective
      rw [closure_frattini h structural alternatives F hne,center_squares_eq_point h F s]
    rw [←he]
    exact commutator_le_frattini_of_isPGroup (p:=2)
  exact isConj_involutions_of_cyclic_four_center hZ hd u v hu hu2 hv2 huv

/-- All noncentral involutions of the actual U fuse under the actual H. -/
theorem closure_noncentral_involutions_fused
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (u v : F.U) (hu : u ∉ center F.U) (hv : v ∉ center F.U)
    (hu2 : u^2=1) (hv2 : v^2=1) : IsConj (u:G) (v:G) := by
  let q := QuotientGroup.mk' (center F.U)
  have huq : q u ≠ 1 := fun hh => hu ((QuotientGroup.eq_one_iff u).mp hh)
  have hvq : q v ≠ 1 := fun hh => hv ((QuotientGroup.eq_one_iff v).mp hh)
  obtain ⟨k,hk⟩ := point_hat_transitive F s (q u) (q v) huq hvq
  let u' : F.U := ⟨(k:G)*u*(k:G)⁻¹,(mem_normalizer_iff.mp
    (le_normalizer_conjugateSpanBy V F.H k.property) u).mp u.property⟩
  have huq' : q u' = q v := by
    rw [F.uhatAction_apply_mk] at hk
    exact hk
  have hu' : u' ∉ center F.U := fun hh => hvq (huq'.symm.trans ((QuotientGroup.eq_one_iff u').mpr hh))
  have hu2' : u'^2=1 := by
    apply Subtype.ext
    change ((k:G)*(u:G)*(k:G)⁻¹)^2=1
    rw [conj_pow,show (u:G)^2=1 from congrArg Subtype.val hu2,mul_one,mul_inv_cancel]
  have huv := closure_involutions_same_hat_fused h structural alternatives F s hne u' v hu' hu2' hv2 huq'
  obtain ⟨a,ha⟩ := isConj_iff.mp huv
  exact (isConj_iff.mpr ⟨(k:G),rfl⟩ : IsConj (u:G) (u':G)).trans
    (isConj_iff.mpr ⟨(a:G),congrArg Subtype.val ha⟩)

/-- Every involution in the original U is ambient-conjugate to an element
of the original seed V. The central and noncentral cases are both retained. -/
theorem closure_involution_fused_into_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (u : G) (hu : u ∈ F.U) (hu2 : orderOf u = 2) :
    ∃ v : G, v ∈ V ∧ IsConj u v := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let uU : F.U := ⟨u,hu⟩
  have huU2 : uU^2=1 := Subtype.ext (by
    change u^2=1
    simpa only [hu2] using pow_orderOf_eq_one u)
  by_cases huZ : uU ∈ center F.U
  · have hP : u ∈ L.pCoreIn 2 := ((le_conjugateSpanBy F.ZU L).trans
      (centerSpan_eq_core h structural alternatives F s hne).le) (mem_map_of_mem F.U.subtype huZ)
    refine ⟨u,?_,IsConj.refl u⟩
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 u
      ((centerSpan_eq_core h structural alternatives F s hne).symm ▸ hP) |>.mp
        (congrArg Subtype.val huU2)
  · have hn : ¬ V ≤ F.ZU := by
      intro hvZ
      have hh := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne
      rw [inf_eq_left.mpr hvZ] at hh
      have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
      rw [hh] at hc
      have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
      omega
    obtain ⟨v,hv,hvZ⟩ := SetLike.not_le_iff_exists.mp hn
    let vU : F.U := ⟨v,le_conjugateSpanBy V F.H hv⟩
    have hvU2 : vU^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv)
    exact ⟨v,hv,closure_noncentral_involutions_fused h structural alternatives F s hne uU vU huZ
      (fun hh => hvZ (mem_map_of_mem F.U.subtype hh)) huU2 hvU2⟩

/-- The outer involution cannot fuse into the original U. -/
theorem outer_involution_not_fused_into_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8)
    (r : G) (hr : r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hrL : r ∉ L)
    (hr2 : orderOf r = 2) (hdis : ∀ l ∈ L, ⁅r,l⁆ ∈ V)
    (u : G) (hu : u ∈ F.U) : ¬ IsConj r u := by
  intro hru
  have hu2 : orderOf u=2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hru
    exact (congrArg orderOf hg).symm.trans (((MulAut.conj g).orderOf_eq r).trans hr2)
  obtain ⟨v,hv,huv⟩ := closure_involution_fused_into_seed h structural alternatives F s hne u hu hu2
  exact outer_involution_not_fused_into_seed h structural alternatives F s hne x hx hx3 hcard
    r hr hrL hr2 hdis v hv (hru.trans huv)

/-- The source transfer produces the actual r and g with rᵍ∈PU−U.
The extremal-centralizer argument, not the transfer placement, is the
remaining order-eight obligation. -/
theorem exists_outer_involution_and_nonclosure_conjugate
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hcard : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    ∃ r g : G, r ∈ F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ∧ r ∉ L ∧
      orderOf r = 2 ∧ (∀ l ∈ L, ⁅r,l⁆ ∈ V) ∧
      (∀ p ∈ L.pCoreIn 2, r*p*r⁻¹ = p⁻¹) ∧
      g⁻¹*r*g ∈ L.pCoreIn 2 ⊔ F.U ∧ g⁻¹*r*g ∉ L.pCoreIn 2 ∧ g⁻¹*r*g ∉ F.U ∧
      (∀ u ∈ F.U, ¬ IsConj r u) := by
  obtain ⟨r,g,hr,hrL,hr2,hd,hi,hg,hgP,_⟩ :=
    exists_outer_involution_and_point_conjugate h structural alternatives F s hne x hx hx3 hcard
  have hno := outer_involution_not_fused_into_closure h structural alternatives F s hne x hx hx3 hcard
    r hr hrL hr2 hd
  have hconj : IsConj r (g⁻¹*r*g) := isConj_iff.mpr ⟨g⁻¹,by simp only [inv_inv]⟩
  exact ⟨r,g,hr,hrL,hr2,hd,hi,hg,hgP,fun hh => hno _ hh hconj,hno⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
