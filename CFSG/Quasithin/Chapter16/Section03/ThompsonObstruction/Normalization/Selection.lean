module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Conjugation
public import Theory.GroupTheory.SaturatedCentralizer
/-!
# Choosing the local Sylow centralizer

Choose a conjugate of t inside C_G(z) whose centralizer in T is Sylow in
the simultaneous centralizer. Relative normality of L preserves the contrary
component assertion, and equivariance of the layer closure transports the
marked enlargement. The transported centralizer Sylow equation recovers
C_{T_C}(t) = ⟨z,t⟩, so the dihedral/semidihedral input survives the choice.
Finally extend C_T(t) to a Sylow subgroup P of C_G(t).

The remaining compatible marking and wreath-product identification are not
asserted here. They must be constructed to pass from `Selected` to `Prepared`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
after Lemma 16.3.11, printed p.1181 / PDF p.1198.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

private theorem exists_sylow_of_maximal {H U : Subgroup G} (hp : IsPGroup 2 U)
    (hUH : U ≤ H)
    (hmax : ∀ V : Subgroup G, IsPGroup 2 V → U ≤ V → V ≤ H → V = U) :
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = U := by
  obtain ⟨S, hS⟩ := (hp.comap_subtype (K := H)).exists_le_sylow
  refine ⟨S, hmax _ (S.isPGroup'.map _) ?_ (map_subtype_le _)⟩
  rw [← map_subgroupOf_eq_of_le hUH]
  exact map_mono hS

/-- Conjugation in C_G(z) preserves the contrary-component assertion, provided
the new involution has been placed in T. Relative normality is sufficient. -/
theorem counterexample_conjugate (h : TerminalCounterexample T z L t)
    (c : G) (hc : c ∈ involutionCentralizer z)
    (ht : (MulAut.conj c) t ∈ (T : Subgroup G)) :
    TerminalCounterexample T z L ((MulAut.conj c) t) := by
  let e : G ≃* G := MulAut.conj c
  have hN : involutionCentralizer z ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.localSetup.component.1).mp h.normal
  have hL : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hN hc)
  have hLback : L.map e.symm.toMonoidHom = L := by
    have hm := congrArg (fun A : Subgroup G => A.map e.symm.toMonoidHom) hL
    simpa [map_map] using hm.symm
  refine ⟨h.localSetup, h.normal, (e.orderOf_eq t).trans h.involution, ⟨ht, ?_⟩, ?_⟩
  · have hm := mem_map_of_mem e.toMonoidHom h.mem_commutingSylow.2
    rw [map_centralizer_equiv,
      show e '' (L : Set G) = (L : Set G) from
        congrArg (fun A : Subgroup G => (A : Set G)) hL] at hm
    exact hm
  · intro hcomp
    have hm := (show Theory.GroupTheory.IsComponentIn L
      (involutionCentralizer (e t)) from hcomp).map e.symm
    rw [hLback, involutionCentralizer, map_centralizer_equiv,
      Set.image_singleton, e.symm_apply_apply] at hm
    exact h.not_component hm

/-- Choose the permitted conjugate of t with C_T(t) Sylow in C_G(t,z).
The original component L and the central involution z are retained. -/
theorem exists_saturated_counterexample [Finite G] (h : TerminalCounterexample T z L t) :
    ∃ c : G, c ∈ involutionCentralizer z ∧
      TerminalCounterexample T z L ((MulAut.conj c) t) ∧
      ∃ S : Sylow 2 ↥(involutionCentralizer ((MulAut.conj c) t) ⊓ involutionCentralizer z),
        (S : Subgroup _).map
          (involutionCentralizer ((MulAut.conj c) t) ⊓ involutionCentralizer z).subtype =
            (T : Subgroup G) ⊓ involutionCentralizer ((MulAut.conj c) t) := by
  let N := involutionCentralizer z
  have hTN : (T : Subgroup G) ≤ N := h.localSetup.sylow_centralizes
  let R := T.subtype hTN
  let x : R := ⟨⟨t, hTN h.mem_commutingSylow.1⟩, h.mem_commutingSylow.1⟩
  obtain ⟨v, hxv, hmax⟩ := R.exists_conjugate_with_saturated_centralizer x
  obtain ⟨a, ha⟩ := isConj_iff.mp hxv
  let c : G := a
  let s : G := v
  have hs : (MulAut.conj c) t = s := congrArg Subtype.val ha
  have hsT : s ∈ (T : Subgroup G) := v.property
  have hh := counterexample_conjugate h c a.property (hs.symm ▸ hsT)
  refine ⟨c, a.property, hh, ?_⟩
  rw [hs]
  let U := (centralizer ({v} : Set R)).map (R : Subgroup N).subtype
  let E := (T : Subgroup G) ⊓ involutionCentralizer s
  have hUE : U.map N.subtype = E := by
    dsimp only [U]
    rw [map_subtype_centralizer_singleton]
    ext g
    constructor
    · rintro ⟨y, ⟨hyR, hyC⟩, rfl⟩
      exact ⟨hyR, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hyC))⟩
    · intro hg
      refine ⟨⟨g, hTN hg.1⟩, ⟨hg.1, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hg.2))
  apply exists_sylow_of_maximal (T.isPGroup'.of_injective
    (inclusion (inf_le_left : E ≤ (T : Subgroup G))) (inclusion_injective _))
  · exact le_inf inf_le_right (inf_le_left.trans hTN)
  · intro V hpV hEV hVH
    have hVN : V ≤ N := hVH.trans inf_le_right
    have hVU : V.subgroupOf N = U := hmax _ hpV.comap_subtype (by
      intro n hn
      have hnE : (n : G) ∈ E := by
        rw [← hUE]
        exact mem_map_of_mem N.subtype hn
      exact hEV hnE) (by
      intro n hn
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp (hVH hn).1)))
    have he := congrArg (fun A : Subgroup N => A.map N.subtype) hVU
    rwa [map_subgroupOf_eq_of_le hVN, hUE] at he

/-- The centralizer Sylow equation from 16.3.11 recovers the exact centralizer
in T_C whenever t has been placed in T. -/
theorem commutingSylow_centralizer_eq [Finite G]
    (h : TerminalCounterexample T z L t) (d : MarkedEnlargement z t L) :
    commutingSylow T L ⊓ involutionCentralizer t = zpowers z ⊔ zpowers t := by
  let H := involutionCentralizer t ⊓ centralizer (L : Set G)
  let U := commutingSylow T L ⊓ involutionCentralizer t
  have hUH : U ≤ H := fun _ hx => ⟨hx.2, hx.1.2⟩
  have hUT : U ≤ (T : Subgroup G) := fun _ hx => hx.1.1
  have hp : IsPGroup 2 U := T.isPGroup'.of_injective (inclusion hUT)
    (inclusion_injective _)
  have htU : t ∈ U := ⟨h.mem_commutingSylow, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzU : z ∈ U :=
    ⟨⟨h.localSetup.mem_sylow, h.localSetup.involution_mem_componentCentralizer⟩,
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp
          (h.localSetup.sylow_centralizes h.mem_commutingSylow.1)).symm⟩
  have hEU : zpowers t ⊔ zpowers z ≤ U :=
    sup_le (zpowers_le.mpr htU) (zpowers_le.mpr hzU)
  obtain ⟨S, hS⟩ := d.centralizer_component_sylow
  have he : U.subgroupOf H = (S : Subgroup H) := S.is_maximal' hp.comap_subtype (by
    intro x hx
    apply hEU
    rw [← hS]
    exact mem_map_of_mem H.subtype hx)
  have hm := congrArg (fun A : Subgroup H => A.map H.subtype) he
  rw [map_subgroupOf_eq_of_le hUH, hS] at hm
  exact hm.trans (sup_comm _ _)

/-- Extend the actual Sylow centralizer to a Sylow subgroup of C_G(t). -/
theorem exists_localSylow (T : Sylow 2 G) (t : G) :
    ∃ P : Sylow 2 (involutionCentralizer t),
      (T : Subgroup G) ⊓ involutionCentralizer t ≤ localSylow P := by
  have hp : IsPGroup 2 ((T : Subgroup G).subgroupOf (involutionCentralizer t)) :=
    T.isPGroup'.comap_subtype
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨P, ?_⟩
  rw [← subgroupOf_map_subtype (T : Subgroup G) (involutionCentralizer t)]
  exact map_mono hP

/-- The completed Sylow and conjugacy choice, before choosing the compatible
marking and computing the marked model of P. -/
structure Selected (T : Sylow 2 G) (z t : G) (L : Subgroup G) where
  counterexample : TerminalCounterexample T z L t
  shape : NonterminalCentralizerShape T z L t
  marked : MarkedEnlargement z t L
  centralizer_sylow :
    ∃ S : Sylow 2 ↥(involutionCentralizer t ⊓ involutionCentralizer z),
      (S : Subgroup _).map (involutionCentralizer t ⊓ involutionCentralizer z).subtype =
        (T : Subgroup G) ⊓ involutionCentralizer t
  P : Sylow 2 (involutionCentralizer t)
  centralizer_le : (T : Subgroup G) ⊓ involutionCentralizer t ≤ localSylow P

/-- The contrary involution lies in the chosen local Sylow. -/
theorem Selected.t_mem_localSylow (s : Selected T z t L) : t ∈ localSylow s.P :=
  s.centralizer_le ⟨s.counterexample.mem_commutingSylow.1,
    mem_centralizer_singleton_iff.mpr rfl⟩

/-- The original central involution lies in the same chosen local Sylow. -/
theorem Selected.z_mem_localSylow (s : Selected T z t L) : z ∈ localSylow s.P :=
  s.centralizer_le ⟨s.counterexample.localSetup.mem_sylow,
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (s.counterexample.localSetup.sylow_centralizes
        s.counterexample.mem_commutingSylow.1)).symm⟩

/-- The permitted conjugate has all the source inputs and both required Sylow
choices. Its enlargement remains the actual layer closure, via `enlargement_map`. -/
theorem exists_selected [Finite G] (h : TerminalCounterexample T z L t)
    (shape : NonterminalCentralizerShape T z L t) (d : MarkedEnlargement z t L) :
    ∃ c : G, c ∈ involutionCentralizer z ∧
      Nonempty (Selected T z ((MulAut.conj c) t) L) := by
  obtain ⟨c, hc, h', hS⟩ := exists_saturated_counterexample h
  let e : G ≃* G := MulAut.conj c
  have hz : e z = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)
  have hN : involutionCentralizer z ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.localSetup.component.1).mp h.normal
  have hL : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hN hc)
  let d' : MarkedEnlargement z (e t) L := d.transport e hz hL
  obtain ⟨P, hP⟩ := exists_localSylow T (e t)
  exact ⟨c, hc, ⟨{
    counterexample := h'
    shape := ⟨shape.model, commutingSylow_centralizer_eq h' d'⟩
    marked := d'
    centralizer_sylow := hS
    P := P
    centralizer_le := hP }⟩⟩

end CFSG.Quasithin.Chapter16.ThompsonObstruction
