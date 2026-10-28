module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductResidualLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductQuadratic
public import Glauberman.BaumannQuadraticLayer

/-!
# The original Baumann-Sylow subgroup F₀

For the actual rank-one envelope I, keep its literal Baumann normal closure
N and D=[U-alpha,O²(N)]. Quadratic action of the full root-product Sylow
restricts to the constructed Sylow of N. Normal generation centralizes D
by O₂(N); opposite commutators span D inside the two Thompson central
omegas. Thus the same Sylow maps exactly to the original Baumann subgroup.
The normal closure is therefore the source F₀, with its original SL₂ field,
characteristic-two structure and unique maximal Sylow overgroup.

This discharges the Sylow clause of the Baumann construction in MS93 (5.1),
printed p.913. The argument replaces the numerical fixed-index criterion;
its bounds need not be additional premises. Selected-path generation,
absence of characteristic normal subgroups, arbitrary-degree Niles,
terminal exclusions and the distance-two witness remain separate steps.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same original Baumann closure has the required Sylow and centralizes
its nonzero residual layer by its whole two-core. -/
theorem Input.replacement_root_product_baumann_sylow
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
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ∧
      let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
      N ⊔ pCore 2 I = ⊤ ∧
      Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
      generalizedFitting N = pCore 2 N ∧
      (pResidual 2 N).map N.subtype = pResidual 2 I ∧
      ∃ P : Sylow 2 N,
        ((P : Subgroup N).map N.subtype).map I.subtype =
          Glauberman.baumannSubgroup (Q d.radical t) ∧
        Order.HasUniqueMaximalOver (P : Subgroup N) ⊤ ∧
        ((omegaCenterIn (thompsonSubgroup (P : Subgroup N))).map N.subtype).map I.subtype =
          omegaCenterIn (thompsonSubgroup (Q d.radical t)) ∧
        Glauberman.baumannSubgroup (P : Subgroup N) = (P : Subgroup N) ∧
      let D := ⁅((U d.radical a).subgroupOf I).subgroupOf N,pResidual 2 N⁆
      D ≠ ⊥ ∧ D ≤ centralizer (pCore 2 N : Set N) ∧
      pCore 2 N ≤ centralizer
        (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) : Set N) := by
  obtain ⟨E,hE,I,hI,S,hS,hgen,heN,hfit,hres,P,hBP,hOm,hBgen,hunique,
    hUn,hWn,hWe,hD,hDne,hDU,hDid,hDn,hDe,hZbound,hZe,hDQ,x,hx,hopp,hcriterion⟩ :=
    h.replacement_root_product_baumann_residual_layer d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let := finite_stabilizer d.radical a
  let : Finite I := Finite.of_injective (inclusion hI) (inclusion_injective hI)
  let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
  let U₀ := ((U d.radical a).subgroupOf I).subgroupOf N
  let D := ⁅U₀,pResidual 2 N⁆
  let : U₀.Normal := hUn
  let : IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) ⊔ D : Subgroup N) := hDe
  let : (omegaCenterIn (thompsonSubgroup (P : Subgroup N)) ⊔ D : Subgroup N).Normal := hDn
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le
    (show D ≤ omegaCenterIn (thompsonSubgroup (P : Subgroup N)) ⊔ D from le_sup_right)
  let eN := Classical.choice heN
  let q := eN.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
  have hq : Function.Surjective q := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 N := by
    change eN.toMonoidHom.ker.comap (QuotientGroup.mk' (pCore 2 N)) = _
    rw [eN.toMonoidHom.ker_eq_bot eN.injective,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have hsupp := (Glauberman.baumann_rank_one_opposites_of_generation P q hq hk hBgen).1
  let f := I.subtype.comp N.subtype
  have hf : Function.Injective f := I.subtype_injective.comp N.subtype_injective
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F ^ 2)
  obtain ⟨M,hM,hJM,hTh,hBa,_⟩ := h.replacement_root_product_baumann_control
    d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hBJ : Glauberman.baumannSubgroup (Q d.radical t) ≤ J := by
    change Glauberman.baumannSubgroup (Q d.radical t) ≤ Subgroup.SmallMover.join _ _ _ _
    rw [hJM]
    exact hBa
  have hcore : (pCore 2 N).map N.subtype ≤ pCore 2 I :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map N.subtype⟩
  have hPmap : (P : Subgroup N).map f ≤ J := by
    rw [←hsupp,Subgroup.map_sup]
    apply sup_le
    · rw [←Subgroup.map_map,hBP]
      exact hBJ
    · rw [←Subgroup.map_map]
      exact ((map_mono hcore).trans (map_mono (pCore_isPGroup.le_sylow_of_normal S))).trans_eq hS
  have hDmap : D.map f ≤ U d.radical a := by
    rintro _ ⟨u,hu,rfl⟩
    exact hDU hu
  have hquad : ⁅⁅D,(P : Subgroup N)⁆,(P : Subgroup N)⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ hf).mp
    rw [map_commutator,map_commutator]
    apply bot_unique
    exact (commutator_mono (commutator_mono hDmap hPmap) hPmap).trans_eq
      (h.replacement_root_product_quadratic d geometry hb ha hat
        E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod)
  obtain ⟨hDc,hZc,hBe⟩ := Glauberman.baumann_eq_sylow_of_quadratic_residual_layer
    P D hBgen hsupp hDid hquad x hopp
  refine ⟨E,hE,I,hI,S,hS,hgen,heN,hfit,hres,P,?_,hunique,hOm,hBe,hDne,hDc,hZc⟩
  rw [←hBe]
  exact hBP

/-- The source F₀ inside the original vertex stabilizer, with the original
Baumann subgroup as its actual Sylow, unchanged field and whole residual. -/
theorem Input.replacement_root_product_F0
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
    ∃ E : BinaryField, E.degree = n ∧
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ C : Subgroup (FreeAmalgam d.radical), C ≤ I ∧ (C.subgroupOf I).Normal ∧
        C ⊔ (pCore 2 I).map I.subtype = I ∧
        Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        generalizedFitting C = pCore 2 C ∧
        (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype ∧
        ∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Glauberman.baumannSubgroup (Q d.radical t) ∧
          Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ := by
  obtain ⟨E,hE,I,hI,S,hS,hgen,⟨eN⟩,hfit,hres,T,hT,hunique,_⟩ :=
    h.replacement_root_product_baumann_sylow d geometry hb ha hat
      E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let N := normalClosure (Glauberman.baumannSubgroup (S : Subgroup I) : Set I)
  let C := N.map I.subtype
  let e : N ≃* C := N.equivMapOfInjective I.subtype I.subtype_injective
  let := finite_stabilizer d.radical a
  let : Finite I := Finite.of_injective (inclusion hI) (inclusion_injective hI)
  let : Finite C := Finite.of_surjective e e.surjective
  have hNsub : C.subgroupOf I = N := comap_map_eq_self_of_injective I.subtype_injective N
  have hCn : (C.subgroupOf I).Normal := by rw [hNsub]; infer_instance
  have hgen' : C ⊔ (pCore 2 I).map I.subtype = I := by
    have hh := congrArg (Subgroup.map I.subtype) hgen
    rwa [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
  let eqQ := e.symm.toMonoidHom.pCoreQuotientEquiv e.symm.surjective
    (IsPGroup.ker_isPGroup_of_injective (p := 2) e.symm.injective)
  let P : Sylow 2 C := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfit' : generalizedFitting C = pCore 2 C := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hfit
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hu : Order.HasUniqueMaximalOver (P : Subgroup C) ⊤ := by
    have hh := hunique.map e.mapSubgroup
    rw [OrderIso.map_top] at hh
    exact hh
  have hres' : (pResidual 2 C).map C.subtype = (pResidual 2 I).map I.subtype := by
    rw [←map_embedded_pResidual 2 N I.subtype,hres]
  refine ⟨E,hE,I,hI,C,map_subtype_le _,hCn,hgen',⟨eqQ.trans eN⟩,hfit',hres',P,?_,hu⟩
  change ((T : Subgroup N).map e.toMonoidHom).map C.subtype = _
  rw [Subgroup.map_map]
  change (T : Subgroup N).map (I.subtype.comp N.subtype) = _
  rw [←Subgroup.map_map]
  exact hT

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
