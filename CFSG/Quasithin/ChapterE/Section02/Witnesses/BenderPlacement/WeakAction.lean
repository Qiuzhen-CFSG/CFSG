module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction.Geometry
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Original
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearCubic
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ClassicalCubic
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.StrictAction

/-!
# Weak cubic bounds without a TI hypothesis

Every original dihedral, binary linear or Suzuki pair gives a nonzero cubic
actor on the same faithful quotient representation. The linear source
estimate is non-strict and requires no trivial-intersection property.
The actual Sylow inclusion transports the actor into each overgroup of the
original Sylow that normalizes V. This is the bound needed by 3.1.8.
Source: Aschbacher–Smith E.2.13 and 3.1.8, pp.224–225,576.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {I D Q : Type*} [Group I] [Finite I] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
  {T : Sylow 2 I} {V M : Subgroup I} {g : I}

theorem QuotientModel.actor_le_two {d : ℕ} (model : QuotientModel M d)
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting I = pCore 2 I)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : I) =
        (a : I) * v * (a : I)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  cases model with
  | dihedral hd p a hp hp2 ha' ξ =>
    exact h.dihedral_cubic_actor hproper hfit
      (dihedral_star_card h hproper hp hp2 ξ) e ρ hρ f ha
  | linear hd ξ hb =>
    exact h.linear_two_cubic_actor hproper hfit d (by omega)
      (GaloisField.card 2 d (by omega)) ξ e ρ hρ f ha
  | suzuki m hm hd ξ hb =>
    have hr := h.suzuki_cubic_actor_strict hproper hfit m (by omega) ξ e ρ hρ f ha
    exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1.le,hr.2.2.2.2.2.le⟩

variable {H : Type*} [Group H] [Finite H]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W]
  {n : ℕ}

theorem OriginalWitness.actor_le_two (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U) :
    let h := w.pair.hypotheses hWS hSW hcore hn
    let ρ := DihedralCubic.representation U W hU q hq hk
    let f := DihedralCubic.actorMap h (w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)) q
    f.ker = (Z (W.subgroupOf w.pair.subgroup) w.pair.conjugator).subgroupOf
        (A (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup) w.pair.conjugator) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  let h := w.pair.hypotheses hWS hSW hcore hn
  let hSU' := w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)
  let e := subgroupOfEquivOfLe w.pair.le
  let ρ := DihedralCubic.representation U W hU q hq hk
  let f := DihedralCubic.actorMap h hSU' q
  apply w.model.actor_le_two h (w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one)
    (w.pair.fitting hSW hfit) e ρ
    (DihedralCubic.representation_injective U W hU q hq hk) f
  intro a v
  apply Subtype.ext
  change ((ρ (q (DihedralCubic.actorIn h hSU' a)) (Additive.ofMul (e v))).toMul : H) =
    ((a : w.pair.subgroup) : H) * ((v : w.pair.subgroup) : H) *
      ((a : w.pair.subgroup) : H)⁻¹
  rw [DihedralCubic.representation_apply]
  rfl

theorem OriginalWitness.cubicRatio_le_two (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U W hU) ≤ 2 := by
  let := DihedralCubic.centralizer_normal U W hU
  exact (w.actor_le_two hWS hSW hcore hn hfit hSU hU
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).2.2.2.2
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement

namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
  {T : Sylow 2 H} {V U : Subgroup H} [IsElementaryAbelian 2 V]

theorem original_witness_cubicRatio_le_two
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    {n : ℕ} (w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 := by
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hn := minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  exact w.cubicRatio_le_two hVT hTV hVM hn hfit hTU hU

theorem linear_three_cubicRatio_le_two
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 0<n)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2^n))
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 := by
  obtain ⟨w⟩ := LinearThree.source_original T hP hs K hK hgen hn hm V hVT hvn hVM hout
  exact original_witness_cubicRatio_le_two hP hVT hvn hVM hout hfit w hTU hU
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement


namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
  {H U V : Subgroup G} [IsElementaryAbelian 2 V]
  {S : Sylow 2 H} {M : Subgroup H} {n : ℕ}
/-- The actual outside-core source acts on V in a possibly different
normalizing overgroup U. The pair group need not be contained in U. -/
theorem OriginalWitness.ambient_cubicRatio_le_two
    (w : OriginalWitness S M (V.subgroupOf H) n) (hVH : V ≤ H)
    (hVS : V.subgroupOf H ≤ (S : Subgroup H))
    (hSV : (S : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H))
    (hcore : V.subgroupOf H ≤ M.pCoreIn 2)
    (hn : normalizer (V.subgroupOf H : Set H) ≤ M)
    (hfit : generalizedFitting H = pCore 2 H)
    (hSU : (S : Subgroup H).map H.subtype ≤ U) (hU : U ≤ normalizer (V : Set G))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U) :
    cubicRatio (DihedralCubic.representation U V hU q hq hk) ≤ 2 := by
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  let h := w.pair.hypotheses hVS hSV hcore hn
  let e := (subgroupOfEquivOfLe w.pair.le).trans (subgroupOfEquivOfLe hVH)
  let aMap : A ((V.subgroupOf H).subgroupOf w.pair.subgroup)
      (M.subgroupOf w.pair.subgroup) w.pair.conjugator →* U :=
    (H.subtype.comp (w.pair.subgroup.subtype.comp (A _ _ _).subtype)).codRestrict U (by
      intro a
      apply hSU
      refine ⟨(a : w.pair.subgroup),?_,rfl⟩
      have ha := DihedralCubic.A_le_sylow h a.property
      have hs : (a : w.pair.subgroup) ∈ (S : Subgroup H).subgroupOf w.pair.subgroup :=
        (w.pair.sylow_eq.le ⟨a,ha,rfl⟩).1
      exact hs)
  let f := q.comp aMap
  let ρ := DihedralCubic.representation U V hU q hq hk
  have hh := w.model.actor_le_two h (w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one)
    (w.pair.fitting hSV hfit) e ρ (DihedralCubic.representation_injective U V hU q hq hk) f
  apply (hh ?_).2.2.2.2
  intro a v
  apply Subtype.ext
  apply Subtype.ext
  change ((ρ (q (aMap a)) (Additive.ofMul (e v))).toMul : G) = _
  rw [DihedralCubic.representation_apply]
  rfl
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
