module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SourceAlternatives
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction
/-!
# The original strict cubic bound outside the two symplectic witness families

The source hypotheses themselves construct the actual dihedral, SL₂ or
Suzuki pair in every solvable, exchanged-component, normal Bender, odd
linear/unitary, and binary PSL₃ case. The strict Bender actor theorem then
proves the original bound in any normalizing overgroup of T. No model or
witness premise remains for these cases. The two unresolved original normal
symplectic families are returned with the same component and quotient map.
Source: Aschbacher–Smith E.2.7–9 and E.2.15, pp.218–222,228.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_cubicRatio_lt_two_or_symplectic
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀g∈ChapterB.minimalParabolicMax T hP,
      V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨ V.map (MulAut.conj g).toMonoidHom=V)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 ∨
    ∃K:Subgroup H,K.IsCComponent ∧ K.Normal ∧ K⊔(T:Subgroup H)=⊤ ∧
      ((∃f:ℕ,2≤f ∧ ClassicalGroup.IsPSp
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) ∨
        Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
          commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  rcases source_original_witness_or_symplectic hH T hP V hVT hvn hVM hout hTI with hw|hs
  · obtain ⟨n,⟨w⟩⟩ := hw
    exact Or.inl (BenderPlacement.original_witness_cubicRatio_lt_two
      hP hVT hvn hVM hout hfit hTI w hTU hU)
  · exact Or.inr hs
end CFSG.Quasithin.ChapterE.Witnesses

namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
  {H U V : Subgroup G} [IsElementaryAbelian 2 V]
  {S : Sylow 2 H} {M : Subgroup H} {n : ℕ}
/-- The actual outside-core source acts on V in a possibly different
normalizing overgroup U. The pair group need not be contained in U. -/
theorem OriginalWitness.ambient_cubicRatio_lt_two
    (w : OriginalWitness S M (V.subgroupOf H) n) (hVH : V ≤ H)
    (hVS : V.subgroupOf H ≤ (S : Subgroup H))
    (hSV : (S : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H))
    (hcore : V.subgroupOf H ≤ M.pCoreIn 2)
    (hn : normalizer (V.subgroupOf H : Set H) ≤ M)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ M, (V.subgroupOf H) ⊓
      (V.subgroupOf H).map (MulAut.conj x).toMonoidHom = ⊥ ∨
      (V.subgroupOf H).map (MulAut.conj x).toMonoidHom = V.subgroupOf H)
    (hSU : (S : Subgroup H).map H.subtype ≤ U) (hU : U ≤ normalizer (V : Set G))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U) :
    cubicRatio (DihedralCubic.representation U V hU q hq hk) < 2 := by
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
  have hh := w.model.actor_strict h (w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one)
    (w.pair.fitting hSV hfit) (restrict_TI w.pair.le hTI) e ρ (DihedralCubic.representation_injective U V hU q hq hk) f
  apply (hh ?_).2.2.2.2.2
  intro a v
  apply Subtype.ext
  apply Subtype.ext
  change ((ρ (q (aMap a)) (Additive.ofMul (e v))).toMul : G) = _
  rw [DihedralCubic.representation_apply]
  rfl
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
