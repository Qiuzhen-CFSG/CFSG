module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.FullLinearScalarSelection
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.EndpointReflectionCubicCross

/-!
# Original TypeAt scalar orbit with the same hexad lift

The physical scalar automorphism of the full original linear group changes
its generators while retaining the original first reflection and torus.
The TypeAt reflection geometry proves the cross-relation for the new exterior
cubic and the same chosen hexad lift. Both complete original radicals and
both endpoint carriers are preserved. This is an actual permitted generator
orbit, not a conclusion that its word-17 defect vanishes for every marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Subgroup.CosetWordCertificate
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
open Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
local notation "F" => Matrix.PSL3Four.F
local notation "PSL" => Matrix.PSL3Four.PSL
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Original TypeAt geometry permits every full-linear scalar choice with
the same literal reflection, cubic and hexad lift, preserving both full
radicals and all thirteen linear relations together with the cross-relation. -/
theorem TypeAt.exists_original_scalar_cubic_generators (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hB16 : Nat.card B = 16)
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hC : A ⊔ B ≤ centralizer (W : Set G))
    (hBA : B ≤ normalizer (A : Set G))
    (d : NaturalEndpointData A) (hBd : B ≤ d.carrier)
    (h64 : Nat.card (A ⊔ B : Subgroup G) = 64)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z)
    (hpointsB : ∀ b ∈ B, b ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 8)
    (u c t r : G) (huV : u ∈ V) (huW : u ∉ W)
    (hcP : c ∈ (normalizer (V : Set G)).pCoreIn 2)
    (hc2 : c ^ 2 = u) (hct : Commute c t)
    (hB : B = A.map (MulAut.conj c).toMonoidHom)
    (ht3 : orderOf t = 3)
    (ht : t ∈ d.carrier) (hr : r ∈ d.carrier)
    (hrJ : r ∉ (A ⊔ B) ⊔ zpowers t)
    (hr2 : orderOf r = 2) (hinv : r * t * r⁻¹ = t⁻¹)
    (Q L : Subgroup G) (hPL : d.carrier≤L) (hQL : Q≤L)
    (hcoreP : d.carrier.pCoreIn 2=A) (hcoreQ : Q.pCoreIn 2=B)
    (e : L≃*PSL)
    (hP : (d.carrier.subgroupOf L).map e.toMonoidHom=pointParabolic F)
    (hQ : (Q.subgroupOf L).map e.toMonoidHom=lineParabolic F)
    (her : e ⟨r,hPL hr⟩=reflection F false)
    (ell : G) (hell : ell∈L)
    (heell : e ⟨ell,hell⟩=Matrix.PSL3Four.MathieuAmalgamMarking.cycle)
    (htell : Commute t ell)
    (n : G) (hnt : Commute n t) (hn3 : n^3=1) (hrn : r*n*r⁻¹=n⁻¹)
    (k : Fˣ) :
    ∃ α : MulAut L,
      (∀ g, e (α g)=firstReflectionScalarActor F k (e g)) ∧
      α ⟨r,hPL hr⟩=⟨r,hPL hr⟩ ∧ α ⟨t,hPL ht⟩=⟨t,hPL ht⟩ ∧
      (d.carrier.subgroupOf L).map α.toMonoidHom=d.carrier.subgroupOf L ∧
      (Q.subgroupOf L).map α.toMonoidHom=Q.subgroupOf L ∧
      (A.subgroupOf L).map α.toMonoidHom=A.subgroupOf L ∧
      (B.subgroupOf L).map α.toMonoidHom=B.subgroupOf L ∧
      orderOf (α ⟨ell,hell⟩:G)=3 ∧ Commute t (α ⟨ell,hell⟩:G) ∧
      r*(α ⟨ell,hell⟩:G)*r⁻¹=(α ⟨ell,hell⟩:G)⁻¹ ∧
      ⁅(α ⟨ell,hell⟩:G),n⁆^2=1 ∧
      ∃ pair : Fin 2→G,
        closure (Set.range pair)=d.carrier ∧ (∀ i,pair i∈d.carrier) ∧
        (∀ i,pair i=(α (e.symm (Matrix.PSL3Four.MathieuAmalgamMarking.pair i)):G)) ∧
        eval pair Matrix.PSL3Four.MathieuAmalgamMarking.reflectionWord=r ∧
        zpowers (eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)=zpowers t ∧
        ∀ i : Fin 13, eval ![pair 0,pair 1,(α ⟨ell,hell⟩:G),n]
          (Theory.SpecificGroups.MathieuAmalgamCompletion.relator ⟨i.val,by omega⟩)=1 := by
  obtain ⟨α,_,hα,_,hαr,hαt,hαP,hαQ,hαA,hαB,_,_,hnew3,hnewt,hnewinv,
      pair,hgen,hmem,hpair,hwr,hwt,hrels⟩ :=
    exists_original_full_linear_scalar_generators d.carrier Q L hPL hQL e hP hQ
      r t ell (hPL hr) ht hell her heell ht3 htell k
  have hcross : ⁅(α ⟨ell,hell⟩:G),n⁆^2=1 :=
    h.endpoint_reflection_cubic_cross_relation W A B hWV hW4 hA16 hB16 hAP hBP
      hC hBA d hBd h64 hpureB hpointsB u c t r huV huW hcP hc2 hct hB ht3 ht hr
      hrJ hr2 hinv (α ⟨ell,hell⟩:G) n hnewt.symm hnt
      (by rw [←hnew3,pow_orderOf_eq_one]) hn3 hnewinv hrn
  refine ⟨α,hα,hαr,hαt,hαP,hαQ,?_,?_,hnew3,hnewt,hnewinv,hcross,
    pair,hgen,hmem,hpair,hwr,hwt,hrels n⟩
  · simpa only [hcoreP] using hαA
  · simpa only [hcoreQ] using hαB

end CFSG.Quasithin.HigmanSims
