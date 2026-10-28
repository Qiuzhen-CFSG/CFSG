module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.MathieuObstruction
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Action
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Models
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# The original odd actor on the marked containing component

At the exterior marking's actual involution, restrict the full M₂₂ residual
to its containing normal C-component Q. The original odd actor acts on the
literal simple section (Q/O₂(Q))/Z(Q/O₂(Q)). If that action is trivial,
Q itself supplies the p.623 comparison subgroup, contradicting the marked
Mathieu obstruction. Otherwise an original actor induces an automorphism of
exact prime order p and fixes the residual image pointwise. The image has
unchanged M₂₂ radical quotient and the model sieve leaves only binary G₂,
triality, Ree F₄ and J₄.

OddNormalizer applies both conclusions to the literal Hall counterexample.
The surviving odd-local exclusions and final normalizer control remain open.
Source: Aschbacher--Smith 4.4.3, printed p.623. The completed p.612 pushing-up
branch is independent and is not used for a new fixed-component assertion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter12.Section02 Chapter4 Chapter4.Section04
open OddLocalMathieu Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The genuine odd-prime action at the marked involution. The seed is the
image of the full original residual, and its radical quotient is still M₂₂.
No claim about an ordinary component in a single-element fixed group is made. -/
@[expose] def ExteriorOddLocalActionData (s : SylowExteriorMarking D)
    (p : ℕ) (A : Subgroup G) (K : Subgroup (normalizer (A : Set G))) : Prop :=
  ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
    ∃ P : Subgroup (centralizer ({s.marking.z} : Set G) ⊓ centralizer (A : Set G) : Subgroup G),
      P.IsCComponent ∧ P.Normal ∧
      Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧
      P.map (centralizer ({s.marking.z} : Set G) ⊓ centralizer (A : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
      ∃ (Q : Subgroup (centralizer ({s.marking.z} : Set G))) (hn : Q.Normal),
        letI := hn
        Q.IsCComponent ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧
        ChapterA.Section02.IsTheoremCModel (SimpleSection Q) ∧
        (T : Subgroup G) ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) ∧
        ∃ hPQ : P.map (inclusion inf_le_left) ≤ Q,
          ∃ (x : A) (hx : (x : G) ∈ centralizer ({s.marking.z} : Set G)),
            let a := simpleAction Q (⟨x,hx⟩ : centralizer ({s.marking.z} : Set G))
            let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
            orderOf a = p ∧ f.range ≠ ⊥ ∧ Group.IsSolvable f.ker ∧
              Nonempty ((f.range ⧸ solvableRadical f.range) ≃* Sporadic.Mathieu.M22) ∧
              f.range ≤ a.fixedSubgroup

/-- An odd-normalizer counterexample has a faithful prime-order action on
the actual simple section of the containing component. A trivial action
already constructs the p.623 comparison group and contradicts its full seed. -/
theorem exterior_janko_odd_local_action (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G))) (r : ExteriorJankoResidualData s A K) :
    ExteriorOddLocalActionData s p A K := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  obtain ⟨aK,_,_,z,hzG,hz,_,_,P,hP,hPn,⟨eP⟩,hPm,Q,hQ,hPQ,hQn,hQq,_,hTQ,hAQ⟩ := r
  let := hQn
  let := hQq
  let := hP.perfect
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hP.ne_bot
  let C := centralizer ({s.marking.z} : Set G)
  let Qg := Q.map C.subtype
  have hAC : A ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hAV hx) _ s.marking.z_mem).symm
  have hRQ : ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
      ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ Qg := by
    rw [←hPm]
    have hh := map_mono (f := C.subtype) hPQ
    simpa only [map_map,subtype_comp_inclusion] using hh
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := hAe.isPGroup.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hnon : ∃ x : A, simpleAction Q (⟨x,hAC x.property⟩ : C) ≠ 1 := by
    by_contra! hh
    have hc : ⁅A.subgroupOf C,Q⁆ ≤ Q.pCoreIn 2 :=
      commutator_le_of_trivial_simpleAction Q (A.subgroupOf C)
        (fun x => hh ⟨x,x.property⟩)
    have hcG := map_mono (f := C.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hAC,
      ←AmalgamLocalCores.pCoreIn_map_of_injective 2 C.subtype C.subtype_injective] at hcG
    have hQI : A ≤ sectionCentralizer Qg :=
      (le_sectionCentralizer_iff _ _).mpr ⟨hAQ,hcG⟩
    have hQM : Qg ≤ s.marking.M := D.sourceOrbit_oddActor_comparison
      h.toHypothesis1221 A hne
      ((s.marking.centralizing_actor_section hAM hAV).trans inf_le_right) ho Qg hTQ hQI
    exact exterior_janko_involution_residual_not_le s h A K aK z hz (hRQ.trans hQM)
  obtain ⟨x,hx⟩ := hnon
  let a := simpleAction Q (⟨x,hAC x.property⟩ : C)
  have hap : a ^ p = 1 := by
    rw [←map_pow]
    have he : (⟨x,hAC x.property⟩ : C) ^ p = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
    rw [he,map_one]
  let j := seedInclusion inf_le_left hPQ
  let f := (projection Q).comp j
  obtain ⟨hfn,hfk,hfe⟩ := seed_image j (seedInclusion_injective inf_le_left hPQ) eP
  have hz1 : s.marking.z ≠ 1 := s.marking.z_ne_one
  have hzG2 : orderOf s.marking.z = 2 := by
    rw [←hzG,orderOf_coe,orderOf_coe]
    exact hz
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    exact ⟨zpowers s.marking.z,fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),
      IsPGroup.of_card (show Nat.card (zpowers s.marking.z) = 2 ^ 1 by
        rw [Nat.card_zpowers,hzG2]; rfl),
      (normalizer_zpowers_eq_centralizer_of_order_two _ hzG2).symm⟩
  refine ⟨z,hzG,hz,P,hP,hPn,⟨eP⟩,hPm,Q,hQn,hQ,hQq,
    simpleSection_model (hC.subgroup Q),hTQ,hPQ,x,hAC x.property,
    orderOf_eq_prime hap hx,hfn,hfk,hfe,?_⟩
  rintro _ ⟨y,rfl⟩
  rw [MulAut.mem_fixedSubgroup]
  change simpleAction Q (⟨x,hAC x.property⟩ : C) (projection Q (j y)) = projection Q (j y)
  rw [simpleAction_projection]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change (x : G) * ((y : (C ⊓ centralizer (A : Set G) : Subgroup G)) : G) * (x : G)⁻¹ = _
  have hc := (y.val.property.2 (x : G) x.property)
  rw [hc,mul_inv_cancel_right]
  rfl

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter12.Section02 Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Apply the actual fixed-section sieve to the same containing component of
the marked involution centralizer. No quasisimplicity of the seed is assumed. -/
theorem exterior_odd_local_remaining_models (s : SylowExteriorMarking D)
    {p : ℕ} (hprime : p.Prime) (hp : 3 < p) {A : Subgroup G}
    {K : Subgroup (normalizer (A : Set G))} (d : ExteriorOddLocalActionData s p A K) :
    ∃ Q : Subgroup (centralizer ({s.marking.z} : Set G)),
      Q.IsCComponent ∧ Q.Normal ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧
      (T : Subgroup G) ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) ∧
      ChapterA.Section02.IsTheoremCModel (SimpleSection Q) ∧
      HasMathieuFixedSection (SimpleSection Q) p ∧ RemainingOddLocalModel (SimpleSection Q) := by
  obtain ⟨z,hzG,hz,P,hP,hPn,heP,hPm,Q,hn,hQ,hQq,hm,hTQ,hPQ,x,hx,ha,hfn,hfk,⟨e⟩,hfix⟩ := d
  let := hn
  let a := simpleAction Q (⟨x,hx⟩ : centralizer ({s.marking.z} : Set G))
  let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
  let g : f.range →* Sporadic.Mathieu.M22 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : ChapterA.Section02.IsSectionOf Sporadic.Mathieu.M22 a.fixedSubgroup :=
    (ChapterA.Section02.IsSectionOf.of_surjective g hg).ambient_injective
      (inclusion hfix) (inclusion_injective hfix)
  have hfixed : HasMathieuFixedSection (SimpleSection Q) p := ⟨a,ha,hs⟩
  exact ⟨Q,hQ,hn,hQq,hTQ,hm,hfixed,hfixed.theoremC_rows hprime hp hm⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
