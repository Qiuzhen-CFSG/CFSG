module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.LocalStructure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.PPerfectHom


/-!
# The Frattini-small branch of MS93 (3.6)

A two-perfect group acting on a finite two-group cannot act nontrivially
through the kernel of the Frattini quotient action: that kernel is a
two-group by Burnside's basis theorem. Apply this to Q/X inside the actual
finite vertex stabilizer. Thus a core contained in Phi(Q)X lies in X.
Coprime commutator idempotence then identifies it with [X,Ltilde].

The final corollary retains [X,Ltilde] = U as an explicit input from the
binary (3.2) module calculation. This module does not assert that input or
the remaining branch of (3.6). In particular it assumes neither a natural
module nor abelianness of the core, and does not make the amalgam finite.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.6), first paragraph of the proof, printed p.870.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo

private theorem commutator_eq_bot_of_le_frattini
    {G : Type*} [Group G] (P A : Subgroup G) [Finite P]
    (hP : IsPGroup 2 P) (hA : IsPPerfect 2 A)
    (hn : A ≤ normalizer (P : Set G))
    (hc : ⁅P, A⁆ ≤ (frattini P).map P.subtype) : ⁅P, A⁆ = ⊥ := by
  let action : A →* MulAut P := P.normalizerMonoidHom.comp (inclusion hn)
  have hk (a : A) : action a ∈ (quotientAut (frattini P)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) x
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini P) (action a y) = QuotientGroup.mk' (frattini P) y
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh : ⁅(a : G), (y : G)⁆ ∈ (frattini P).map P.subtype := by
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator a.property y.property
    obtain ⟨z, hz, he⟩ := hh
    have he' : z = action a y / y := by
      apply Subtype.ext
      simpa [action, commutatorElement_def, div_eq_mul_inv] using he
    exact he' ▸ hz
  let action' : A →* (quotientAut (frattini P)).ker := action.codRestrict _ hk
  have htriv := hA.hom_eq_one_of_isPGroup (isPGroup_quotientAut_frattini_kernel hP) action'
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx a ha
  have he := congrArg (fun f : A →* (quotientAut (frattini P)).ker =>
    (((f ⟨a, ha⟩ : MulAut P) ⟨x, hx⟩) : G)) htriv
  change a * x * a⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem commutator_le_of_le_frattini_sup
    {G : Type*} [Group G] (P A X : Subgroup G) [Finite P]
    [P.Normal] [X.Normal]
    (hP : IsPGroup 2 P) (hA : IsPPerfect 2 A)
    (hc : ⁅P, A⁆ ≤ (frattini P).map P.subtype ⊔ X) : ⁅P, A⁆ ≤ X := by
  let q := QuotientGroup.mk' X
  let P' := P.map q
  let A' := A.map q
  have hP' : IsPGroup 2 P' := hP.map q
  have hA' : IsPPerfect 2 A' := hA.of_surjective (q.subgroupMap A)
    (q.subgroupMap_surjective A)
  let : Finite P' := Finite.of_surjective (q.subgroupMap P) (q.subgroupMap_surjective P)
  let : P'.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective X)
  have hphi : ((frattini P).map P.subtype).map q ≤ (frattini P').map P'.subtype := by
    have h := frattini_le_comap_frattini_of_surjective (q.subgroupMap_surjective P)
    have hh := map_mono (f := P'.subtype) (map_le_iff_le_comap.mpr h)
    have he : P'.subtype.comp (q.subgroupMap P) = q.comp P.subtype := by
      ext x
      rfl
    simpa only [map_map, he] using hh
  have hcomm : ⁅P', A'⁆ ≤ (frattini P').map P'.subtype := by
    have h := map_mono (f := q) hc
    rw [map_commutator, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h
    exact h.trans hphi
  have hzero := commutator_eq_bot_of_le_frattini P' A' hP' hA'
    le_normalizer_of_normal hcomm
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hzero
  exact hzero

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo

open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem distanceTwo_X_normal (a : Vertex R) :
    ((X R a).subgroupOf (stabilizer R a)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (omegaCenter (Q R a)).map (MulAut.conj g).toMonoidHom = _
  rw [← omegaCenter_map _ _ (MulAut.conj g).injective]
  have hQ := mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)
  change (Q R a).map (MulAut.conj g).toMonoidHom = Q R a at hQ
  rw [hQ]
  rfl

private theorem distanceTwo_frattini_map {G : Type*} [Group G]
    (P S : Subgroup G) (hPS : P ≤ S) :
    ((frattini (P.subgroupOf S)).map (P.subgroupOf S).subtype).map S.subtype =
      (frattini P).map P.subtype := by
  let e := subgroupOfEquivOfLe hPS
  calc
    _ = ((frattini (P.subgroupOf S)).map e.toMonoidHom).map P.subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [frattini_map_equiv]

/-- The local commutator core is generated by its commutators with the
local two-residual. This uses no module identification. -/
theorem LocalSource.core_full_commutation (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ⁅core R a, Ltilde R a⁆ = core R a := by
  let S := stabilizer R a
  let P := (Q R a).subgroupOf S
  let : Finite S := finite_stabilizer R a
  let : P.Normal := Q_normal R a
  have hp : IsPGroup 2 P := (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
  have h := commutator_isPPerfect_idempotent (pResidual 2 S) P
    (isPPerfect_pResidual 2) hp le_normalizer_of_normal
  have hm := congrArg (Subgroup.map S.subtype) h
  have hPm : P.map S.subtype = Q R a := map_subgroupOf_eq_of_le (fun _ hx => hx.1)
  simpa only [map_commutator, hPm, core, Ltilde, S] using hm

/-- Burnside's basis-kernel theorem removes the Frattini factor in the
first paragraph of MS93 (3.6). Relative subgroups lie in the actual finite
vertex stabilizer, while the displayed conclusion is in the free amalgam. -/
theorem LocalSource.core_le_X_of_le_frattini_sup (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false)
    (h : core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    core R a ≤ X R a := by
  let S := stabilizer R a
  let P := (Q R a).subgroupOf S
  let A := pResidual 2 S
  let Y := (X R a).subgroupOf S
  let : Finite S := finite_stabilizer R a
  let : P.Normal := Q_normal R a
  let : Y.Normal := distanceTwo_X_normal a
  have hQ : Q R a ≤ S := fun _ hx => hx.1
  have hX : X R a ≤ S := (omegaCenter_le (Q R a)).trans hQ
  have hPm : P.map S.subtype = Q R a := map_subgroupOf_eq_of_le hQ
  have hYm : Y.map S.subtype = X R a := map_subgroupOf_eq_of_le hX
  have hcm : (⁅P, A⁆ : Subgroup S).map S.subtype = core R a := by
    rw [map_commutator, hPm]
    rfl
  have hfm : ((frattini P).map P.subtype).map S.subtype =
      (frattini (Q R a)).map (Q R a).subtype := distanceTwo_frattini_map _ _ hQ
  have hc : ⁅P, A⁆ ≤ (frattini P).map P.subtype ⊔ Y := by
    intro x hx
    have hx' : (x : FreeAmalgam R) ∈
        ((frattini P).map P.subtype ⊔ Y).map S.subtype := by
      rw [Subgroup.map_sup, hfm, hYm]
      exact h (hcm ▸ mem_map_of_mem S.subtype hx)
    obtain ⟨z, hz, he⟩ := hx'
    exact (S.subtype_injective he) ▸ hz
  have hp : IsPGroup 2 P := (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
  have hsmall := DistanceTwo.commutator_le_of_le_frattini_sup P A Y hp
    (isPPerfect_pResidual 2) hc
  have hh := map_mono (f := S.subtype) hsmall
  rwa [hcm, hYm] at hh

/-- The Frattini-small branch identifies the core with the moving part of X.
Identifying that moving part with U is the separate binary module estimate. -/
theorem LocalSource.core_eq_X_commutator_of_le_frattini_sup (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false)
    (h : core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    core R a = ⁅X R a, Ltilde R a⁆ := by
  apply le_antisymm
  · rw [← source.core_full_commutation a ha]
    exact commutator_mono (source.core_le_X_of_le_frattini_sup a ha h) le_rfl
  · exact commutator_mono (omegaCenter_le (Q R a)) le_rfl

/-- Source (3.6)'s first reduction, with the still-needed (3.2) estimate
explicit. No natural-module or core-abelianness assumption is used. -/
theorem LocalSource.core_eq_U_of_le_frattini_sup (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false)
    (hX : ⁅X R a, Ltilde R a⁆ = U R a)
    (h : core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    core R a = U R a :=
  (source.core_eq_X_commutator_of_le_frattini_sup a ha h).trans hX

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
