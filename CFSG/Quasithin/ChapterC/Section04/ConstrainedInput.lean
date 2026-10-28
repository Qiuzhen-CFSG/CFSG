module
public import CFSG.Quasithin.ChapterC.Section04.NontrivialAction
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction

/-!
# The original C.4 input to the constrained-component analysis

C.2.8 supplies all radical, Sylow and characteristic-normalizer fields of
C.2.3. Once C.4.4 supplies normalization of the escaping component by R,
the same literal component, radical and local subgroup therefore give the
input to C.2.7. Its already proved kernel and offender conclusions apply
without an additional ambient-normality assumption.

The radical-normalization premise is the exact remaining C.4.4 obligation;
this module does not infer the later normalizer classification from it.
Source: Aschbacher--Smith, quasithin C.4.4--5, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions
open ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- C.2.8 supplies the literal C.2.3 setup used in C.4. -/
theorem constrained_pushingUpSetup {κ : GroupClass}
    (h : HypothesisC28 κ H M L R V) : PushingUpSetup κ H R M := by
  refine ⟨h.sqtk,h.radical_le.trans h.local_le,h.local_le,h.isRadical,
    h.characteristic_control,?_⟩
  obtain ⟨S,hS⟩ := h.sylow_in_normalClosure
  have hs : Chapter1.IsSylowIn 2
      ((S : Subgroup (normalClosure (R.subgroupOf M : Set M))).map
        (normalClosure (R.subgroupOf M : Set M)).subtype)
      (normalClosure (R.subgroupOf M : Set M)) := ⟨S,rfl⟩
  have hm := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hs
  rwa [hS] at hm

/-- The constrained escaping component supplies C.2.7 as soon as the
original radical-normalization conclusion C.4.4 has been proved. -/
theorem constrained_input_of_radical_normalizes {κ : GroupClass}
    (h : HypothesisC28 κ H M L R V) (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (hn : R ≤ normalizer (K.map H.subtype : Set G)) :
    Input κ H R M (K.map H.subtype) := by
  let B := K.map H.subtype
  let e : K ≃* B := K.equivMapOfInjective H.subtype H.subtype_injective
  have hb : B.subgroupOf H = K := by
    exact K.comap_map_eq_self_of_injective H.subtype_injective
  let := hq
  have hqB : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hfB : generalizedFitting B = pCore 2 B := by
    rw [← map_generalizedFitting_equiv e, hfK, pCore_map_iso]
  refine ⟨h.constrained_pushingUpSetup,⟨map_subtype_le _,hb.symm ▸ hK⟩,
    hqB,hfB,?_,hn⟩
  intro hBM
  exact hout (fun k hk => hBM (mem_map_of_mem H.subtype hk))

/-- The unchanged C.4 source obtains the proved C.2.7 kernel and offender
clauses; the sole added premise is precisely C.4.4. -/
theorem constrained_kernel_offender_of_radical_normalizes
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (hn : R ≤ normalizer (K.map H.subtype : Set G)) :
    KernelConclusion (K.map H.subtype) R ∧ OffenderConclusion (K.map H.subtype) R :=
  C27Source.kernel_offender_from_source
    (h.constrained_input_of_radical_normalizes K hK hq hout hfK hn)

end CFSG.Quasithin.ChapterC.HypothesisC28
