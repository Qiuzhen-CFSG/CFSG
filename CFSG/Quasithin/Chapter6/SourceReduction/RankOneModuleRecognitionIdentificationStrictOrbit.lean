module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictNontransitivity
public import Theory.Representation.BinaryOffender.MarkedOrbitCore

/-!
# Orbit generation and the two-core of the strict dotted actor

The actual H-conjugates of the source line generate U/Z(U), because U
is the H-normal closure of Z_S. The unique nonzero vector of the binary
line therefore has spanning orbit. The exact plane-stabilizer lift fixes
this vector under the image of the original Sylow subgroup T.

Applying the Sylow-fixed orbit lemma to the faithful dotted action gives
O₂(H-dot)=1. Both the source vector quotient and the image Sylow subgroup
are retained literally; no order or recognition assertion about H is used.

Source: Aschbacher--Smith, 6.2.16(2), using B.2.13, printed pp.689 and 78.
These orbit inputs feed the remaining crossing and G.10/G.11 construction.
The LocalAnalysis premise is discharged by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

theorem strict_sourceLine_group_generates (T L R : Subgroup G) (z : G) :
    closure {w : StrictVectorQuotient T L R z | ∃ h : centralizer ({z} : Set G),
      ∃ s ∈ ((ZS T L R).subgroupOf (sourceClosure T L R z)).map
        (QuotientGroup.mk' (center (sourceClosure T L R z))),
          strictQuotientAction T L R z h s = w} = ⊤ := by
  let H := centralizer ({z} : Set G)
  let N := equalityClosure T L R z
  let U := sourceClosure T L R z
  let e : N ≃* U := N.equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.mk' (center U)
  let f := q.comp e.toMonoidHom
  let C := closure {w : StrictVectorQuotient T L R z | ∃ h : H,
    ∃ s ∈ ((ZS T L R).subgroupOf U).map q, strictQuotientAction T L R z h s = w}
  let D := (C.comap f).map N.subtype
  have hND : N ≤ D := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨s, hs, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨h, rfl⟩ := isConj_iff.mp hconj
    let sN : N := ⟨s, M22Recognition.CentralizerExtension.sourceEight_contains _ hs⟩
    let sU := e sN
    let uN : N := ⟨h * s * h⁻¹, (inferInstance : N.Normal).conj_mem s sN.property h⟩
    refine mem_map.mpr ⟨uN, ?_, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨h, q sU, mem_map_of_mem q hs, ?_⟩
    rw [strictQuotientAction_mk]
    change q (strictClosureAction T L R z h sU) = q (e uN)
    apply congrArg q
    apply Subtype.ext
    rfl
  apply top_unique
  intro w _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center U) w
  obtain ⟨n, rfl⟩ := e.surjective u
  obtain ⟨n', hn', he⟩ := hND n.property
  exact (Subtype.ext he : n' = n) ▸ hn'

section Linear
variable {T L R : Subgroup G} {z : G}
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]

theorem strictSourceLine_orbit_span :
    Submodule.span (ZMod 2) {w | ∃ a : StrictActor T L R z,
      ∃ s ∈ strictSourceLine T L R z, strictRepresentation T L R z a s = w} = ⊤ := by
  let P := Submodule.span (ZMod 2) {w | ∃ a : StrictActor T L R z,
    ∃ s ∈ strictSourceLine T L R z, strictRepresentation T L R z a s = w}
  let D : Subgroup (StrictVectorQuotient T L R z) := P.toAddSubgroup.toSubgroup'
  have hg : closure {w : StrictVectorQuotient T L R z | ∃ h : centralizer ({z} : Set G),
      ∃ s ∈ ((ZS T L R).subgroupOf (sourceClosure T L R z)).map
        (QuotientGroup.mk' (center (sourceClosure T L R z))),
          strictQuotientAction T L R z h s = w} ≤ D := by
    apply (closure_le _).mpr
    rintro _ ⟨h, s, hs, rfl⟩
    change Additive.ofMul (strictQuotientAction T L R z h s) ∈ P
    exact Submodule.subset_span ⟨QuotientGroup.mk' _ h, Additive.ofMul s, hs, rfl⟩
  rw [strict_sourceLine_group_generates] at hg
  apply top_unique
  intro w _
  exact hg (mem_top w.toMul)

end Linear

theorem LocalAnalysis.strictSourcePoint_orbit_span [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (hv : v ∈ strictSourceLine (T : Subgroup G) L R z) (hv0 : v ≠ 0) :
    Submodule.span (ZMod 2) {w | ∃ a : StrictActor (T : Subgroup G) L R z,
      strictRepresentation (T : Subgroup G) L R z a v = w} = ⊤ := by
  have hline : strictSourceLine (T : Subgroup G) L R z = Submodule.span (ZMod 2) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (A.strictSourceLine_finrank h611 hnatural hz horder hstrict) hv hv0
  apply top_unique
  rw [← strictSourceLine_orbit_span (T := (T : Subgroup G)) (L := L) (R := R) (z := z)]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, s, hs, rfl⟩
  rw [hline] at hs
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  rw [map_smul]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)

section Sylow
variable [Finite G] {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}
  [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]

theorem LocalAnalysis.strict_sourceLine_fixed_of_mem
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (h : centralizer ({z} : Set G)) (hm : (h : G) ∈ M)
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (hv : v ∈ strictSourceLine (T : Subgroup G) L R z) :
    strictRepresentation (T : Subgroup G) L R z
      (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker h) v = v := by
  let D := strictSourceLine (T : Subgroup G) L R z
  let ρ := strictRepresentation (T : Subgroup G) L R z
  let b := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker h
  have hD : Nat.card D = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      A.strictSourceLine_finrank h611 hnatural hz horder hstrict, pow_one]
  by_cases hv0 : v = 0
  · simp only [hv0, map_zero]
  have hb : ∀ x, x ∈ strictCentralPlane (T : Subgroup G) L R z ↔
      ρ b x ∈ strictCentralPlane (T : Subgroup G) L R z :=
    (A.strict_plane_stabilizer_iff_mem h611 hnatural hz horder hstrict h).mpr hm
  have hmem := A.strict_stabilizer_preserves_sourceLine h611 hnatural hz horder hstrict b hb v hv
  have hne : ρ b v ≠ 0 := by
    intro he
    have hh := congrArg (ρ b⁻¹) he
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hh
    exact hv0 hh
  have he : (⟨ρ b v, hmem⟩ : D) = ⟨v, hv⟩ :=
    ((Nat.card_eq_two_iff' (0 : D)).mp hD).unique
      (fun he => hne (congrArg Subtype.val he))
      (fun he => hv0 (congrArg Subtype.val he))
  exact congrArg Subtype.val he

theorem LocalAnalysis.strict_actor_twoCore_eq_bot
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    pCore 2 (StrictActor (T : Subgroup G) L R z) = ⊥ := by
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  apply Representation.BinaryOffender.twoCore_eq_bot_of_sylow_fixed_span
    (strictRepresentation (T : Subgroup G) L R z) (strictRepresentation_injective _ _ _ _)
    S (strictSourceLine (T : Subgroup G) L R z) ?_ strictSourceLine_orbit_span
  intro v hv a
  obtain ⟨h, hh, ha⟩ := a.property
  change strictRepresentation (T : Subgroup G) L R z (a : StrictActor (T : Subgroup G) L R z) v = v
  rw [← ha]
  exact A.strict_sourceLine_fixed_of_mem h611 hnatural hz horder hstrict h
    (h611.sylow_le hh) v hv

end Sylow

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
