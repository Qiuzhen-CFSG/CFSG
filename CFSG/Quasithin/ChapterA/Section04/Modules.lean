module

public import CFSG.Quasithin.ChapterA.Section04.Defs
-- Intentional internal proof split: unfold Basic's unexposed definition only
-- to prove the public equation below, without changing Basic or its API.
import all CFSG.Quasithin.ChapterA.Section04.Basic
public import Stellmacher.OmegaOneCenterMap
public import BenderSuzuki.External.Huppert.IV.ResidualCommutator
public import Theory.GroupAction.PPerfectFixedCentralizer

/-!
# Internal modules for two-perfect groups

The module V(X,R) lies in the actual omega-center of R and is equal to
[V(X,R),X]. Nested signalizers give the fixed-subgroup formulas of
Aschbacher–Smith A.4.8(3),(4); the Thompson A × B consequence detects
nontriviality in (5). Relative normalization and the commutator bound in
the embedded two-core are explicit inputs, supplied by A.4.2(3) in the
subnormal application. No generalized-Fitting hypothesis is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.6 and A.4.8(1),(3)–(5), printed pp.59–60.
-/

open Subgroup Stellmacher
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterA.Section04

variable {G : Type*} [Group G]

/-- The defining omega-center is the ambient omega-center used in the action API. -/
public theorem signalizerModule_eq_commutator_omegaCenter (X R : Subgroup G) :
    signalizerModule X R = ⁅X, omegaOneCenterAmbient R⁆ := by rfl

/-- The omega-center is preserved by every element normalizing its group. -/
public theorem normalizer_le_normalizer_omegaCenter (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (omegaOneCenterAmbient R : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change (omegaOneCenterAmbient R).map (MulAut.conj x).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective]
  exact congrArg omegaOneCenterAmbient hx

/-- A.4.6: the module lies in the actual omega-center, not just the signalizer. -/
public theorem signalizerModule_le_omegaCenter (X R : Subgroup G)
    (hXR : X ≤ normalizer (R : Set G)) :
    signalizerModule X R ≤ omegaOneCenterAmbient R := by
  exact le_normalizer_iff_commutator_le_right.mp
    (hXR.trans (normalizer_le_normalizer_omegaCenter R))

/-- A.4.6: every internal module is elementary abelian at two. -/
public theorem signalizerModule_elementaryAbelian (X R : Subgroup G)
    (hXR : X ≤ normalizer (R : Set G)) :
    IsElementaryAbelian 2 (signalizerModule X R) := by
  have hle := signalizerModule_le_omegaCenter X R hXR
  let W := omegaOneCenterAmbient R
  let _ : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian R
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply Subtype.ext
    exact congrArg (fun w : W => (w : G))
      (IsMulCommutative.is_comm.comm (⟨a, hle a.property⟩ : W) ⟨b, hle b.property⟩)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) (hle a.property)

/-- Normalizing both inputs preserves the internal module. -/
public theorem normalizes_signalizerModule (T X R : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G)) (hTR : T ≤ normalizer (R : Set G)) :
    T ≤ normalizer (signalizerModule X R : Set G) := by
  intro t ht
  have hx := mem_normalizer_iff_map_conj_eq.mp (hTX ht)
  have hr := mem_normalizer_iff_map_conj_eq.mp
    ((hTR.trans (normalizer_le_normalizer_omegaCenter R)) ht)
  rw [mem_normalizer_iff_map_conj_eq, signalizerModule_eq_commutator_omegaCenter,
    map_commutator, hx, hr]

/-- A.4.6(*): a two-perfect group acts idempotently on its internal module. -/
public theorem signalizerModule_commutator_self [Finite G] (X R : Subgroup G)
    (hX : IsPPerfect 2 X) (hXR : X ≤ normalizer (R : Set G)) :
    ⁅signalizerModule X R, X⁆ = signalizerModule X R := by
  have hres : BenderSuzuki.External.hktPResidual 2 X = ⊤ := by
    exact hX _ BenderSuzuki.External.hktPResidual_normal
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have hmap : (BenderSuzuki.External.hktPResidual 2 X).map X.subtype = X := by
    rw [hres]
    exact le_antisymm (map_subtype_le _) (fun x hx => ⟨⟨x, hx⟩, mem_top _, rfl⟩)
  let W := omegaOneCenterAmbient R
  let _ : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian R
  have h := BenderSuzuki.External.commutator_map_pResidual_idempotent_of_isPGroup
    2 W X (IsElementaryAbelian.isPGroup 2 W)
    (hXR.trans (normalizer_le_normalizer_omegaCenter R))
  dsimp only at h
  rw [hmap] at h
  rw [signalizerModule_eq_commutator_omegaCenter, commutator_comm X]
  exact h

/-- The intrinsic core is normalized by every normalizer of X. -/
public theorem normalizer_le_normalizer_intrinsicCore (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (((pCore 2 X).map X.subtype : Subgroup G) : Set G) :=
  BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic X (pCore 2 X)

/-- The intrinsic module is preserved by every element normalizing X. -/
public theorem normalizer_le_normalizer_intrinsicModule (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (intrinsicSignalizerModule X : Set G) :=
  normalizes_signalizerModule _ X _ le_rfl (normalizer_le_normalizer_intrinsicCore X)

/-- A.4.8(1): the intrinsic two-core centralizes V(X). -/
public theorem intrinsicCore_le_centralizer_intrinsicModule (X : Subgroup G) :
    (pCore 2 X).map X.subtype ≤ centralizer (intrinsicSignalizerModule X : Set G) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro v hv
  have hvW := signalizerModule_le_omegaCenter X _
    (X.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore X)) hv
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hvW).2.2 q hq |>.symm

/-- A commutator bound in the intrinsic core forces mutual normalization. -/
public theorem normalizes_left_of_commutator_le_intrinsicCore (X S : Subgroup G)
    (hXS : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    S ≤ normalizer (X : Set G) :=
  le_normalizer_iff_commutator_le_left.mpr (hXS.trans (map_subtype_le _))

/-- A.4.8(1), before passing to the faithful action: the commutator is in its kernel. -/
public theorem commutator_le_centralizer_intrinsicModule (X S : Subgroup G)
    (hXS : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    ⁅X, S⁆ ≤ centralizer (intrinsicSignalizerModule X : Set G) :=
  hXS.trans (intrinsicCore_le_centralizer_intrinsicModule X)

/-- Centralizing a larger subgroup makes a contained elementary subgroup
lie in its omega-center. -/
private theorem elementary_inf_centralizer_le_omegaCenter (V S : Subgroup G)
    [IsElementaryAbelian 2 V] (hVS : V ≤ S) :
    V ⊓ centralizer (S : Set G) ≤ omegaOneCenterAmbient S := by
  intro v hv
  exact (mem_omegaOneCenterAmbient_iff S v).mpr
    ⟨hVS hv.1, elemPow_eq_one_of_isElementaryAbelian v hv.1,
      mem_centralizer_iff.mp hv.2⟩

/-- A.4.8(3): comparison of modules for nested signalizers. -/
public theorem signalizerModule_eq_fixed_commutator [Finite G] (X R S : Subgroup G)
    (hX : IsPPerfect 2 X)
    (hXR : X ≤ normalizer (R : Set G)) (hXS : X ≤ normalizer (S : Set G))
    (hRS : R ≤ S) (hVR : signalizerModule X S ≤ R) :
    signalizerModule X S = ⁅signalizerModule X R ⊓ centralizer (S : Set G), X⁆ := by
  have hVS := signalizerModule_le_omegaCenter X S hXS
  have hle : signalizerModule X S ≤ omegaOneCenterAmbient R := by
    intro v hv
    obtain ⟨_, hp, hc⟩ := (mem_omegaOneCenterAmbient_iff S v).mp (hVS hv)
    exact (mem_omegaOneCenterAmbient_iff R v).mpr
      ⟨hVR hv, hp, fun r hr => hc r (hRS hr)⟩
  have hcomp : signalizerModule X S ≤ signalizerModule X R := by
    calc
      signalizerModule X S = ⁅signalizerModule X S, X⁆ :=
        (signalizerModule_commutator_self X S hX hXS).symm
      _ ≤ ⁅omegaOneCenterAmbient R, X⁆ := commutator_mono hle le_rfl
      _ = signalizerModule X R :=
        (commutator_comm _ _).trans (signalizerModule_eq_commutator_omegaCenter X R).symm
  have hcent : signalizerModule X S ≤ centralizer (S : Set G) := by
    intro v hv
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff S v).mp (hVS hv)).2.2
  apply le_antisymm
  · calc
      signalizerModule X S = ⁅signalizerModule X S, X⁆ :=
        (signalizerModule_commutator_self X S hX hXS).symm
      _ ≤ _ := commutator_mono (le_inf hcomp hcent) le_rfl
  · let _ := signalizerModule_elementaryAbelian X R hXR
    have hfixed := elementary_inf_centralizer_le_omegaCenter (signalizerModule X R) S
      ((signalizerModule_le_right X R hXR).trans hRS)
    calc
      ⁅signalizerModule X R ⊓ centralizer (S : Set G), X⁆ ≤
          ⁅omegaOneCenterAmbient S, X⁆ := commutator_mono hfixed le_rfl
      _ = signalizerModule X S :=
        (commutator_comm _ _).trans (signalizerModule_eq_commutator_omegaCenter X S).symm

/-- The action commutator bound also places V(X,S) in the embedded core. -/
public theorem signalizerModule_le_intrinsicCore (X S : Subgroup G)
    (hXS : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    signalizerModule X S ≤ (pCore 2 X).map X.subtype := by
  apply le_trans (commutator_mono le_rfl ?_) hXS
  intro v hv
  exact ((mem_omegaOneCenterAmbient_iff S v).mp hv).1

/-- A.4.8(4): fixed points in the intrinsic module compute V(X,S). -/
public theorem signalizerModule_eq_intrinsic_fixed_commutator [Finite G]
    (X S : Subgroup G) (hX : IsPPerfect 2 X)
    (hXS : X ≤ normalizer (S : Set G))
    (hQS : (pCore 2 X).map X.subtype ≤ S)
    (hcomm : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    signalizerModule X S = ⁅intrinsicSignalizerModule X ⊓ centralizer (S : Set G), X⁆ :=
  signalizerModule_eq_fixed_commutator X _ S hX
    (X.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore X)) hXS hQS
    (signalizerModule_le_intrinsicCore X S hcomm)

/-- The module of an overgroup of the core lies in the intrinsic module. -/
public theorem signalizerModule_le_intrinsicModule [Finite G]
    (X S : Subgroup G) (hX : IsPPerfect 2 X)
    (hXS : X ≤ normalizer (S : Set G))
    (hQS : (pCore 2 X).map X.subtype ≤ S)
    (hcomm : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    signalizerModule X S ≤ intrinsicSignalizerModule X := by
  rw [signalizerModule_eq_intrinsic_fixed_commutator X S hX hXS hQS hcomm]
  exact (commutator_mono inf_le_left le_rfl).trans
    (signalizerModule_commutator_self X _ hX
      (X.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore X))).le

/-- A.4.8(5): the larger signalizer detects exactly the nontrivial intrinsic module. -/
public theorem signalizerModule_ne_bot_iff_intrinsic [Finite G]
    (X S : Subgroup G) (hX : IsPPerfect 2 X) (hS : IsPGroup 2 S)
    (hXS : X ≤ normalizer (S : Set G))
    (hQS : (pCore 2 X).map X.subtype ≤ S)
    (hcomm : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    signalizerModule X S ≠ ⊥ ↔ intrinsicSignalizerModule X ≠ ⊥ := by
  have hXQ := X.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore X)
  have hXV := X.le_normalizer.trans (normalizer_le_normalizer_intrinsicModule X)
  have hSV := (normalizes_left_of_commutator_le_intrinsicCore X S hcomm).trans
    (normalizer_le_normalizer_intrinsicModule X)
  let _ : IsElementaryAbelian 2 (intrinsicSignalizerModule X) :=
    signalizerModule_elementaryAbelian X _ hXQ
  have hkernel : ⁅S, X⁆ ≤ centralizer (intrinsicSignalizerModule X : Set G) := by
    rw [commutator_comm]
    exact commutator_le_centralizer_intrinsicModule X S hcomm
  constructor
  · intro hne hzero
    apply hne
    exact le_bot_iff.mp ((signalizerModule_le_intrinsicModule X S hX hXS hQS hcomm).trans
      hzero.le)
  · intro hne hzero
    have hfix : ⁅intrinsicSignalizerModule X ⊓ centralizer (S : Set G), X⁆ = ⊥ := by
      rw [← signalizerModule_eq_intrinsic_fixed_commutator X S hX hXS hQS hcomm, hzero]
    have htriv := hX.centralizes_of_commuting_fixed X S (intrinsicSignalizerModule X)
      hS hXV hSV hkernel hfix
    exact hne ((signalizerModule_commutator_self X _ hX hXQ).symm.trans htriv)

/-- The full A.4.6 containment uses relative, rather than ambient, normality. -/
public theorem signalizerModule_le_inf_omegaCenter (X R : Subgroup G)
    (hXR : X ≤ normalizer (R : Set G)) (hRX : R ≤ normalizer (X : Set G)) :
    signalizerModule X R ≤ X ⊓ omegaOneCenterAmbient R :=
  le_inf (signalizerModule_le_left X R hRX) (signalizerModule_le_omegaCenter X R hXR)

/-- A.4.8(1) as an equality in the actual automorphism group of V(X).
This applies to R by restricting the bound on [X,S] along R ≤ S. -/
public theorem intrinsicModule_action_images_commute (X S : Subgroup G)
    (hcomm : ⁅X, S⁆ ≤ (pCore 2 X).map X.subtype) :
    let V := intrinsicSignalizerModule X
    let hXV := X.le_normalizer.trans (normalizer_le_normalizer_intrinsicModule X)
    let hSV := (normalizes_left_of_commutator_le_intrinsicCore X S hcomm).trans
      (normalizer_le_normalizer_intrinsicModule X)
    ⁅(V.normalizerMonoidHom.comp (inclusion hXV)).range,
      (V.normalizerMonoidHom.comp (inclusion hSV)).range⁆ = ⊥ := by
  dsimp only
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro a ⟨x, rfl⟩
  rw [mem_centralizer_iff]
  rintro b ⟨s, rfl⟩
  apply Eq.symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  let V := intrinsicSignalizerModule X
  let xN : normalizer (V : Set G) :=
    ⟨x, (X.le_normalizer.trans (normalizer_le_normalizer_intrinsicModule X)) x.property⟩
  let sN : normalizer (V : Set G) :=
    ⟨s, ((normalizes_left_of_commutator_le_intrinsicCore X S hcomm).trans
      (normalizer_le_normalizer_intrinsicModule X)) s.property⟩
  have hk : ⁅xN, sN⁆ ∈ V.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact commutator_le_centralizer_intrinsicModule X S hcomm
      (commutator_mem_commutator x.property s.property)
  change ⁅V.normalizerMonoidHom xN, V.normalizerMonoidHom sN⁆ = 1
  rw [← map_commutatorElement]
  exact hk

end CFSG.Quasithin.ChapterA.Section04
