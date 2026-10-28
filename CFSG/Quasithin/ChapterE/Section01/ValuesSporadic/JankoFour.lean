module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoFour.Ambient
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoFour.LocalBounds
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoFour.MathieuBounds
public import CFSG.Quasithin.Defs

/-!
# Janko-four E-generation: the actual Sylow-containing generating pair

The max1 subgroup M and the full marked involution centralizer C generate
the concrete Janko model. Their intersection has odd index: its index in M
is 1771 and M has odd ambient index. Thus they contain a common ambient
Sylow two-subgroup. Sylow conjugacy transports this pair to any prescribed
Sylow subgroup, retaining the actual subgroup isomorphisms and generation.

Ambient proves that a simple generalized Fitting subgroup isomorphic to J4
is all of G, accounting for all source-allowed extensions. LocalBounds
reduces the intrinsic bounds for M and C to rank-one generation for M24
and rank-two generation for Aut(M22), including the genuine covering kernel
in C/O2(C). MathieuBounds discharges both bounds. E.1.12 then proves
rank-two E-generation for the model, and the ambient equivalence transfers
it to every source-allowed group. The final exports give both E-generation
and n(G) ≤ 2 under the full source hypotheses, without additional premises.

All E-generation predicates use the corrected local-tau and
intrinsic-quotient definitions in ChapterE.Defs.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
E.1.12 and E.1.14(5), printed p.214, citing Aschbacher,
GF(2)-representations of finite groups (1982), Lemma 4.9.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.JankoFour
variable {G : Type*} [Group G] [Finite G]

open Janko4 Janko4.Max1AmalgamRigidity

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
  Janko4.Cardinality.localX Janko4.Cardinality.localY Janko4.Cardinality.localKernelSeed

private theorem overlap_index_odd : ¬ 2 ∣ H.index := by
  rw [index_map_subtype, Janko4.Max1RelativeRigidity.pair_centralizer_index]
  exact Nat.prime_two.not_dvd_mul (by norm_num)
    Janko4.OuterReduction.max1_odd_index_unconditional

/-- The literal two local groups have a common ambient Sylow two-subgroup. -/
theorem exists_common_sylow : ∃ S : Sylow 2 Model,
    (S : Subgroup Model) ≤ M ∧ (S : Subgroup Model) ≤ C := by
  let P : Sylow 2 H := default
  have hodd : ¬ 2 ∣ (P.toSubgroup.map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index overlap_index_odd
  let S := (P.isPGroup'.map H.subtype).toSylow hodd
  have hSH : (S : Subgroup Model) ≤ H := map_subtype_le _
  exact ⟨S, hSH.trans (H_eq_inf ▸ inf_le_left), hSH.trans H_le_C⟩

/-- Transport the actual generating pair and its intrinsic bounds to a prescribed Sylow. -/
theorem rankTwo_family_of_equiv (e : G ≃* Model) (T : Sylow 2 G)
    (hM : IsEGenerated 2 M) (hC : IsEGenerated 2 C) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H := by
  obtain ⟨S, hSM, hSC⟩ := exists_common_sylow
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S T'
  let f : Model ≃* G := (MulAut.conj g).trans e.symm
  have hSf : (S : Subgroup Model).map f.toMonoidHom = (T : Subgroup G) := by
    have he : (S : Subgroup Model).map (MulAut.conj g).toMonoidHom =
        (T : Subgroup G).map e.toMonoidHom := congrArg Sylow.toSubgroup hg
    change (S : Subgroup Model).map
      (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
    rw [← map_map, he, map_map]
    simp
  let M' := M.map f.toMonoidHom
  let C' := C.map f.toMonoidHom
  have hTM : (T : Subgroup G) ≤ M' := hSf ▸ map_mono hSM
  have hTC : (T : Subgroup G) ≤ C' := hSf ▸ map_mono hSC
  refine ⟨{C', M'}, ?_, ?_⟩
  · rw [sSup_insert, sSup_singleton]
    change C.map f.toMonoidHom ⊔ M.map f.toMonoidHom = ⊤
    rw [← Subgroup.map_sup, Janko4.AdequateLocal.centralizer_sup_max1_eq_top]
    exact map_top_of_surjective _ f.surjective
  · intro U hU
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact ⟨hTC, hC.map_equiv (f.subgroupMap C)⟩
    · obtain rfl := Set.mem_singleton_iff.mp hU
      exact ⟨hTM, hM.map_equiv (f.subgroupMap M)⟩

/-- Ambient reduction and the Mathieu quotient lift, retaining the centralizer bound. -/
theorem rankTwo_family_of_local_bounds (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Model) (T : Sylow 2 G)
    (h24 : IsEGenerated 1 Sporadic.Mathieu.M24) (hC : IsEGenerated 2 C) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H :=
  rankTwo_family_of_equiv (ambientEquiv L hL e) T
    ((mathieu_isEGenerated_of_m24 h24).mono (by decide)) hC

end CFSG.Quasithin.ChapterE.JankoFour

namespace CFSG.Quasithin.ChapterE.JankoFour
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Conditional E.1.12 input: only the M24 and Aut(M22) generation bounds remain. -/
theorem rankTwo_family_of_mathieu_bounds (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Janko4.Model) (T : Sylow 2 G)
    (h24 : IsEGenerated 1 Sporadic.Mathieu.M24)
    (h22 : IsEGenerated 2 (MulAut Sporadic.Mathieu.M22)) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H :=
  rankTwo_family_of_local_bounds L hL e T h24
    (centralizer_isEGenerated_of_aut_m22 (by decide) h22)
end CFSG.Quasithin.ChapterE.JankoFour

namespace CFSG.Quasithin.ChapterE.JankoFour
open Subgroup Theory.GroupTheory Sporadic.Mathieu

variable {G : Type*} [Group G] [Finite G]

/-- The actual generating family required by E.1.12, with every local bound discharged. -/
theorem rankTwo_family (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Janko4.Model) (T : Sylow 2 G) :
    ∃ Δ : Set (Subgroup G), sSup Δ = ⊤ ∧
      ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 2 H :=
  rankTwo_family_of_mathieu_bounds L hL e T
    mathieu24_isEGenerated autMathieu22_isEGenerated

/-- E.1.12 applied to the two literal local subgroups of the concrete model. -/
theorem model_isEGenerated_two : IsEGenerated 2 Janko4.Model := by
  let T : Sylow 2 Janko4.Model := default
  obtain ⟨Δ, hΔ, hlocal⟩ := rankTwo_family_of_equiv (MulEquiv.refl Janko4.Model) T
    ((mathieu_isEGenerated_of_m24 mathieu24_isEGenerated).mono (by decide))
    (centralizer_isEGenerated_of_aut_m22 (by decide) autMathieu22_isEGenerated)
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 2 T Ω
  rw [← hΔ]
  exact sSup_le fun H hH => ChiefOrbit.overgroup_le_generationTarget T H
    (hlocal H hH).1 hΩ (hlocal H hH).2

/-- Rank-two E-generation for any finite group with simple J4 generalized Fitting subgroup. -/
theorem isEGenerated_two (L : Subgroup G) [IsSimpleGroup L]
    (hL : generalizedFitting G = L) (e : L ≃* Janko4.Model) : IsEGenerated 2 G :=
  model_isEGenerated_two.map_equiv (ambientEquiv L hL e).symm

end CFSG.Quasithin.ChapterE.JankoFour

namespace CFSG.Quasithin.ChapterE
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The J4 upper-generation clause of E.1.14(5), retaining every source hypothesis. -/
theorem isEGenerated_two_of_sqtk_janko4 {K : GroupClass.{u}}
    (_hG : IsSQTK K G) (L : Subgroup G) (hL : L = generalizedFitting G)
    [IsSimpleGroup L] (T : Sylow 2 G) (_hLT : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Janko4.Model) : IsEGenerated 2 G :=
  JankoFour.isEGenerated_two L hL.symm e

/-- The numerical J4 clause of E.1.14(5). -/
theorem generationParameter_le_two_of_sqtk_janko4 {K : GroupClass.{u}}
    (hG : IsSQTK K G) (L : Subgroup G) (hL : L = generalizedFitting G)
    [IsSimpleGroup L] (T : Sylow 2 G) (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* Janko4.Model) : generationParameter G ≤ 2 :=
  generationParameter_le (by decide) (isEGenerated_two_of_sqtk_janko4 hG L hL T hLT e)

end CFSG.Quasithin.ChapterE
