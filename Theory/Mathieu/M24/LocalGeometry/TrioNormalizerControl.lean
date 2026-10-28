module
public import Theory.Mathieu.M24.LocalGeometry.EightNormalizers
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds.NativeNormalizers
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.TensorSection.Irreducibility
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.TrioCore
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.Algebra.Module.ZMod
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Recognition and normalizer control for the native Mathieu trio

An index-63 overgroup of a Sylow two-subgroup with nontrivial two-core is
an actual trio stabilizer. The native elementary normalizer catalogue puts
it in an octad, trio or sextet stabilizer; the order 64512 excludes the
octad and sextet cases and gives equality in the trio case.

The trio core is the irreducible natural tensor module of order 64 and is
self-centralizing. Hence every normal subgroup which is not a two-group
contains that core. The checked Sylow elementary catalogue has exactly two
order-64 rows. Their different normalizer orders show that the trio core
cannot fuse to the sextet core. Sylow conjugacy inside the trio stabilizer
therefore proves that any conjugate of its core lying there is the same
core. An actor whose normal closure of a non-two normal seed stays in the
trio stabilizer must consequently stabilize the trio itself.

The actual source application, retaining its component image, original
Sylow and quotient maps, is in NaturalSource/Local/Normalizers/Mathieu.
Source: Aschbacher--Smith, 12.5.3--4, printed pp.818--819, and H.14.1,
printed pp.396--397. This uses the existing native permutation and tensor
proofs without introducing further finite computation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.TrioRecognition
open PairOvergroups EvenCatalogue MathieuCode.TrioCalculation

/-- The order of the literal standard trio stabilizer. -/
theorem standard_trio_card : Nat.card (trioStabilizer standardTrio) = 64512 := by
  have hq : Nat.card (trioStabilizer standardTrio ⧸ pCore 2 (trioStabilizer standardTrio)) = 1008 := by
    rw [Nat.card_congr standardQuotientEquiv.toEquiv]
    change Nat.card (Equiv.Perm (Fin 3) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = _
    rw [Nat.card_prod,Nat.card_perm,Nat.card_fin,Atlas.Comparisons.Exceptional.sl3Two_card]
    rfl
  have hh := (pCore 2 (trioStabilizer standardTrio)).card_mul_index
  rw [index_eq_card,hq,M24ChapterHStabilizers.TrioAction.core_card] at hh
  exact hh.symm

private abbrev markedSylow : Sylow 2 M24 := Sylow.ofCard SylowNormalizer.candidate (by
  rw [SylowNormalizer.candidate_card,m24_order]
  decide +kernel)

private theorem fixed_trio (A : Subgroup M24)
    (hSA : SylowNormalizer.candidate ≤ A) (hc : pCore 2 A ≠ ⊥)
    (hcard : Nat.card A = 64512) : A = EvenCandidates.localGroup 0 := by
  have htwo : IsTwoLocal (normalizer (A.pCoreIn 2 : Set M24)) := by
    refine ⟨A.pCoreIn 2,?_,pCore_isPGroup.map A.subtype,rfl⟩
    intro he
    exact hc ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp he)
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal htwo
  have hAN : A ≤ N := (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))).trans hNN
  obtain ⟨R,hR,hn,he,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le
    markedSylow hN (hSA.trans hAN)
  let := he
  obtain ⟨i,hi⟩ := Coverage.catalogue_of_normal_exponent_two R hR hn (fun x hx => by
    have hx2 : (⟨x,hx⟩ : R) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p _
    apply Subtype.ext
    change (x : M24) * (x : M24) = 1
    exact congrArg (fun z : R => ((z : (markedSylow : Subgroup M24)) : M24)) hx2)
  have hNi : N = localGroup i := by rw [hNR,hi]; rfl
  have hAi : A ≤ localGroup i := hNi ▸ hAN
  rcases normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · exact (EightNormalizers.octad_no_subgroup_order64512 O
      (A.subgroupOf (octadStabilizer O))
      ((Nat.card_congr (subgroupOfEquivOfLe (hAi.trans hO)).toEquiv).trans hcard)).elim
  · have hAk := hAi.trans hk
    fin_cases k
    · exact eq_of_le_of_card_ge hAk (by
        rw [Nat.card_congr NormalSeeds.trioNormalizerEquiv.toEquiv,standard_trio_card,hcard])
    · have hd := card_dvd_of_le hAk
      change Nat.card A ∣ Nat.card (EvenCandidates.localGroup 1) at hd
      rw [hcard,Nat.card_congr NormalSeeds.sextetNormalizerEquiv.toEquiv,
        SextetCore.stabilizer_card] at hd
      norm_num at hd

/-- An index-63 Sylow overgroup with nontrivial two-core is an actual trio stabilizer. -/
theorem exists_conjugate_trio (S : Sylow 2 M24) (A : Subgroup M24)
    (hSA : (S : Subgroup M24) ≤ A) (hc : pCore 2 A ≠ ⊥)
    (hi : (S : Subgroup M24).relIndex A = 63) :
    ∃ g : M24, A.map (MulAut.conj g).toMonoidHom = trioStabilizer standardTrio := by
  have hS : Nat.card S = 1024 := by
    rw [S.card_eq_multiplicity,m24_order]
    decide +kernel
  have hcard : Nat.card A = 64512 := by
    have hh := ((S : Subgroup M24).subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hSA).toEquiv,hS] at hh
    change 1024 * (S : Subgroup M24).relIndex A = Nat.card A at hh
    rw [hi] at hh
    exact hh.symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S markedSylow
  let e := MulAut.conj g
  have hmap : (S : Subgroup M24).map e.toMonoidHom = SylowNormalizer.candidate :=
    congrArg Sylow.toSubgroup hg
  have hA : A.map e.toMonoidHom = EvenCandidates.localGroup 0 := by
    apply fixed_trio _ (hmap ▸ map_mono hSA) ?_
      ((card_map_of_injective e.injective).trans hcard)
    intro hz
    have hh := pCore_map_iso 2 (e.subgroupMap A)
    change (pCore 2 A).map (e.subgroupMap A).toMonoidHom = pCore 2 (A.map e.toMonoidHom) at hh
    rw [hz] at hh
    exact hc ((map_eq_bot_iff_of_injective _ (e.subgroupMap A).injective).mp hh)
  refine ⟨FourNormalizers.certificateElement 0 * g,?_⟩
  have hh := congrArg (map (MulAut.conj (FourNormalizers.certificateElement 0)).toMonoidHom) hA
  rw [NormalSeeds.trio_normalizer_map_eq,map_map] at hh
  exact hh

end Sporadic.Mathieu.M24LocalGeometry.TrioRecognition
namespace Sporadic.Mathieu.M24LocalGeometry.TrioNormalSeeds
open PairOvergroups M24ChapterHStabilizers.TrioAction MathieuCode.TrioCalculation

/-- The intrinsic translation core is minimal normal in the actual trio stabilizer. -/
theorem normal_subgroup_of_core (N : Subgroup Stabilizer) [N.Normal]
    (hle : N ≤ Kernel) : N = ⊥ ∨ N = Kernel := by
  let H : AddSubgroup NaturalTensor :=
    { carrier := {z | (tensorEquiv (Multiplicative.ofAdd z)).val ∈ N}
      zero_mem' := by
        change (tensorEquiv 1).val ∈ N
        rw [map_one]
        exact N.one_mem
      add_mem' := by
        intro a b ha hb
        change (tensorEquiv (Multiplicative.ofAdd a * Multiplicative.ofAdd b)).val ∈ N
        rw [map_mul]
        exact N.mul_mem ha hb
      neg_mem' := by
        intro a ha
        change (tensorEquiv (Multiplicative.ofAdd a)⁻¹).val ∈ N
        rw [map_inv]
        exact N.inv_mem ha }
  let W : Subrepresentation standardTensorRepresentation :=
    { toSubmodule := AddSubgroup.toZModSubmodule 2 H
      apply_mem_toSubmodule := by
        intro g z hz
        change (tensorEquiv (Multiplicative.ofAdd (standardTensorRepresentation g z))).val ∈ N
        rw [←tensorEquiv_conjugation]
        exact (inferInstance : N.Normal).conj_mem _ hz g }
  let := standardTensorRepresentation_irreducible
  rcases eq_bot_or_eq_top W with hz | ht
  · left
    apply bot_unique
    intro n hn
    obtain ⟨z,hz'⟩ := tensorEquiv.surjective ⟨n,hle hn⟩
    have hm : z.toAdd ∈ W := by
      change (tensorEquiv z).val ∈ N
      rw [hz']
      exact hn
    have hz0 : z.toAdd = 0 := by
      rw [hz] at hm
      exact hm
    have hz1 : z = 1 := Multiplicative.toAdd.injective hz0
    have hh := congrArg Subtype.val hz'
    rw [hz1,map_one] at hh
    exact mem_bot.mpr hh.symm
  · right
    apply le_antisymm hle
    intro n hn
    obtain ⟨z,hz'⟩ := tensorEquiv.surjective ⟨n,hn⟩
    have hm : z.toAdd ∈ W := by rw [ht]; trivial
    change (tensorEquiv z).val ∈ N at hm
    rwa [hz'] at hm

/-- The literal standard core is self-centralizing. -/
theorem core_selfCentralizing : centralizer (Kernel : Set Stabilizer) ≤ Kernel := by
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 FourNormalizers.trioEquiv).mp
    FourNormalizers.trio_core_selfCentralizing

/-- A non-two normal subgroup contains the full order-64 translation core. -/
theorem core_le_normal_not_two (N : Subgroup Stabilizer) [N.Normal]
    (hp : ¬ IsPGroup 2 N) : Kernel ≤ N := by
  rcases normal_subgroup_of_core (N ⊓ Kernel) inf_le_right with hz | he
  · have hc : N ≤ centralizer (Kernel : Set Stabilizer) :=
      commutator_eq_bot_iff_le_centralizer.mp (bot_unique (hz ▸ (commutator_le_inf N Kernel : ⁅N,Kernel⁆ ≤ N ⊓ Kernel)))
    exact (hp (pCore_isPGroup.to_le (hc.trans core_selfCentralizing))).elim
  · exact he.symm.le.trans inf_le_left

end Sporadic.Mathieu.M24LocalGeometry.TrioNormalSeeds
namespace Sporadic.Mathieu.M24LocalGeometry.TrioNormalSeeds
open PairOvergroups M24ChapterHStabilizers.TrioAction M24ChapterHStabilizers.ElementaryFusion
open EvenCatalogue

private theorem core_normalizer_card : Nat.card (normalizer (trioCore : Set M24)) = 64512 := by
  rw [←trioCandidate_eq_core (show Nat.card trioCore = 64 from core_ambient_card),
    markedCandidate,←map_equiv_normalizer_eq,card_map_of_injective (MulAut.conj transport).injective]
  exact (Nat.card_congr NormalSeeds.trioNormalizerEquiv.toEquiv).trans TrioRecognition.standard_trio_card

private theorem sextet_core_normalizer_card :
    Nat.card (normalizer (SextetCore.core : Set M24)) = 138240 := by
  rw [←sextetCandidate_eq_core,markedCandidate,←map_equiv_normalizer_eq,
    card_map_of_injective (MulAut.conj transport).injective]
  exact (Nat.card_congr NormalSeeds.sextetNormalizerEquiv.toEquiv).trans SextetCore.stabilizer_card

/-- The trio is recovered as the full ambient normalizer of its translation core. -/
theorem normalizer_core : normalizer (trioCore : Set M24) = trioStabilizer standardTrio := by
  apply (eq_of_le_of_card_ge
    ((trioStabilizer standardTrio).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (trioStabilizer standardTrio)))) ?_).symm
  change Nat.card (normalizer (trioCore : Set M24)) ≤ Nat.card (trioStabilizer standardTrio)
  rw [core_normalizer_card,TrioRecognition.standard_trio_card]

private theorem core_not_conjugate_sextet (g : M24) :
    trioCore.map (MulAut.conj g).toMonoidHom ≠ SextetCore.core := by
  intro he
  have hh := congrArg (fun Q : Subgroup M24 => Nat.card (normalizer (Q : Set M24))) he
  rw [←map_equiv_normalizer_eq,card_map_of_injective (MulAut.conj g).injective,
    core_normalizer_card,sextet_core_normalizer_card] at hh
  omega

/-- A conjugate of the trio core lying in the trio stabilizer equals that core. -/
theorem conj_core_le_iff (g : M24) :
    trioCore.map (MulAut.conj g).toMonoidHom ≤ trioStabilizer standardTrio ↔
      g ∈ trioStabilizer standardTrio := by
  constructor
  · intro hg
    let P := trioStabilizer standardTrio
    let Q := trioCore.map (MulAut.conj g).toMonoidHom
    have hEQ : IsElementaryAbelian 2 Q := by
      let : IsElementaryAbelian 2 trioCore := core_ambient_elementary
      exact IsElementaryAbelian.map _
    have hQc : Nat.card Q = 64 :=
      (card_map_of_injective (MulAut.conj g).injective).trans core_ambient_card
    obtain ⟨R,hR⟩ := ((hEQ.isPGroup 2 Q).of_equiv (subgroupOfEquivOfLe hg).symm).exists_le_sylow
    let S := standardSylow.subtype standardSylow_le_trio
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq P R S
    have hQR : (Q.subgroupOf P).map (MulAut.conj a).toMonoidHom ≤ (S : Subgroup P) := by
      rw [←ha]
      exact map_mono hR
    have hQS : Q.map (MulAut.conj (a : M24)).toMonoidHom ≤ (standardSylow : Subgroup M24) := by
      have hh := map_mono (f := P.subtype) hQR
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le standardSylow_le_trio,map_map] at hh
      have he : P.subtype.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (a : M24)).toMonoidHom.comp P.subtype := by ext x; rfl
      rw [he,←map_map,map_subgroupOf_eq_of_le hg] at hh
      exact hh
    have hE : IsElementaryAbelian 2 (Q.map (MulAut.conj (a : M24)).toMonoidHom) := by
      let := hEQ
      exact IsElementaryAbelian.map _
    have hcard : Nat.card (Q.map (MulAut.conj (a : M24)).toMonoidHom) = 64 :=
      (card_map_of_injective (MulAut.conj (a : M24)).injective).trans hQc
    have he := (elementary_card64_iff_eq_core _).mp ⟨hE,hcard,hQS⟩
    have hcomp : (MulAut.conj (a : M24)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj ((a : M24) * g)).toMonoidHom := by ext x; simp [MulAut.conj_apply,mul_assoc]
    change (trioCore.map _).map _ = _ ∨ (trioCore.map _).map _ = _ at he
    rw [map_map,hcomp] at he
    have hfix := he.resolve_left (core_not_conjugate_sextet _)
    have hag : (a : M24) * g ∈ P := by
      change (a : M24) * g ∈ trioStabilizer standardTrio
      rw [←normalizer_core]
      exact mem_normalizer_iff_map_conj_eq.mpr hfix
    have hh := P.mul_mem (P.inv_mem a.property) hag
    simpa only [inv_mul_cancel_left] using hh
  · intro hg
    have he := mem_normalizer_iff_map_conj_eq.mp (normalizer_core.symm ▸ hg)
    change trioCore.map (MulAut.conj g).toMonoidHom = trioCore at he
    rw [he]
    exact map_subtype_le _

/-- A non-two normal seed in the trio stabilizer controls an actor whose
conjugate closure remains in that same stabilizer. -/
theorem actor_le_of_seed_closure (Y A : Subgroup M24)
    (hY : Y ≤ trioStabilizer standardTrio)
    (hn : (Y.subgroupOf (trioStabilizer standardTrio)).Normal)
    (hp : ¬ IsPGroup 2 Y)
    (hc : conjugateSpanBy Y A ≤ trioStabilizer standardTrio) :
    A ≤ trioStabilizer standardTrio := by
  let := hn
  have hnot : ¬ IsPGroup 2 (Y.subgroupOf (trioStabilizer standardTrio)) := fun ht =>
    hp (ht.of_equiv (subgroupOfEquivOfLe hY))
  have hcore : trioCore ≤ Y := by
    have hh := map_mono (f := (trioStabilizer standardTrio).subtype)
      (core_le_normal_not_two (Y.subgroupOf _) hnot)
    rw [map_subgroupOf_eq_of_le hY] at hh
    exact hh
  intro a ha
  apply (conj_core_le_iff a).mp
  rintro _ ⟨q,hq,rfl⟩
  exact hc (subset_closure ⟨a,ha,q,hcore hq,rfl⟩)

end Sporadic.Mathieu.M24LocalGeometry.TrioNormalSeeds
