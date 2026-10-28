module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.ThreeSubgroups
public import Theory.Representation.EndFieldRep
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Commutation of the actual exchanged blocks

Restrict the relative subnormal block from H to the literal product K, and
transport its conjugate using the actual exchanger in U. The blocks have
quasisimple two-core quotients. Their images modulo O₂(K) are distinct
components, so they commute there. Two-perfectness then makes the original
blocks normalize one another; their commutator lies in both intrinsic two-cores.

The remaining lifting argument uses the irreducible module U(A)/C_U(A)(A).
A perfect group acting on A trivially modulo O₂(A) commutes with A on this
module. Schur's lemma and the finite endomorphism field make that action
trivial. Coprime commutator idempotence and the three-subgroup lemma lift
this to centralization of U(A), then to commutation of the blocks.

This proves the quasisimple-quotient case directly. It does not invoke the
unproved general C.1.9 interface or omit its additional A₃-block hypothesis:
no order-three-quotient block enters the argument. In particular, the proof
needs neither a characteristic-two assertion for H nor a transfer of the
supplied characteristic-two assertion from K to H. It works for every field
parameter, with the required field-four statement exported separately.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.7–10,
printed pp.123–124 (PDF pp.134–135), and the exchanged-block case in the proof
of 15.4.20, printed pp.1163–1164 (PDF pp.1180–1181).
-/

public section


open scoped IsMulCommutative MonoidAlgebra
open Subgroup Representation

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality.ExchangedCommutation.Schur
variable {A B W : Type*} [Group A] [Group B] [Group W]
  [Finite W] [IsElementaryAbelian 2 W]

private def linearAction (ρ : A →* MulAut W) : Representation (ZMod 2) A (Additive W) where
  toFun a := (ρ a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext w; exact DFunLike.congr_fun (map_one ρ) w
  map_mul' a b := by ext w; exact DFunLike.congr_fun (map_mul ρ a b) w

omit [Finite W] in
private theorem linearAction_irreducible (ρ : A →* MulAut W) [Nontrivial W]
    (hirr : ∀ D : Subgroup W, (∀ a w, w ∈ D → ρ a w ∈ D) → D = ⊥ ∨ D = ⊤) :
    IsIrreducible (linearAction ρ) := by
  constructor
  intro N
  let D : Subgroup W := N.toSubmodule.toAddSubgroup.toSubgroup
  have hd : D = ⊥ ∨ D = ⊤ := hirr D (fun a w hw => N.apply_mem_toSubmodule a hw)
  rcases hd with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro w hw
    exact (show w.toMul ∈ (⊥ : Subgroup W) from hb ▸ hw)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    exact (show w.toMul ∈ D from ht ▸ mem_top w.toMul)

set_option backward.isDefEq.respectTransparency false in
private theorem commuting_perfect_action [Nontrivial W] [Group.IsPerfect B]
    (ρ : A →* MulAut W) (σ : B →* MulAut W)
    (hirr : ∀ D : Subgroup W, (∀ a w, w ∈ D → ρ a w ∈ D) → D = ⊥ ∨ D = ⊤)
    (hc : ∀ a b, ρ a * σ b = σ b * ρ a) : σ = 1 := by
  let r := linearAction ρ
  let s := linearAction σ
  let : IsIrreducible r := linearAction_irreducible ρ hirr
  let t : B →* IntertwiningMap r r := {
    toFun := fun b => ⟨s b, fun a => by
      ext w
      exact DFunLike.congr_fun (hc a b).symm w⟩
    map_one' := by ext w; exact DFunLike.congr_fun (map_one s) w
    map_mul' := by intro a b; ext w; exact DFunLike.congr_fun (map_mul s a b) w }
  let e := IntertwiningMap.equivAlgEnd r
  let f := (e.toMonoidHom.comp t).toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    exact Units.ext (mul_comm _ _)⟩⟩
  let : Subsingleton f.range := inferInstance
  have hf (b : B) : f b = 1 := by
    exact congrArg Subtype.val (Subsingleton.elim (⟨f b, b, rfl⟩ : f.range) 1)
  ext b w
  have ht : t b = 1 := e.toMulEquiv.injective (by
    rw [map_one]
    exact congrArg Units.val (hf b))
  exact DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap ht) (Additive.ofMul w)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality.ExchangedCommutation.Schur

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
open Subgroup Theory.GroupTheory ChapterC
open scoped commutatorElement

namespace ExchangedCommutation

variable {L : Type*} [Group L]

private def blockAut : MulAut L →* MulAut (BlockModule L) where
  toFun := blockModuleEquiv
  map_one' := by
    ext u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) u
    rfl
  map_mul' a b := by
    ext u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) u
    rfl

private theorem blockAut_mk (a : MulAut L) (u : blockU L) :
    blockAut a (QuotientGroup.mk' (blockFixed L) u) =
      QuotientGroup.mk' (blockFixed L) (blockUEquiv a u) := rfl

private theorem blockAction_irreducible (h : IsShort L)
    (ρ : L →* MulAut (BlockModule L))
    (hρ : ∀ (l : L) (u : blockU L),
      ρ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u))
    (D : Subgroup (BlockModule L))
    (hD : ∀ l w, w ∈ D → ρ l w ∈ D) : D = ⊥ ∨ D = ⊤ := by
  let q := QuotientGroup.mk' (blockFixed L)
  let N := (D.comap q).map (blockU L).subtype
  have hN : N.Normal := by
    constructor
    intro x hx l
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨blockConjugate L l u, ?_, rfl⟩
    change q (blockConjugate L l u) ∈ D
    rw [← hρ]
    exact hD l (q u) hu
  have hlo : blockU L ⊓ center L ≤ N := by
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    change q ⟨x, hx.1⟩ ∈ D
    have he : q ⟨x, hx.1⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hx.2
    rw [he]
    exact D.one_mem
  rcases h.irreducible.2 N hN hlo (map_subtype_le _) with hz | ht
  · left
    apply bot_unique
    intro w hw
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) w
    have hu : (u : L) ∈ N := ⟨u, hw, rfl⟩
    rw [hz] at hu
    exact (QuotientGroup.eq_one_iff u).mpr hu.2
  · right
    apply top_unique
    intro w _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) w
    have hu : (u : L) ∈ N := by rw [ht]; exact u.property
    obtain ⟨v, hv, he⟩ := hu
    have he' : v = u := Subtype.ext he
    exact he' ▸ hv

variable {D : Type*} [Group D] [Finite D]

private theorem perfect_normal_block_centralizes_layer (A B : Subgroup D)
    [A.Normal] [Group.IsPerfect B] (hA : IsShort A)
    (hc : ⁅A, B⁆ ≤ A.pCoreIn 2) :
    ⁅(blockU A).map A.subtype, B⁆ = ⊥ := by
  let ρ : D →* MulAut (BlockModule A) := blockAut.comp MulAut.conjNormal
  let r := ρ.comp A.subtype
  let s := ρ.comp B.subtype
  have hr (a : A) (u : blockU A) :
      r a (QuotientGroup.mk' (blockFixed A) u) =
        QuotientGroup.mk' (blockFixed A) (blockConjugate A a u) := rfl
  have hker : A.pCoreIn 2 ≤ ρ.ker := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA.core_le_moduleAction_ker r hr ha
  have hcomm (a : A) (b : B) : r a * s b = s b * r a := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅ρ (a : D), ρ (b : D)⁆ = 1
    rw [← map_commutatorElement]
    exact hker (hc (commutator_mem_commutator a.property b.property))
  let := hA.module_elementary
  let := hA.module_nontrivial
  have hs : s = 1 := Schur.commuting_perfect_action r s
    (blockAction_irreducible hA r hr) hcomm
  let U := (blockU A).map A.subtype
  let Z := (center A).map A.subtype
  have hUB : ⁅U, B⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨u, hu, rfl⟩ := hu
    let v : blockU A := ⟨u, hu⟩
    have he := DFunLike.congr_fun (DFunLike.congr_fun hs ⟨b, hb⟩)
      (QuotientGroup.mk' (blockFixed A) v)
    change QuotientGroup.mk' (blockFixed A) (blockUEquiv (MulAut.conjNormal b) v) =
      QuotientGroup.mk' (blockFixed A) v at he
    have hz := QuotientGroup.eq_iff_div_mem.mp he
    refine ⟨(blockUEquiv (MulAut.conjNormal b) v : A) / u, hz, ?_⟩
    simp only [blockUEquiv_val, commutatorElement_def, div_eq_mul_inv]
    rfl
  have hZA : ⁅Z, A⁆ = ⊥ := by
    rw [← A.range_subtype, MonoidHom.range_eq_map, ← map_commutator]
    simp only [commutator_top_right_eq_bot_iff_le_center.mpr le_rfl, Subgroup.map_bot]
  have hcoreU : ⁅A.pCoreIn 2, U⁆ = ⊥ := by
    rw [pCoreIn, ← map_commutator]
    simpa only [Subgroup.map_bot] using congrArg (Subgroup.map A.subtype)
      (commutator_eq_bot_iff_le_centralizer.mpr hA.core_centralizes_blockU)
  have h1 : ⁅⁅U, B⁆, A⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hUB le_rfl).trans hZA.le)
  have h2 : ⁅⁅B, A⁆, U⁆ = ⊥ := by
    rw [commutator_comm B A]
    exact le_bot_iff.mp ((commutator_mono hc le_rfl).trans hcoreU.le)
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  have hUA : ⁅U, A⁆ = U := by
    simpa only [U, blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype] using
      congrArg (Subgroup.map A.subtype)
      (commutator_isPPerfect_idempotent (⊤ : Subgroup A) (pCore 2 A)
        (hA.twoPerfect.of_surjective (topEquiv : (⊤ : Subgroup A) ≃* A).symm.toMonoidHom
          (topEquiv : (⊤ : Subgroup A) ≃* A).symm.surjective)
        pCore_isPGroup le_normalizer_of_normal)
  rwa [commutator_comm A U, hUA] at h3

private theorem normal_perfect_blocks_commute (A B : Subgroup D)
    [A.Normal] [Group.IsPerfect A] [Group.IsPerfect B]
    (hA : IsShort A) (hc : ⁅A, B⁆ ≤ A.pCoreIn 2) : ⁅A, B⁆ = ⊥ := by
  let U := (blockU A).map A.subtype
  have hn : U.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← A.normalizer_eq_top]
    exact normalizer_le_normalizer_characteristic_image A (blockU A)))
  let := hn
  have hcore : ⁅A.pCoreIn 2, A⁆ = U := by
    change ⁅(pCore 2 A).map A.subtype, A⁆ = (blockU A).map A.subtype
    rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have h1 : ⁅⁅A, B⁆, A⁆ ≤ U := (commutator_mono hc le_rfl).trans hcore.le
  have h2 : ⁅⁅B, A⁆, A⁆ ≤ U := by rwa [commutator_comm B A]
  have hAB := commutator_commutator_le_of_rotate h1 h2
  rw [commutator_eq_self] at hAB
  apply commutator_eq_bot_of_iterated_eq_bot
  exact le_bot_iff.mp ((commutator_mono hAB le_rfl).trans
    (perfect_normal_block_centralizes_layer A B hA hc).le)

end ExchangedCommutation
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC


namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality.ExchangedCommutation
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem perfect_of_twoPerfect (h : IsPPerfect 2 D)
    [IsQuasisimple (D ⧸ pCore 2 D)] : Group.IsPerfect D := by
  have hs : _root_.commutator D ⊔ pCore 2 D = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 D)
    have hm : (_root_.commutator D).map q = ⊤ := by
      rw [commutator_def, map_commutator, map_top_of_surjective q
        (QuotientGroup.mk'_surjective _)]
      exact Group.IsPerfect.commutator_eq_top
    have hh := congrArg (Subgroup.comap q) hm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  exact ⟨h _ inferInstance (isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hs)⟩

omit [Finite D] in
private theorem eq_of_map_eq (A B : Subgroup D) (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hpA : IsPPerfect 2 A) (hpB : IsPPerfect 2 B)
    (he : A.map (QuotientGroup.mk' (pCore 2 D)) =
      B.map (QuotientGroup.mk' (pCore 2 D))) : A = B := by
  have hnA : pCore 2 D ≤ normalizer A :=
    le_normalizer_of_isSubnormal_isPPerfect A _ hA hpA pCore_isPGroup
      le_normalizer_of_normal
  have hnB : pCore 2 D ≤ normalizer B :=
    le_normalizer_of_isSubnormal_isPPerfect B _ hB hpB pCore_isPGroup
      le_normalizer_of_normal
  have hs : A ⊔ pCore 2 D = B ⊔ pCore 2 D := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using
      congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 D))) he
  have ha := embedded_pResidual_join_pGroup A (pCore 2 D) hpA pCore_isPGroup hnA
  have hb := embedded_pResidual_join_pGroup B (pCore 2 D) hpB pCore_isPGroup hnB
  rw [hs] at ha
  exact ha.symm.trans hb

private noncomputable def coreQuotientEquiv (A : Subgroup D) (hA : A.IsSubnormal) :
    (A ⧸ pCore 2 A) ≃* A.map (QuotientGroup.mk' (pCore 2 D)) := by
  let f := (QuotientGroup.mk' (pCore 2 D)).subgroupMap A
  have he : f.ker = pCore 2 A := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hA).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 D)).subgroupMap_surjective A))

private theorem quotient_commutation (A B : Subgroup D)
    (hA : IsBlock A) (hB : IsBlock B)
    (hqA : IsQuasisimple (A ⧸ pCore 2 A))
    (hqB : IsQuasisimple (B ⧸ pCore 2 B)) (hne : A ≠ B) :
    ⁅A, B⁆ ≤ pCore 2 D := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let := hqA
  let := hqB
  have hAc : IsComponent (D ⧸ pCore 2 D) (A.map q) :=
    ⟨hA.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (coreQuotientEquiv A hA.subnormal)⟩
  have hBc : IsComponent (D ⧸ pCore 2 D) (B.map q) :=
    ⟨hB.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (coreQuotientEquiv B hB.subnormal)⟩
  have hn : A.map q ≠ B.map q :=
    fun he => hne (eq_of_map_eq A B hA.subnormal hB.subnormal
      hA.short.twoPerfect hB.short.twoPerfect he)
  have hc := hAc.commutator_eq_bot_of_ne hBc hn
  rwa [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hc

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality.ExchangedCommutation

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality.ExchangedCommutation
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem normalizes_of_commutator_le_core (A B : Subgroup D)
    (hA : IsBlock A) (hc : ⁅A, B⁆ ≤ pCore 2 D) : B ≤ normalizer A := by
  have hnA : pCore 2 D ≤ normalizer A :=
    le_normalizer_of_isSubnormal_isPPerfect A _ hA.subnormal hA.short.twoPerfect
      pCore_isPGroup le_normalizer_of_normal
  have hres := embedded_pResidual_join_pGroup A (pCore 2 D)
    hA.short.twoPerfect pCore_isPGroup hnA
  have hn : B ≤ normalizer ((A ⊔ pCore 2 D : Subgroup D) : Set D) := by
    let q := QuotientGroup.mk' (pCore 2 D)
    have hqc : ⁅A.map q, B.map q⁆ = ⊥ := by
      rwa [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hbn : B.map q ≤ normalizer (A.map q : Set (D ⧸ pCore 2 D)) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hqc)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := (map_le_iff_le_comap.mp hbn).trans ((A.map q).le_normalizer_comap q)
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hh
  rw [← hres]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ _)

private theorem pair_core_bound (A B : Subgroup D)
    (hA : IsBlock A) (hB : IsBlock B)
    (hqA : IsQuasisimple (A ⧸ pCore 2 A))
    (hqB : IsQuasisimple (B ⧸ pCore 2 B)) (hne : A ≠ B) :
    B ≤ normalizer A ∧ A ≤ normalizer B ∧
      ⁅A, B⁆ ≤ A.pCoreIn 2 ⊓ B.pCoreIn 2 := by
  have hc := quotient_commutation A B hA hB hqA hqB hne
  have hnA := normalizes_of_commutator_le_core A B hA hc
  have hnB := normalizes_of_commutator_le_core B A hB (by
    rwa [commutator_comm])
  have hp : IsPGroup 2 ↥(⁅A, B⁆ : Subgroup D) := pCore_isPGroup.to_le hc
  refine ⟨hnA, hnB, le_inf ?_ ?_⟩
  · exact le_pCoreIn_of_normalizes hp
      (le_normalizer_iff_commutator_le_left.mp hnA)
      (normalizer_commutator_ge_left A B)
  · exact le_pCoreIn_of_normalizes hp
      (le_normalizer_iff_commutator_le_right.mp hnB)
      (normalizer_commutator_ge_right A B)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality.ExchangedCommutation

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

namespace ExchangedCommutation

private def firstInK {c : ContraryData κ d i j} (b : ExchangedBlock c) : Subgroup c.K :=
  b.first.subgroupOf c.K

private def secondInK {c : ContraryData κ d i j} (b : ExchangedBlock c) : Subgroup c.K :=
  (b.first.map (MulAut.conj b.exchanger).toMonoidHom).subgroupOf c.K

variable (c : ContraryData κ d i j) (b : ExchangedBlock c)

private theorem first_le_K : b.first ≤ c.K := b.product ▸ le_sup_left

private theorem second_le_K : b.first.map (MulAut.conj b.exchanger).toMonoidHom ≤ c.K :=
  b.product ▸ le_sup_right

private theorem firstInK_map : (firstInK b).map c.K.subtype = b.first :=
  map_subgroupOf_eq_of_le (first_le_K c b)

private theorem secondInK_map : (secondInK b).map c.K.subtype =
    b.first.map (MulAut.conj b.exchanger).toMonoidHom :=
  map_subgroupOf_eq_of_le (second_le_K c b)

private theorem normalizes_K : c.H ≤ normalizer (c.K : Set G) := by
  rw [← c.conjugate_closure]
  apply le_normalizer_iff.mpr
  intro h hh v hv
  obtain ⟨v, hv, rfl⟩ := hv
  exact ⟨(⟨h, hh⟩ : c.H) * v * (⟨h, hh⟩ : c.H)⁻¹,
    (normalClosure_normal (s := (d.wholeX.subgroupOf c.H : Set c.H))).conj_mem
      v hv ⟨h, hh⟩, rfl⟩

private def exchangerOnK : MulAut c.K :=
  c.K.normalizerMonoidHom ⟨b.exchanger, normalizes_K c
    ((c.sylow_image ▸ map_subtype_le (c.sylow : Subgroup c.H)) b.exchanger_mem)⟩

private theorem firstInK_conjugate : (firstInK b).map (exchangerOnK c b).toMonoidHom =
    secondInK b := by
  apply map_injective c.K.subtype_injective
  rw [map_map]
  have he : c.K.subtype.comp (exchangerOnK c b).toMonoidHom =
      (MulAut.conj b.exchanger).toMonoidHom.comp c.K.subtype := by
    ext a
    rfl
  rw [he, ← map_map, firstInK_map, secondInK_map]

private theorem firstInK_block : IsBlock (firstInK b) := by
  have hKH : c.K ≤ c.H := c.product ▸ le_sup_left
  refine ⟨inferInstance,
    b.model.2.1.of_mulEquiv (subgroupOfEquivOfLe (first_le_K c b)).symm, ?_⟩
  exact b.relative_block.subnormal.comap (inclusion hKH)

private theorem secondInK_block : IsBlock (secondInK b) := by
  rw [← firstInK_conjugate]
  exact (firstInK_block c b).map_equiv (exchangerOnK c b)

private theorem firstInK_quasisimple : IsQuasisimple (firstInK b ⧸ pCore 2 (firstInK b)) := by
  let := b.quotient_quasisimple
  let e := (subgroupOfEquivOfLe (first_le_K c b)).symm
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

private theorem secondInK_quasisimple :
    IsQuasisimple (secondInK b ⧸ pCore 2 (secondInK b)) := by
  rw [← firstInK_conjugate]
  let := firstInK_quasisimple c b
  let e := (exchangerOnK c b).subgroupMap (firstInK b)
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

private theorem firstInK_ne_secondInK : firstInK b ≠ secondInK b := by
  intro he
  apply b.exchanger_moves
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hm := congrArg (Subgroup.map c.K.subtype) he
  rw [firstInK_map, secondInK_map] at hm
  exact hm.symm

private theorem pair_generates : firstInK b ⊔ secondInK b = ⊤ := by
  apply map_injective c.K.subtype_injective
  rw [Subgroup.map_sup, firstInK_map, secondInK_map, b.product,
    ← MonoidHom.range_eq_map, range_subtype]

private theorem pair_normal_and_core_bound :
    (firstInK b).Normal ∧ (secondInK b).Normal ∧
      ⁅firstInK b, secondInK b⁆ ≤
        (firstInK b).pCoreIn 2 ⊓ (secondInK b).pCoreIn 2 := by
  obtain ⟨hnA, hnB, hc⟩ := pair_core_bound _ _
    (firstInK_block c b) (secondInK_block c b)
    (firstInK_quasisimple c b) (secondInK_quasisimple c b)
    (firstInK_ne_secondInK c b)
  refine ⟨normalizer_eq_top_iff.mp ?_, normalizer_eq_top_iff.mp ?_, hc⟩
  · apply top_unique
    rw [← pair_generates c b]
    exact sup_le (firstInK b).le_normalizer hnA
  · apply top_unique
    rw [← pair_generates c b]
    exact sup_le hnB (secondInK b).le_normalizer

private theorem firstInK_perfect : Group.IsPerfect (firstInK b) := by
  let := firstInK_quasisimple c b
  exact perfect_of_twoPerfect (firstInK_block c b).short.twoPerfect

private theorem secondInK_perfect : Group.IsPerfect (secondInK b) := by
  let := secondInK_quasisimple c b
  exact perfect_of_twoPerfect (secondInK_block c b).short.twoPerfect

private theorem exchanged_blocks_commute :
    ⁅b.first, b.first.map (MulAut.conj b.exchanger).toMonoidHom⁆ = ⊥ := by
  obtain ⟨hnA, _, hc⟩ := pair_normal_and_core_bound c b
  let := hnA
  let := firstInK_perfect c b
  let := secondInK_perfect c b
  have he := normal_perfect_blocks_commute (firstInK b) (secondInK b)
    (firstInK_block c b).short (hc.trans inf_le_left)
  have hm := congrArg (Subgroup.map c.K.subtype) he
  rwa [map_commutator, firstInK_map, secondInK_map, Subgroup.map_bot] at hm

end ExchangedCommutation

/-- Distinct actual exchanged blocks with quasisimple two-core quotients commute.
The proof covers every field parameter in `ExchangedBlock`. -/
theorem exchanged_blocks_commute
    (c : ContraryData κ d i j) (b : ExchangedBlock c) :
    ⁅b.first, b.first.map (MulAut.conj b.exchanger).toMonoidHom⁆ = ⊥ :=
  ExchangedCommutation.exchanged_blocks_commute c b

/-- The commutation equation required for the surviving field-four case. -/
theorem fieldFour_exchanged_blocks_commute
    (c : ContraryData κ d i j) (b : ExchangedBlock c) (_hn : b.n = 2) :
    ⁅b.first, b.first.map (MulAut.conj b.exchanger).toMonoidHom⁆ = ⊥ :=
  ExchangedCommutation.exchanged_blocks_commute c b

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
