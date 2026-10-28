module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.CoreGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.Intrinsic
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic

/-!
# Recognizing the ordinary block from its actual moved module

The core bound identifies the literal W_K with U(K)=[O₂(K),K]. The A₅
marking on that module then proves every short-group clause and provides
coordinates on the actual block quotient U(K)/C_U(K). In particular the
core can have a central attachment; it is not assumed to equal U(K).

This is the conditional recognition step in the last paragraph of 13.3.14.
The source module sieve and Baumann chief budget remain separate inputs.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlockRecognition
open ChapterC
variable {X : Type*} [Group X]
variable (eQ : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (eV : blockU X ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (x : X) (v : blockU X),
      (eV (blockConjugate X x v)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 X) x)) (eV v).toAdd)

private abbrev naturalEquiv : blockU X ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  eV.trans (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative

include eV he

private theorem natural_equivariant (x : X) (v : blockU X) :
    (naturalEquiv eV (blockConjugate X x v)).toAdd =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
        (eQ (QuotientGroup.mk' (pCore 2 X) x)) (naturalEquiv eV v).toAdd := by
  change BinaryPermutation.coreEquivNatural (Fin 5) (by decide) (eV (blockConjugate X x v)).toAdd = _
  rw [he]
  exact BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) _ _

/-- Faithfulness of the marked five-letter module detects the intrinsic two-core. -/
private theorem layer_centralizer_le_core : centralizer (blockU X : Set X) ≤ pCore 2 X := by
  intro x hx
  have ha : eQ (QuotientGroup.mk' (pCore 2 X) x) = 1 := by
    apply Subtype.ext
    apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := (naturalEquiv eV).surjective (Multiplicative.ofAdd v)
    have hc : blockConjugate X x w = w := by
      apply Subtype.ext
      change x * (w : X) * x⁻¹ = w
      rw [← hx w w.property, mul_inv_cancel_right]
    have hh := natural_equivariant eQ eV he x w
    rw [hc,hw] at hh
    change v = BinaryPermutation.naturalRepresentation (Fin 5)
      (eQ (QuotientGroup.mk' (pCore 2 X) x)).val v at hh
    simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hh.symm
  have hq : QuotientGroup.mk' (pCore 2 X) x = 1 := eQ.injective (ha.trans eQ.map_one.symm)
  exact (QuotientGroup.eq_one_iff x).mp hq

omit he eQ in
/-- The marked commutator layer is intrinsically elementary abelian. -/
private theorem layer_elementary : IsElementaryAbelian 2 (blockU X) := by
  have hm : IsElementaryAbelian 2 (Multiplicative (BinaryPermutation.core (Fin 5))) := {
    is_comm := ⟨mul_comm⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v => by
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      apply Subtype.ext
      ext i
      exact CharTwo.add_self_eq_zero _) }
  let := hm
  exact IsElementaryAbelian.of_injective eV.toMonoidHom eV.injective

/-- Normal subgroups inside the marked layer are trivial or the full layer. -/
private theorem invariant_layer (N : Subgroup X) (hn : N.Normal) (hN : N ≤ blockU X) :
    N = ⊥ ∨ N = blockU X := by
  let e := naturalEquiv eV
  let S : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 5)) := {
    carrier := {v | (e.symm (Multiplicative.ofAdd v)).val ∈ N}
    zero_mem' := by change (e.symm 1).val ∈ N; rw [map_one]; exact N.one_mem
    add_mem' := by
      intro v w hv hw
      change (e.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w)).val ∈ N
      rw [map_mul]
      exact N.mul_mem hv hw
    smul_mem' := by
      intro c v hv
      fin_cases c
      · change (e.symm (Multiplicative.ofAdd ((0 : ZMod 2) • v))).val ∈ N
        rw [zero_smul]
        change (e.symm 1).val ∈ N
        rw [map_one]; exact N.one_mem
      · change (e.symm (Multiplicative.ofAdd ((1 : ZMod 2) • v))).val ∈ N
        rw [one_smul]
        exact hv }
  let W : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)) :=
    ⟨S, by
      intro a v hv
      obtain ⟨z,hz⟩ := eQ.surjective a
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
      let u := e.symm (Multiplicative.ofAdd v)
      have heq : e.symm (Multiplicative.ofAdd
          (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) a v)) =
          blockConjugate X x u := by
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [MulEquiv.apply_symm_apply]
        have hh := natural_equivariant eQ eV he x u
        change _ = BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 X) x)) (e (e.symm (Multiplicative.ofAdd v))).toAdd at hh
        rw [hz,MulEquiv.apply_symm_apply] at hh
        exact hh.symm
      change (e.symm (Multiplicative.ofAdd _)).val ∈ N
      rw [heq]
      exact hn.conj_mem _ hv x⟩
  let : IsIrreducible (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)) :=
    BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  rcases eq_bot_or_eq_top W with hb | ht
  · left
    apply bot_unique
    intro x hx
    let u : blockU X := ⟨x,hN hx⟩
    have hv : (e u).toAdd ∈ W := by
      change (e.symm (Multiplicative.ofAdd (e u).toAdd)).val ∈ N
      simpa using hx
    rw [hb] at hv
    have he1 : e u = e 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective hv
    exact congrArg Subtype.val (e.injective he1)
  · right
    apply le_antisymm hN
    intro x hx
    let u : blockU X := ⟨x,hx⟩
    have hv : (e u).toAdd ∈ W := ht ▸ Submodule.mem_top
    change (e.symm (Multiplicative.ofAdd (e u).toAdd)).val ∈ N at hv
    simpa using hv


private theorem layer_fixed_eq_bot : blockU X ⊓ center X = ⊥ := by
  rcases invariant_layer eQ eV he (blockU X ⊓ center X) inferInstance inf_le_left with hb | ht
  · exact hb
  have hc : blockU X ≤ center X := ht.symm ▸ inf_le_right
  have htop : (⊤ : Subgroup X) ≤ pCore 2 X :=
    (by rw [centralizer_center] : (⊤ : Subgroup X) ≤ centralizer (center X : Set X)).trans
      ((centralizer_le hc).trans (layer_centralizer_le_core eQ eV he))
  have hall (a : alternatingGroup (Fin 5)) : a = 1 := by
    obtain ⟨z,rfl⟩ := eQ.surjective a
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
    have hx : QuotientGroup.mk' (pCore 2 X) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (htop (mem_top x))
    rw [hx,map_one]
  obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  exact (ha (hall a)).elim

private theorem fixed_eq_bot : blockFixed X = ⊥ := by
  apply map_injective (blockU X).subtype_injective
  rw [blockFixed_map,layer_fixed_eq_bot eQ eV he,Subgroup.map_bot]

private theorem short [Finite X] (hperfect : IsPPerfect 2 X)
    (hfit : generalizedFitting X = pCore 2 X) : IsShort X := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hne : blockU X ≠ ⊥ := by
    let : Nontrivial (BinaryPermutation.core (Fin 5)) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (by
        rw [BinaryPermutation.finrank_core]; decide)
    let : Nontrivial (blockU X) := eV.toEquiv.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  refine {
    finite := inferInstance
    twoPerfect := hperfect
    fitting := hfit
    elementary := layer_elementary eV
    central := ?_
    quotient := Or.inl (IsQuasisimple.of_mulEquiv eQ.symm)
    irreducible := ?_ }
  · intro u hu x hx
    have hq : eQ (QuotientGroup.mk' (pCore 2 X) x) = 1 := by
      have hxq : QuotientGroup.mk' (pCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      rw [hxq,map_one]
    have hh := he x ⟨u,hu⟩
    rw [hq,map_one,Module.End.one_apply] at hh
    have heq := congrArg Subtype.val (eV.injective (Multiplicative.toAdd.injective hh))
    exact mul_inv_eq_iff_eq_mul.mp heq
  · rw [BlockModuleIrreducible,layer_fixed_eq_bot eQ eV he]
    exact ⟨bot_lt_iff_ne_bot.mpr hne,fun N hn _ hN => invariant_layer eQ eV he N hn hN⟩

private def moduleIso : BlockModule X ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
  (((QuotientGroup.quotientMulEquivOfEq (fixed_eq_bot eQ eV he)).trans
    QuotientGroup.quotientBot).trans (naturalEquiv eV))

private theorem moduleIso_mk (u : blockU X) :
    moduleIso eQ eV he (QuotientGroup.mk' (blockFixed X) u) = naturalEquiv eV u := rfl

/-- A marked intrinsic commutator layer, including its original action, constructs
an A₅ block even when the full two-core has an additional central factor. -/
theorem alternatingBlock_of_layer [Finite X] (hperfect : IsPPerfect 2 X)
    (hfit : generalizedFitting X = pCore 2 X) : IsAlternatingBlock X 5 := by
  refine ⟨by decide,short eQ eV he hperfect hfit,
    (BinaryPermutation.naturalMulAction (Fin 5)).comp (alternatingGroup (Fin 5)).subtype,
    ⟨{ quotientIso := eQ, moduleIso := moduleIso eQ eV he, intertwining := ?_ }⟩,
    fun _ _ => rfl⟩
  intro x v
  apply Multiplicative.toAdd.injective
  rw [moduleIso_mk,moduleIso_mk]
  exact natural_equivariant eQ eV he x v

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlockRecognition

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterC
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

/-- Recognize the actual selected block from its identified intrinsic layer
and the genuine conjugation model of the same ambient moved module. -/
theorem ordinary_alternatingBlock_of_moved_model
    (B A T : Subgroup G) (hp : IsPPerfect 2 B)
    (hfit : generalizedFitting B = pCore 2 B)
    (heq : (blockU B).map B.subtype = Diagonal.movedModule B A T)
    (hm : Chapter6.Source.IsConjugationModel B (Diagonal.movedModule B A T)
      Chapter6.Source.a5Module) : IsAlternatingBlock B 5 := by
  obtain ⟨eQ,f,hf⟩ := hm
  let W := Diagonal.movedModule B A T
  let c : blockU B ≃* W :=
    ((blockU B).equivMapOfInjective B.subtype B.subtype_injective).trans
      (MulEquiv.subgroupCongr heq)
  let n := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let eV : blockU B ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    (c.trans f).trans n.symm.toAddEquiv.toMultiplicative
  have hnat (b : B) (v : blockU B) :
      (f (c (blockConjugate B b v))).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 B) b)) (f (c v)).toAdd := by
    have hh := hf b (c v)
    have he : f.symm (Multiplicative.ofAdd
        (Chapter6.Source.a5Module (eQ (QuotientGroup.mk' (pCore 2 B) b))
          (f (c v)).toAdd)) = c (blockConjugate B b v) := Subtype.ext hh
    have hh' := congrArg f he
    rw [MulEquiv.apply_symm_apply] at hh'
    exact (congrArg Multiplicative.toAdd hh').symm
  apply OrdinaryBlockRecognition.alternatingBlock_of_layer eQ eV ?_ hp hfit
  intro b v
  apply n.injective
  change n (n.symm (f (c (blockConjugate B b v))).toAdd) = _
  have ht : n (BinaryPermutation.alternatingCoreRepresentation (Fin 5)
      (eQ (QuotientGroup.mk' (pCore 2 B) b)) (eV v).toAdd) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
        (eQ (QuotientGroup.mk' (pCore 2 B) b)) (n (eV v).toAdd) :=
    BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) _ _
  rw [n.apply_symm_apply,ht]
  change (f (c (blockConjugate B b v))).toAdd =
    BinaryPermutation.alternatingNaturalRepresentation (Fin 5)
      (eQ (QuotientGroup.mk' (pCore 2 B) b)) (n (n.symm (f (c v)).toAdd))
  rw [n.apply_symm_apply]
  exact hnat b v

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
