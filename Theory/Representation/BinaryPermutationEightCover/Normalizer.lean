module
public import Theory.SpecificGroups.AlternatingEight.ReducedCover
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Representation.BinaryPermutationEightCover.TranslationCore
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Lifting the code transvections to the original subgroup normalizer

A surjection from K to A₈ has two-group kernel when K/O₂(K) is
quasisimple: the reduced-cover theorem excludes the residual Schur
kernel. A full augmentation marking identifies N_K(V) with the preimage
of the code stabilizer. Lifting its two-core through that surjection
produces an element of O₂(N_K(V)) moving V.

All normalizers and centralizers in the conclusion are the original
ambient subgroups. The source application supplies the four-dimensional
code properties from the central-line residual's transitivity.
Source: Aschbacher–Smith, Lemma 12.3.3, printed p.808; GLS III 5.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace AlternatingEight
variable {K : Type*} [Group K] [Finite K] [IsQuasisimple (K ⧸ pCore 2 K)]

theorem quotient_cover_kernel_isTwoGroup
    (π : K →* alternatingGroup (Fin 8)) (hπ : Function.Surjective π) :
    IsPGroup 2 π.ker := by
  let A := alternatingGroup (Fin 8)
  let N := (pCore 2 K).map π
  let : N.Normal := Subgroup.Normal.map inferInstance π hπ
  have hn : N = ⊥ := by
    apply (alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 8))).resolve_right
    intro he
    have hp : IsPGroup 2 N := pCore_isPGroup.map π
    have hpA : IsPGroup 2 A := hp.of_equiv ((MulEquiv.subgroupCongr he).trans topEquiv)
    let : Group.IsNilpotent A := hpA.isNilpotent
    let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable A inferInstance
  have hk : pCore 2 K ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp hn
  let q := QuotientGroup.lift (pCore 2 K) π hk
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨k,rfl⟩ := hπ a
    exact ⟨QuotientGroup.mk' _ k,rfl⟩
  have hi := reduced_cover_injective q hq (pCore_quotient_pCore_eq_bot 2)
  have he : π.ker = pCore 2 K := by
    apply le_antisymm _ hk
    intro k h
    apply (QuotientGroup.eq_one_iff k).mp
    apply hi
    exact (show q (QuotientGroup.mk' _ k) = 1 from h).trans q.map_one.symm
  rw [he]
  exact pCore_isPGroup
end AlternatingEight

namespace BinaryPermutation.EightCore
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]

theorem normalizer_core_not_centralizes
    (K V W : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : V ≤ W) (hKW : K ≤ normalizer (W : Set G))
    (π : K →* alternatingGroup (Fin 8)) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (E : W ≃* Multiplicative (core (Fin 8)))
    (ha : ∀ (k : K) (v w : W), (w : G) = (k : G) * (v : G) * (k : G)⁻¹ →
      (E w).toAdd = alternatingCoreRepresentation (Fin 8) (π k) (E v).toAdd)
    (hd : let f := (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
      Module.finrank (ZMod 2) f.range = 4)
    (hone : let f := (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
      oneWord ∈ f.range)
    (hw : let f := (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
      ∀ v ∈ f.range, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4) :
    ¬ (K ⊓ normalizer (V : Set G)).pCoreIn 2 ≤ centralizer (V : Set G) := by
  let f := (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
  let U := f.range
  let B := subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U
  let N := K ⊓ normalizer (V : Set G)
  have hm (w : W) : (E w).toAdd ∈ U ↔ (w : G) ∈ V := by
    constructor
    · rintro ⟨v,hv⟩
      have he : inclusion hV v.toMul = w := E.injective (congrArg Multiplicative.ofAdd hv)
      exact (congrArg Subtype.val he) ▸ v.toMul.property
    · intro hv
      exact ⟨Additive.ofMul ⟨w,hv⟩,rfl⟩
  let cw (k : K) (w : W) : W := ⟨(k : G) * w * (k : G)⁻¹,
    (mem_normalizer_iff.mp (hKW k.property) w).mp w.property⟩
  have hcw (k : K) (w : W) :
      alternatingCoreRepresentation (Fin 8) (π k) (E w).toAdd = (E (cw k w)).toAdd :=
    (ha k w (cw k w) rfl).symm
  have hmem (k : K) : π k ∈ B ↔ (k : G) ∈ normalizer (V : Set G) := by
    constructor
    · intro hk
      apply mem_normalizer_iff.mpr
      intro x
      constructor
      · intro hx
        let w : W := ⟨x,hV hx⟩
        apply (hm (cw k w)).mp
        rw [← hcw]
        exact (hk (E w).toAdd).mpr ((hm w).mpr hx)
      · intro hx
        have hxW : x ∈ W := (mem_normalizer_iff.mp (hKW k.property) x).mpr (hV hx)
        let w : W := ⟨x,hxW⟩
        apply (hm w).mp
        apply (hk (E w).toAdd).mp
        rw [hcw]
        exact (hm (cw k w)).mpr hx
    · intro hk v
      obtain ⟨w,hw⟩ := E.surjective (Multiplicative.ofAdd v)
      have he : (E w).toAdd = v := congrArg Multiplicative.toAdd hw
      rw [← he,hcw,hm,hm]
      exact (mem_normalizer_iff.mp hk w).symm
  let q : N →* B := (π.comp (inclusion (show N ≤ K from inf_le_left))).codRestrict B
    (fun n => (hmem ⟨n,n.property.1⟩).mpr n.property.2)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨k,hk⟩ := hπ b.val
    have hn : (k : G) ∈ N := ⟨k.property,(hmem k).mp (hk ▸ b.property)⟩
    exact ⟨⟨k,hn⟩,Subtype.ext hk⟩
  have hkq : IsPGroup 2 q.ker := by
    let j : q.ker →* π.ker :=
      { toFun := fun x => ⟨⟨x.val,x.val.property.1⟩,congrArg Subtype.val x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hker.of_injective j (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun a : π.ker => ((a : K) : G)) h)))
  obtain ⟨g,hg,v,hmove⟩ := code_twoCore_moves U hd hone hw
  obtain ⟨n,hn⟩ := hq g
  have hncore : n ∈ pCore 2 N := by
    rw [← q.comap_pCore_of_ker_isPGroup hq hkq]
    change q n ∈ pCore 2 B
    rwa [hn]
  intro hc
  have hnc : (n : G) ∈ centralizer (V : Set G) := hc (mem_map_of_mem N.subtype hncore)
  obtain ⟨w,hwv⟩ := v.property
  let w' : W := inclusion hV w.toMul
  have hfixed : cw ⟨n,n.property.1⟩ w' = w' := by
    apply Subtype.ext
    change (n : G) * (w.toMul : G) * (n : G)⁻¹ = (w.toMul : G)
    rw [← hnc w.toMul w.toMul.property,mul_inv_cancel_right]
  apply hmove
  have he : (E w').toAdd = v.val := hwv
  rw [← he]
  have hng : π ⟨n,n.property.1⟩ = g.val := congrArg Subtype.val hn
  rw [← hng,hcw,hfixed]

end BinaryPermutation.EightCore
