module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.MultiplicativeNormalizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.Index

/-!
# Conjugate spans in an ambient natural alternating-six module

Let `C` and `W` be subgroups normalized by `I`, with `C ≤ I`. A surjective
alternating-six marking of `C`, intertwined with its literal conjugation on
`W`, identifies `W` with the four-dimensional binary natural module. The
normalizer of that alternating action preserves the natural alternating
form. A Sylow two-subgroup of `C` fixing a point and plane therefore gives
them simultaneous canonical coordinates.

If a subgroup `J ≤ I` centralizes the point and moves the plane, the plane's
`J`-conjugate span lies in the point's perpendicular hyperplane and properly
contains the plane. Its order is consequently eight. Every subgroup and
conjugation in this interface remains in the original ambient group; no
alternating-block identification or whole-core control is assumed.

Source: Aschbacher--Smith, 14.6.10(5), printed p.1029, the natural
four-dimensional case; binary natural-module geometry from B.3.
-/

public noncomputable section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section06.NaturalSixSpan
open Theory.SpecificGroups.SymmetricSix.BinaryFlags NaturalGeometry NaturalPairing
private theorem plane_le_hyperplane : canonicalPlane ≤ PointAction.Hyperplane := by
  intro v hv x hx
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
  have h01 : form (pairVector 4 5) (pairVector 0 1) = 0 := by
    change naturalPairing (Fin 6) (coreToNatural (Fin 6) ⟨Pi.single 4 1 + Pi.single 5 1, by simp [mem_core]; decide⟩) (coreToNatural (Fin 6) ⟨Pi.single 0 1 + Pi.single 1 1, by simp [mem_core]; decide⟩) = 0
    rw [naturalPairing_apply_core]
    decide
  have h23 : form (pairVector 4 5) (pairVector 2 3) = 0 := by
    change naturalPairing (Fin 6) (coreToNatural (Fin 6) ⟨Pi.single 4 1 + Pi.single 5 1, by simp [mem_core]; decide⟩) (coreToNatural (Fin 6) ⟨Pi.single 2 1 + Pi.single 3 1, by simp [mem_core]; decide⟩) = 0
    rw [naturalPairing_apply_core]
    decide
  simp only [map_add,map_smul,LinearMap.smul_apply,h01,h23,smul_zero,zero_add]

variable {G : Type*} [Group G]
theorem form_invariant_of_natural_component
    (I C W : Subgroup G) (hCI : C ≤ I)
    (hIC : I ≤ normalizer (C : Set G)) (hIW : I ≤ normalizer (W : Set G))
    (f : C →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (E : W ≃* Multiplicative (natural (Fin 6)))
    (ha : ∀ (c : C) (w : W) (hw : c.val * w.val * c.val⁻¹ ∈ W),
      (E ⟨c.val * w.val * c.val⁻¹, hw⟩).toAdd =
        naturalRepresentation (Fin 6) (f c).val (E w).toAdd)
    (g : G) (hg : g ∈ I) (v w : W)
    (hv : g * v.val * g⁻¹ ∈ W) (hw : g * w.val * g⁻¹ ∈ W) :
    form (E ⟨g * v.val * g⁻¹, hv⟩).toAdd (E ⟨g * w.val * g⁻¹, hw⟩).toAdd =
      form (E v).toAdd (E w).toAdd := by
  let ρ := W.normalizerMonoidHom.comp (inclusion hIW)
  let σ := (MulAut.congr E).toMonoidHom.comp ρ
  let C' := C.subgroupOf I
  have hact (c : C') : σ c.val = naturalMulAction (Fin 6) (f ⟨c.val.val,c.property⟩).val := by
    ext x : 1
    apply Multiplicative.toAdd.injective
    exact (ha ⟨c.val.val,c.property⟩ (E.symm x)
      (le_normalizer_iff.mp hIW c.val.val c.val.property (E.symm x) (E.symm x).property)).trans
      (congrArg (fun y => naturalRepresentation (Fin 6)
        (f ⟨c.val.val,c.property⟩).val y.toAdd) (E.apply_symm_apply x))
  have hm : C'.map σ = ((naturalMulAction (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype).range := by
    ext x
    constructor
    · rintro ⟨c,hc,rfl⟩
      exact ⟨f ⟨c.val,hc⟩,(hact ⟨c,hc⟩).symm⟩
    · rintro ⟨c,rfl⟩
      obtain ⟨k,rfl⟩ := hf c
      exact ⟨⟨k,hCI k.property⟩,k.property,hact ⟨⟨k,hCI k.property⟩,k.property⟩⟩
  have : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCI).mpr hIC
  have hn : σ ⟨g,hg⟩ ∈ normalizer (C'.map σ : Set (MulAut (Multiplicative (natural (Fin 6))))) := by
    apply C'.le_normalizer_map σ
    exact mem_map_of_mem σ (show (⟨g,hg⟩ : I) ∈ normalizer (C' : Set I) from
      le_normalizer_of_normal (mem_top _))
  rw [hm] at hn
  obtain ⟨t,ht⟩ := Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.exists_permutation_of_normalizes_alternatingMulImage (σ ⟨g,hg⟩) hn
  have he (u : W) (hu : g * u.val * g⁻¹ ∈ W) : (E ⟨g * u.val * g⁻¹,hu⟩).toAdd =
      naturalRepresentation (Fin 6) t (E u).toAdd := by
    have h := congrArg Multiplicative.toAdd (DFunLike.congr_fun ht (E u))
    change _ = (E (ρ ⟨g,hg⟩ (E.symm (E u)))).toAdd at h
    rw [E.symm_apply_apply] at h
    exact h.symm
  rw [he,he]
  exact form_invariant t _ _

theorem conjugate_span_card
    [Finite G] (W : Subgroup G)
    (q : W ≃* Multiplicative (natural (Fin 6)))
    (V Z J : Subgroup G) (hVW : V ≤ W)
    (hplane : (V.subgroupOf W).map q.toMonoidHom =
      canonicalPlane.toAddSubgroup.toSubgroup)
    (hpoint : (Z.subgroupOf W).map q.toMonoidHom =
      canonicalLine.toAddSubgroup.toSubgroup)
    (hJW : J ≤ normalizer (W : Set G))
    (hform : ∀ (j : J) (v w : W)
      (hv : j.val * v.val * j.val⁻¹ ∈ W) (hw : j.val * w.val * j.val⁻¹ ∈ W),
      form (q ⟨j.val * v.val * j.val⁻¹,hv⟩).toAdd
        (q ⟨j.val * w.val * j.val⁻¹,hw⟩).toAdd = form (q v).toAdd (q w).toAdd)
    (hJZ : J ≤ centralizer (Z : Set G))
    (hmove : ¬ J ≤ normalizer (V : Set G)) (hcard : Nat.card V = 4) :
    Nat.card (conjugateSpanBy V J) = 8 := by
  let P : Subgroup W := PointAction.Hyperplane.toAddSubgroup.toSubgroup.comap q.toMonoidHom
  let B : Subgroup G := P.map W.subtype
  have hBW : B ≤ W := map_subtype_le P
  have hmem (w : W) : w.val ∈ B ↔ (q w).toAdd ∈ PointAction.Hyperplane := by
    change w.val ∈ P.map W.subtype ↔ _
    rw [mem_map]
    constructor
    · rintro ⟨u,hu,he⟩
      exact (Subtype.ext he : u=w) ▸ hu
    · intro hw
      exact ⟨w,hw,rfl⟩
  have hVB : V ≤ B := by
    intro v hv
    apply (hmem ⟨v,hVW hv⟩).mpr
    apply plane_le_hyperplane
    have hh := mem_map_of_mem q.toMonoidHom (show (⟨v,hVW hv⟩ : W) ∈ V.subgroupOf W from hv)
    change q ⟨v,hVW hv⟩ ∈ (V.subgroupOf W).map q.toMonoidHom at hh
    rw [hplane] at hh
    exact hh
  obtain ⟨z,hzZ,hzq⟩ : ∃ z : W, z.val ∈ Z ∧ (q z).toAdd = pairVector 4 5 := by
    have hh : Multiplicative.ofAdd (pairVector 4 5) ∈
        (Z.subgroupOf W).map q.toMonoidHom := by
      rw [hpoint]
      change pairVector 4 5 ∈ canonicalLine
      exact Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨z,hz,he⟩ := hh
    exact ⟨z,hz,congrArg Multiplicative.toAdd he⟩
  have hJB : J ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro j hj v hv
    have hvW := hBW hv
    have hv' := le_normalizer_iff.mp hJW j hj v hvW
    apply (hmem ⟨j*v*j⁻¹,hv'⟩).mpr
    intro x hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hzfixed : j*z.val*j⁻¹ = z.val := by
      have hc := hJZ hj z hzZ
      exact mul_inv_eq_iff_eq_mul.mpr hc.symm
    have hzW : j*z.val*j⁻¹ ∈ W := hzfixed.symm ▸ z.property
    have he := hform ⟨j,hj⟩ z ⟨v,hvW⟩ hzW hv'
    change form (q ⟨j*z.val*j⁻¹,hzW⟩).toAdd
      (q ⟨j*v*j⁻¹,hv'⟩).toAdd = form (q z).toAdd (q ⟨v,hvW⟩).toAdd at he
    have hez : (⟨j*z.val*j⁻¹,hzW⟩ : W) = z := Subtype.ext hzfixed
    rw [hez] at he
    have hzv : form (q z).toAdd (q ⟨v,hvW⟩).toAdd = 0 := by
      rw [hzq]
      exact (hmem ⟨v,hvW⟩).mp hv _ (Submodule.subset_span (Set.mem_singleton _))
    change form (c • pairVector 4 5) (q ⟨j*v*j⁻¹,hv'⟩).toAdd = 0
    rw [map_smul,LinearMap.smul_apply,←hzq,he,hzv,smul_zero]
  have hspanB : conjugateSpanBy V J ≤ B := conjugateSpanBy_le hVB hJB
  have hBcard : Nat.card B = 8 := by
    have heP : Nat.card P = Nat.card (Multiplicative PointAction.Hyperplane) := by
      let f : P ≃ Multiplicative PointAction.Hyperplane := {
        toFun p := Multiplicative.ofAdd ⟨(q p.val).toAdd,p.property⟩
        invFun x := ⟨q.symm (Multiplicative.ofAdd x.toAdd.val), by
          change (q (q.symm (Multiplicative.ofAdd x.toAdd.val))).toAdd ∈ PointAction.Hyperplane
          rw [q.apply_symm_apply]
          exact x.toAdd.property⟩
        left_inv p := by apply Subtype.ext; exact q.symm_apply_apply p.val
        right_inv x := by
          apply Multiplicative.toAdd.injective
          apply Subtype.ext
          exact congrArg Multiplicative.toAdd (q.apply_symm_apply _) }
      exact Nat.card_congr f
    have heB : Nat.card B = Nat.card P :=
      (Nat.card_congr (P.equivMapOfInjective W.subtype W.subtype_injective).toEquiv).symm
    exact heB.trans (heP.trans PointAction.hyperplane_card)
  have hlo : 4 < Nat.card (conjugateSpanBy V J) := by
    apply lt_of_not_ge
    intro hc
    have he : V = conjugateSpanBy V J :=
      eq_of_le_of_card_ge (le_conjugateSpanBy V J) (by simpa [hcard] using hc)
    exact hmove (he ▸ le_normalizer_conjugateSpanBy V J)
  have hd : Nat.card (conjugateSpanBy V J) ∣ 8 :=
    hBcard ▸ card_dvd_of_le hspanB
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (conjugateSpanBy V J) ∣ 2 ^ 3 from hd)
  interval_cases k <;> norm_num only [pow_zero,pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl] at he <;> omega


variable [Finite G]
private def imageSpace (W : Subgroup G) (q : W ≃* Multiplicative (natural (Fin 6))) (B : Subgroup G) :
    Submodule (ZMod 2) (natural (Fin 6)) :=
  AddSubgroup.toZModSubmodule 2
    ((B.subgroupOf W).map q.toMonoidHom).toAddSubgroup'

omit [Finite G] in
private theorem imageSpace_card (W : Subgroup G) (q : W ≃* Multiplicative (natural (Fin 6))) (B : Subgroup G) (hB : B ≤ W) :
    Nat.card (imageSpace W q B) = Nat.card B := by
  let E := (B.subgroupOf W).map q.toMonoidHom
  have he : Nat.card (imageSpace W q B) = Nat.card E := by
    exact Nat.card_congr {
      toFun v := ⟨Multiplicative.ofAdd v.val,v.property⟩
      invFun v := ⟨v.val.toAdd,v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact he.trans ((card_map_of_injective q.injective).trans
    (Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv))

omit [Finite G] in
private theorem imageSpace_invariant (C W : Subgroup G)
    (hCW : C ≤ normalizer (W : Set G))
    (f : C →* alternatingGroup (Fin 6))
    (q : W ≃* Multiplicative (natural (Fin 6)))
    (ha : ∀ (c : C) (w : W) (hw : c.val * w.val * c.val⁻¹ ∈ W),
      (q ⟨c.val * w.val * c.val⁻¹,hw⟩).toAdd =
        naturalRepresentation (Fin 6) (f c).val (q w).toAdd)
    (B : Subgroup G) (S : Sylow 2 C) (hSB : (S : Subgroup C).map C.subtype ≤ normalizer (B : Set G)) :
    ∀ x ∈ ((S : Subgroup C).map
      f).map
        (alternatingGroup (Fin 6)).subtype,
      move x (imageSpace W q B) = imageSpace W q B := by
  have hi : ∀ k ∈ (S : Subgroup C), ∀ v ∈ imageSpace W q B,
      naturalRepresentation (Fin 6)
        (f k).val v ∈ imageSpace W q B := by
    intro k hk v hv
    change Multiplicative.ofAdd v ∈ (B.subgroupOf W).map
      q.toMonoidHom at hv
    obtain ⟨w,hw,he⟩ := hv
    have hw' : (k : G) * w.val * (k : G)⁻¹ ∈ W :=
      le_normalizer_iff.mp hCW k k.property w w.property
    refine ⟨⟨(k : G) * w.val * (k : G)⁻¹,hw'⟩,
      le_normalizer_iff.mp hSB k (mem_map_of_mem _ hk) w hw,?_⟩
    apply Multiplicative.toAdd.injective
    exact (ha k w hw').trans (congrArg (naturalRepresentation (Fin 6) (f k).val)
      (congrArg Multiplicative.toAdd he))
  rintro _ ⟨a,⟨k,hk,rfl⟩,rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq ?_ (move_finrank _ _)
  rintro _ ⟨v,hv,rfl⟩
  exact hi k hk v hv


omit [Finite G] in
private theorem imageSpace_relabel (W : Subgroup G)
    (q : W ≃* Multiplicative (natural (Fin 6))) (B : Subgroup G)
    (a : alternatingGroup (Fin 6)) :
    imageSpace W (q.trans (naturalMulAction (Fin 6) a.val)) B =
      move a.val (imageSpace W q B) := by
  apply le_antisymm
  · rintro v ⟨w,hw,he⟩
    refine ⟨(q w).toAdd,⟨w,hw,rfl⟩,?_⟩
    exact congrArg Multiplicative.toAdd he
  · rintro v ⟨w,⟨u,hu,he⟩,rfl⟩
    refine ⟨u,hu,?_⟩
    exact congrArg (naturalMulAction (Fin 6) a.val) he

theorem exists_flag_coordinates (I C W : Subgroup G) (hCI : C ≤ I)
    (hIC : I ≤ normalizer (C : Set G)) (hIW : I ≤ normalizer (W : Set G))
    (f : C →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (q : W ≃* Multiplicative (natural (Fin 6)))
    (ha : ∀ (c : C) (w : W) (hw : c.val * w.val * c.val⁻¹ ∈ W),
      (q ⟨c.val * w.val * c.val⁻¹,hw⟩).toAdd =
        naturalRepresentation (Fin 6) (f c).val (q w).toAdd)
    (B Z : Subgroup G) (hB : B ≤ W) (hZ : Z ≤ W)
    (hBc : Nat.card B = 4) (hZc : Nat.card Z = 2)
    (S : Sylow 2 C)
    (hSB : (S : Subgroup C).map C.subtype ≤ normalizer (B : Set G))
    (hSZ : (S : Subgroup C).map C.subtype ≤ normalizer (Z : Set G)) :
    ∃ q' : W ≃* Multiplicative (natural (Fin 6)),
      (B.subgroupOf W).map q'.toMonoidHom = canonicalPlane.toAddSubgroup.toSubgroup ∧
      (Z.subgroupOf W).map q'.toMonoidHom = canonicalLine.toAddSubgroup.toSubgroup ∧
      ∀ (g : G) (_hg : g ∈ I) (v w : W)
        (hv : g * v.val * g⁻¹ ∈ W) (hw : g * w.val * g⁻¹ ∈ W),
        form (q' ⟨g * v.val * g⁻¹,hv⟩).toAdd
          (q' ⟨g * w.val * g⁻¹,hw⟩).toAdd = form (q' v).toAdd (q' w).toAdd := by
  let S' := S.mapSurjective (f := f) hf
  have hd (E : Subgroup G) (hE : E ≤ W) (n : ℕ)
      (hc : Nat.card E = 2 ^ n) : Module.finrank (ZMod 2) (imageSpace W q E) = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := imageSpace W q E)
    rw [Nat.card_zmod] at he
    exact he.symm.trans ((imageSpace_card W q E hE).trans hc)
  obtain ⟨a,haZ,haB⟩ := sylow_flag_of_between (alternatingGroup (Fin 6)) le_rfl S'
    (imageSpace W q Z) (imageSpace W q B)
    (hd Z hZ 1 hZc) (hd B hB 2 hBc)
    (imageSpace_invariant C W (hCI.trans hIW) f q ha Z S hSZ)
    (imageSpace_invariant C W (hCI.trans hIW) f q ha B S hSB)
  let q' := q.trans (naturalMulAction (Fin 6) a.val⁻¹)
  refine ⟨q',?_,?_,?_⟩
  · have he : imageSpace W q' B = canonicalPlane := by
      rw [show q' = q.trans (naturalMulAction (Fin 6) (a⁻¹).val) from rfl,
        imageSpace_relabel,haB]
      exact move_inv a.val canonicalPlane
    exact congrArg (fun U : Submodule (ZMod 2) (natural (Fin 6)) =>
      U.toAddSubgroup.toSubgroup) he
  · have he : imageSpace W q' Z = canonicalLine := by
      rw [show q' = q.trans (naturalMulAction (Fin 6) (a⁻¹).val) from rfl,
        imageSpace_relabel,haZ]
      exact move_inv a.val canonicalLine
    exact congrArg (fun U : Submodule (ZMod 2) (natural (Fin 6)) =>
      U.toAddSubgroup.toSubgroup) he
  · intro g hg v w hv hw
    change form (naturalRepresentation (Fin 6) a.val⁻¹ (q ⟨g * v.val * g⁻¹,hv⟩).toAdd)
      (naturalRepresentation (Fin 6) a.val⁻¹ (q ⟨g * w.val * g⁻¹,hw⟩).toAdd) =
        form (naturalRepresentation (Fin 6) a.val⁻¹ (q v).toAdd)
          (naturalRepresentation (Fin 6) a.val⁻¹ (q w).toAdd)
    rw [form_invariant,form_invariant]
    exact form_invariant_of_natural_component I C W hCI hIC hIW f hf q ha g hg v w hv hw

theorem span_card_of_natural_component
    (I C W : Subgroup G) (hCI : C ≤ I)
    (hIC : I ≤ normalizer (C : Set G)) (hIW : I ≤ normalizer (W : Set G))
    (f : C →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (q : W ≃* Multiplicative (natural (Fin 6)))
    (ha : ∀ (c : C) (w : W) (hw : c.val * w.val * c.val⁻¹ ∈ W),
      (q ⟨c.val * w.val * c.val⁻¹,hw⟩).toAdd =
        naturalRepresentation (Fin 6) (f c).val (q w).toAdd)
    (V Z J : Subgroup G) (hJI : J ≤ I) (hV : V ≤ W) (hZ : Z ≤ W)
    (hVc : Nat.card V = 4) (hZc : Nat.card Z = 2)
    (S : Sylow 2 C)
    (hSV : (S : Subgroup C).map C.subtype ≤ normalizer (V : Set G))
    (hSZ : (S : Subgroup C).map C.subtype ≤ normalizer (Z : Set G))
    (hJZ : J ≤ centralizer (Z : Set G)) (hmove : ¬ J ≤ normalizer (V : Set G)) :
    Nat.card (conjugateSpanBy V J) = 8 := by
  obtain ⟨q',hp,hz,hform⟩ := exists_flag_coordinates I C W hCI hIC hIW f hf q ha V Z hV hZ hVc hZc S hSV hSZ
  exact conjugate_span_card W q' V Z J hV hp hz (hJI.trans hIW)
    (fun j => hform j.val (hJI j.property)) hJZ hmove hVc

end CFSG.Quasithin.Chapter14.Section06.NaturalSixSpan
