module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityResidualFixed

/-!
# Common centralizers at the original G and T

The common-centralizer argument uses the structural input only to normalize
the chosen V by the original T. Specialize its necessary kernel, Sylow and
Thompson steps, reusing the proved literal block and cohomology calculations.

These are additive specializations of the corresponding rigidity modules;
public results independent of the universal inputs are reused directly.
Source: Aschbacher–Smith, original 12.2.25–26, printed pp.804–806
(PDF pp.821–823), with 12.2.2(3) and A.3.12 for containing components.
-/

public noncomputable section

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {d : ℕ} {H P U : Subgroup G}
namespace CyclicLocalAnalysis
variable (C : CyclicLocalAnalysis T L V d H P U)
include C

end CyclicLocalAnalysis

/-- Application to the original source choice: the first direct product
in the displayed equality (*) on printed p.805. -/
theorem chosen_centralizer_core_directProduct_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ e : U × ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (U : Set G)),
      ∀ u c, (e (u, c) : G) = (u : G) * (c : G) :=
  C.sylow_centralizer_core_directProduct (by have := A.dimension.1; omega)
    (((structural L h).2.2 V D).1) D.le_sylow hnone

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- The centralizer of UV in the Sylow subgroup splits over the original
intersection U∩V. This is the second equality in the opening paragraph. -/
theorem join_centralizer_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) =
      (U ⊓ V) ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hEU : E ≤ centralizer (U : Set G) := inf_le_right.trans
    (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left))
  have hEV : E ≤ centralizer (V : Set G) := inf_le_right.trans
    (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right))
  have he : (T : Subgroup G) ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) =
      ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓ centralizer (V : Set G) := by
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans
        (centralizer_le (show U ≤ U ⊔ V from le_sup_left))))
        (inf_le_right.trans (centralizer_le (show V ≤ U ⊔ V from le_sup_right)))
    · exact le_inf (inf_le_left.trans inf_le_left) (le_centralizer_iff.mp
        (sup_le (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
          (le_centralizer_iff.mp inf_le_right)))
  rw [he, C.sylow_centralizer_core_decomposition
    (by have := A.dimension.1; omega) (((structural L h).2.2 V D).1) D.le_sylow hnone]
  rw [sup_comm U E, inf_centralizer_sup_of_centralizing E U V
    (hEU.trans (Subgroup.centralizer_le_normalizer _)) hEV, C.action_kernel, sup_comm]

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

omit [Finite G] in
private theorem index_two_generation_at {W V K : Subgroup G}
    (hi : W.relIndex V = 2) {v : G} (hv : v ∈ V) (hvW : v ∉ W)
    (hWK : W ≤ K) (hvK : v ∈ K) : V ≤ K := by
  intro x hx
  by_cases hxW : x ∈ W
  · exact hWK hxW
  have hw : v⁻¹ * x ∈ W :=
    ((W.subgroupOf V).mul_mem_iff_of_index_two hi
      (a := ⟨v⁻¹,V.inv_mem hv⟩) (b := ⟨x,hx⟩)).mpr
      (by simpa only [mem_subgroupOf, inv_mem_iff] using iff_of_false hvW hxW)
  simpa only [mul_inv_cancel_left] using K.mul_mem hvK (hWK hw)

omit [Finite G] in
private theorem hyperplane_index_at
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, C.hyperplane, chosen_card A] at hh
  have hd : d = d - 1 + 1 := by have := A.dimension.1; omega
  have hc : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hd
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hc] at hh
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
  nlinarith

/-- The pointwise hyperplane centralizer is the original transvection group
times the original action kernel, before either dimensional splitting. -/
theorem hyperplane_centralizer_eq_core_sup_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
  let := C.elementary
  let W := U ⊓ V
  have hTV := ((structural L h).2.2 V D).1
  obtain ⟨v,hv,hvU,_⟩ := C.inverted
  have hvW : v ∉ W := fun hvW => hvU hvW.1
  apply le_antisymm
  · intro t ht
    have htvV : t * v * t⁻¹ ∈ V := (mem_normalizer_iff.mp (hTV ht.1) v).mp hv
    have htvW : t * v * t⁻¹ ∉ W := by
      intro hw
      have hc := ht.2 _ hw
      have he : t * v * t⁻¹ = v := by
        apply (mul_left_cancel (a := t))
        simpa only [mul_inv_cancel_right, inv_mul_cancel_right] using hc.symm
      exact hvW (he ▸ hw)
    have hw : ⁅t,v⁆ ∈ W :=
      ((W.subgroupOf V).mul_mem_iff_of_index_two (hyperplane_index_at A C)
        (a := ⟨t*v*t⁻¹,htvV⟩) (b := ⟨v⁻¹,V.inv_mem hv⟩)).mpr
        (by simpa only [mem_subgroupOf, inv_mem_iff] using iff_of_false htvW hvW)
    obtain ⟨u,hu,he⟩ := hyperplane_displacement_surjective A C hv hvW _ hw
    have hcv : v * (u⁻¹*t) = (u⁻¹*t) * v := by
      have hc : u * v * u⁻¹ = t * v * t⁻¹ :=
        mul_right_cancel (show (u*v*u⁻¹)*v⁻¹ = (t*v*t⁻¹)*v⁻¹ from he)
      calc
        v * (u⁻¹*t) = u⁻¹ * (u*v*u⁻¹) * t := by group
        _ = u⁻¹ * (t*v*t⁻¹) * t := by rw [hc]
        _ = (u⁻¹*t)*v := by group
    have hcW : u⁻¹*t ∈ centralizer (W : Set G) :=
      (centralizer (W : Set G)).mul_mem
        ((centralizer _).inv_mem (centralizer_le (show W ≤ U from inf_le_left) (le_centralizer U hu))) ht.2
    have hcV : u⁻¹*t ∈ centralizer (V : Set G) := by
      intro x hx
      have hgen := index_two_generation_at (hyperplane_index_at A C) hv hvW
        (K := centralizer ({u⁻¹*t} : Set G))
        (fun w hw => mem_centralizer_singleton_iff.mpr (hcW w hw))
        (mem_centralizer_singleton_iff.mpr hcv)
      exact mem_centralizer_singleton_iff.mp (hgen hx)
    have hm := mul_mem_sup hu (show u⁻¹*t ∈ (T : Subgroup G) ⊓ centralizer (V : Set G) from
      ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (C.core_le_sylow hu)) ht.1,hcV⟩)
    simpa only [mul_inv_cancel_left] using hm
  · exact sup_le (le_inf C.core_le_sylow ((le_centralizer U).trans (centralizer_le inf_le_left)))
      (le_inf inf_le_left (inf_le_right.trans (centralizer_le inf_le_right)))

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- Once the dimension branch splits Q, the same original factors split R.
The branch premise remains with qt-d-12225-common-centralizers. -/
theorem centralizer_split_of_kernel_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hQ : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let := C.elementary
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hZU : Z ≤ centralizer (U : Set G) := component_centralizer_le_core_centralizer D A C
  have hZV : Z ≤ normalizer (V : Set G) :=
    (inf_le_right.trans (centralizer_le D.le_component)).trans (Subgroup.centralizer_le_normalizer _)
  have hEQ : E ≤ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊓
      centralizer (U : Set G) := le_inf
    (le_inf inf_le_left (inf_le_right.trans (centralizer_le
      (show V ≤ cyclicPairJoin P U V from le_sup_right))))
    (inf_le_right.trans (centralizer_le
      (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  have hE : E ≤ U ⊔ Z := by
    rw [hQ, sup_comm V Z, inf_centralizer_sup_of_centralizing Z V U hZV hZU,
      chosen_centralizer_core A C] at hEQ
    exact hEQ.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  apply le_antisymm
  · rw [C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural L h).2.2 V D).1) D.le_sylow hnone]
    exact sup_le le_sup_left hE
  · exact sup_le (le_inf C.core_le_sylow (le_centralizer U)) (le_inf inf_le_left hZU)

/-- R is elementary in every dimension, without first splitting Q. The
Frattini subgroup of R equals that of C_T(I), embeds in Φ(Q), and therefore
lies in the common central factor already eliminated by uniqueness. -/
theorem radical_elementary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    IsElementaryAbelian 2 ↥((T : Subgroup G) ⊓ centralizer (U : Set G)) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hR : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hQ : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hEQ : E ≤ Q := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right)))
  have hE : IsPGroup 2 E := T.isPGroup'.to_le inf_le_left
  let : Fact (IsPGroup 2 E) := ⟨hE⟩
  have hfEQ : (frattini E).map E.subtype ≤ (frattini Q).map Q.subtype := by
    have hh := map_mono (f := Q.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hEQ))
    rw [map_map] at hh
    exact hh
  have hfE := frattini_map_eq_of_central_elementary_supplement R E U hR C.elementary
    (le_centralizer_iff.mp inf_le_right)
    (C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural L h).2.2 V D).1) D.le_sylow hnone)
  have hf : (frattini R).map R.subtype = ⊥ := by
    apply bot_unique
    rw [← common_trivial h D C, hfE]
    exact le_inf (le_inf ((map_subtype_le _).trans inf_le_left)
      (hfEQ.trans (kernel_frattini_centralizes D A C))) (map_subtype_le _)
  apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
  exact map_injective R.subtype_injective (hf.trans (Subgroup.map_bot R.subtype).symm)

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- Every automorphism of the binary natural module is realized by L.
Inside LT this gives a product with the literal centralizer of V. -/
theorem local_join_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) :
    L ⊔ (T : Subgroup G) = L ⊔ ((L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G)) := by
  let J := L ⊔ (T : Subgroup G)
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes
    (((structural L h).2.2 V D).1)
  obtain ⟨e,f,hf⟩ := A.natural
  apply le_antisymm _ (sup_le le_sup_left inf_le_left)
  intro g hg
  let a : MulAut V := V.normalizerMonoidHom ⟨g,hJV hg⟩
  obtain ⟨x,hx⟩ := Representation.specialLinearNatural_binary_full d ((f.symm.trans a).trans f)
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm x)
  have hel : e (QuotientGroup.mk' (pCore 2 L) l) = x := by rw [hl,e.apply_symm_apply]
  have ha : V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ = a := by
    ext v
    have hact := hf l v
    rw [hel] at hact
    have heq := hx (f v)
    simp only [MulEquiv.trans_apply, f.symm_apply_apply] at heq
    rw [heq, f.symm_apply_apply] at hact
    exact hact.symm
  have hk : (⟨l,D.normalizes l.property⟩⁻¹ * (⟨g,hJV hg⟩ : normalizer (V : Set G))) ∈
      V.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha]
    exact inv_mul_cancel a
  rw [normalizerMonoidHom_ker] at hk
  have hc : (l : G)⁻¹*g ∈ J ⊓ centralizer (V : Set G) :=
    ⟨J.mul_mem (J.inv_mem ((show L ≤ J from le_sup_left) l.property)) hg,hk⟩
  simpa only [mul_inv_cancel_left] using mul_mem_sup l.property hc

/-- The original Sylow is the product (T∩L)C_T(V), the consequence of
12.2.20 used in the common centralizer proof. -/
theorem sylow_split_over_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
  let J := L ⊔ (T : Subgroup G)
  let B := J ⊓ centralizer (V : Set G)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hLJ : L ≤ J := le_sup_left
  have hBJ : B ≤ J := inf_le_left
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes
    (((structural L h).2.2 V D).1)
  have hJB : J ≤ normalizer (B : Set G) :=
    (le_inf J.le_normalizer (hJV.trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJB
  have hcover : L.subgroupOf J ⊔ B.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hLJ hBJ, ← local_join_split_at h D structural A, subgroupOf_self]
  have he := (T.subtype hTJ).inf_sup_eq_sup_inf_normal (L.subgroupOf J) (B.subgroupOf J)
  rw [hcover, inf_top_eq] at he
  have hm := congrArg (map J.subtype) he
  rw [Subgroup.map_sup, map_inf _ _ _ J.subtype_injective, map_inf _ _ _ J.subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ, map_subgroupOf_eq_of_le hLJ,
    map_subgroupOf_eq_of_le hBJ] at hm
  simpa only [B, inf_assoc, ← inf_assoc, inf_eq_left.mpr hTJ] using hm

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

omit [Finite G] in
private theorem hyperplane_index'_at
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, C.hyperplane, chosen_card A] at hh
  have hd : d = d - 1 + 1 := by have := A.dimension.1; omega
  have hc : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hd
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hc] at hh
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
  nlinarith

/-- The full kernel inside LT is the same literal two-core as C_T(V). -/
theorem local_join_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  have hc : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
    have hm := congrArg (map L.subtype) C.block.2.1.centralizer_blockU
    rw [map_centralizer_subtype, LiteralNaturalBlock.blockLayer_eq D A C] at hm
    exact hm
  rw [ambient_centralizer_eq_core_of_normal_supplement L V (T : Subgroup G)
    D.sylow_normalizes_component (D.le_component.trans le_sup_left)
    (sup_le D.normalizes (((structural L h).2.2 V D).1)) T.isPGroup' hc D.core_centralizes,
    LiteralNaturalBlock.kernel_eq_local_core D A C]

/-- The full pointwise hyperplane stabilizer inside LT is a two-group,
so it equals the centralizer in the original Sylow subgroup. -/
theorem local_join_hyperplane_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let W := U ⊓ V
  let K := J ⊓ centralizer (W : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hTV := (((structural L h).2.2 V D).1)
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes hTV
  let f : K →* MulAut V := V.normalizerMonoidHom.comp (inclusion (inf_le_left.trans hJV))
  let W' := W.subgroupOf V
  let F := fixingSubgroup (MulAut V) (W' : Set V)
  have hfix : f.range ≤ F := by
    rintro _ ⟨k,rfl⟩
    apply (mem_fixingSubgroup_iff (MulAut V)).mpr
    intro w hw
    apply Subtype.ext
    change (k : G) * (w : G) * (k : G)⁻¹ = w
    rw [← k.property.2 w hw, mul_inv_cancel_right]
  have hk : IsPGroup 2 f.ker := by
    apply (T.isPGroup'.to_le (show Q ≤ (T : Subgroup G) from inf_le_left)).comap_subtype.to_le
    intro k hk
    have hkc : (k : G) ∈ centralizer (V : Set G) := by
      have hh : (⟨k,(inf_le_left.trans hJV) k.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker := hk
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    exact (local_join_kernel_at h D structural A C).le ⟨k.property.1,hkc⟩
  have hFp : IsPGroup 2 F := W'.isPGroup_fixingSubgroup_of_index_two
    (hyperplane_index'_at A C) ((T.isPGroup'.to_le (show W ≤ (T : Subgroup G) from inf_le_right.trans D.le_sylow)).comap_subtype)
  have hKp : IsPGroup 2 K := by
    have hp := hFp.comap_of_ker_isPGroup f hk
    have he : F.comap f = ⊤ := top_unique (fun k _ => hfix ⟨k,rfl⟩)
    rw [he] at hp
    exact hp.of_equiv Subgroup.topEquiv
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_inf (le_sup_right.trans J.le_normalizer)
      (hTW.trans (normalizer_le_normalizer_centralizer W))).trans inf_normalizer_le_normalizer_inf
  have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hKp hTK) le_sup_left
  have hKT : K ≤ (T : Subgroup G) := he ▸ le_sup_right
  exact le_antisymm (le_inf hKT inf_le_right) (inf_le_inf_right _ le_sup_right)

/-- The literal hyperplane normalizer in L normalizes C_T(U∩V), as asserted
immediately before 12.2.25. No normality of T in that normalizer is assumed. -/
theorem hyperplane_normalizer_normalizes_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G) ≤
      normalizer (((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  rw [← local_join_hyperplane_centralizer_at h D structural A C]
  exact (le_inf ((inf_le_left.trans le_sup_left).trans (L ⊔ (T : Subgroup G)).le_normalizer)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer (U ⊓ V)))).trans inf_normalizer_le_normalizer_inf

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityResidual
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

/-- The literal residual fixed space, in all three source dimensions. -/
theorem radical_fixed_eq_component_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let W := U ⊓ V
  let Y := rigidityHyperplaneResidual L U V
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let X := R ⊓ centralizer (Y : Set G)
  have hYL : Y ≤ L := (map_subtype_le _).trans inf_le_left
  have hYW : Y ≤ normalizer (W : Set G) := (map_subtype_le _).trans inf_le_right
  have hYV : Y ≤ normalizer (V : Set G) := hYL.trans D.normalizes
  have hTV := ((structural L h).2.2 V D).1
  have hRW : R ≤ centralizer (W : Set G) := inf_le_right.trans (centralizer_le inf_le_left)
  have hRV : R ≤ normalizer (V : Set G) := inf_le_left.trans hTV
  have hVY : ⁅V,Y⁆ ≤ W := commutator_le_of_normalized_index_two V W Y
    inf_le_right (hyperplane_index A C) hYV hYW
  have hVR : ⁅V,R⁆ ≤ W := commutator_le_of_normalized_index_two V W R
    inf_le_right (hyperplane_index A C) hRV
    (hRW.trans (Subgroup.centralizer_le_normalizer _))
  have hXY : ⁅Y,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp inf_le_right)
  have hVYX : ⁅⁅V,Y⁆,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hVY.trans (le_centralizer_iff.mp (inf_le_left.trans hRW)))
  have hXVY : ⁅⁅X,V⁆,Y⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hVYX
    (by rw [hXY, commutator_bot_left])
  have hXVW : ⁅X,V⁆ ≤ W := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_left).trans hVR
  have hXV : ⁅X,V⁆ = ⊥ := bot_unique ((le_inf hXVW
    (commutator_eq_bot_iff_le_centralizer.mp hXVY)).trans_eq
      (hyperplane_residual_fixed_eq_bot D A C))
  have hZX : Z ≤ X := le_inf
    (le_sup_right.trans B.centralizer_split.symm.le)
    (inf_le_right.trans (centralizer_le hYL))
  have hZV : Z ≤ centralizer (V : Set G) :=
    inf_le_right.trans (centralizer_le D.le_component)
  have hZY : Z ≤ centralizer (Y : Set G) := inf_le_right.trans (centralizer_le hYL)
  have hsplit : R ⊓ centralizer (V : Set G) = Z ⊔ W := by
    rw [show R = U ⊔ Z from B.centralizer_split, sup_comm,
      inf_centralizer_sup_of_centralizing Z U V
        ((le_sup_right.trans B.centralizer_split.symm.le).trans
          (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) hZV,
      C.action_kernel]
  have hXZW : X ≤ Z ⊔ W := (le_inf inf_le_left
    (commutator_eq_bot_iff_le_centralizer.mp hXV)).trans hsplit.le
  have hfix : (Z ⊔ W) ⊓ centralizer (Y : Set G) = Z := by
    rw [inf_centralizer_sup_of_centralizing Z W Y
      ((hZV.trans (centralizer_le inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)) hZY,
      hyperplane_residual_fixed_eq_bot D A C, sup_bot_eq]
  exact le_antisymm ((le_inf hXZW inf_le_right).trans hfix.le) hZX

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityResidual
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- The literal kernel is V times its fixed subgroup on the cyclic pair.
This precedes, and does not assume, either cohomology branch. -/
theorem kernel_pair_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  let := D.elementary
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hVQ : V ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    le_inf D.le_sylow (le_centralizer V)
  have hEQ : E ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (centralizer_le
      (show V ≤ cyclicPairJoin P U V from le_sup_right)))
  apply le_antisymm _ (sup_le hVQ hEQ)
  intro q hq
  obtain ⟨v,hv,hvq⟩ := kernel_action_twist D A C
    (((structural L h).2.2 V D).1) hq
  have hvqQ := ((T : Subgroup G) ⊓ centralizer (V : Set G)).mul_mem (hVQ hv) hq
  have hvqJ : v*q ∈ (T : Subgroup G) ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) :=
    ⟨hvqQ.1, le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mp (show zpowers (v*q) ≤ centralizer (U : Set G) from
        zpowers_le.mpr hvq))
      (le_centralizer_iff.mp (show zpowers (v*q) ≤ centralizer (V : Set G) from
        zpowers_le.mpr hvqQ.2))) (mem_zpowers (v*q))⟩
  have hx : v*q ∈ V ⊔ E := (show (U ⊓ V) ⊔ E ≤ V ⊔ E from
    sup_le (inf_le_right.trans le_sup_left) le_sup_right)
    ((join_centralizer_split_at h D structural A C hnone).le hvqJ)
  simpa only [inv_mul_cancel_left] using (V ⊔ E).mul_mem (mem_sup_left (V.inv_mem hv)) hx

/-- The source hyperplane centralizer with the original pair factor, in
all dimensions. No cohomology or component-centralizer split is assumed. -/
theorem hyperplane_pair_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      U ⊔ V ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  rw [hyperplane_centralizer_eq_core_sup_kernel_at h D structural A C,
    kernel_pair_split_at h D structural A C hnone,sup_assoc]

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- An element of the elementary radical lying in L acts nontrivially on V.
This also supplies an involutory lift for the central-cover calculation. -/
theorem exists_component_radical_noncentral_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ l : L, (l : G) ∈ (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
      (l : G) ∉ centralizer (V : Set G) := by
  let := C.elementary
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let TL := (T : Subgroup G) ⊓ L
  have hE : E ≤ R := le_inf inf_le_left (inf_le_right.trans
    (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  have hEV : E ≤ centralizer (V : Set G) := inf_le_right.trans
    (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right))
  have hs : (T : Subgroup G) = TL ⊔ E := by
    rw [sylow_split_over_kernel_at h D structural A,
      kernel_pair_split_at h D structural A C hnone,← sup_assoc,
      sup_eq_left.mpr (le_inf D.le_sylow D.le_component)]
  have hn : ¬ U ≤ centralizer (V : Set G) := by
    intro hu
    have hz : U ⊓ V = ⊥ := C.transvections.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hu)
    have hc := C.hyperplane
    rw [hz,card_bot] at hc
    have hp : 1 < 2 ^ (d - 1) := one_lt_pow₀ (by decide) (by have := A.dimension.1; omega)
    omega
  obtain ⟨u,hu,huV⟩ := SetLike.not_le_iff_exists.mp hn
  have hprod : u ∈ (TL : Set G) * (E : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left TL E
      ((le_inf (inf_le_left.trans (T : Subgroup G).le_normalizer)
        (inf_le_left.trans D.sylow_normalizes_component)).trans inf_normalizer_le_normalizer_inf),← hs]
    exact C.core_le_sylow hu
  obtain ⟨l,hl,e,he,rfl⟩ := hprod
  have hlR : l ∈ R := by
    have hh := R.mul_mem (show l*e ∈ R from ⟨C.core_le_sylow hu,le_centralizer U hu⟩)
      (R.inv_mem (hE he))
    simpa only [mul_inv_cancel_right] using hh
  refine ⟨⟨l,hl.2⟩,hlR,?_⟩
  intro hlV
  exact huV ((centralizer (V : Set G)).mul_mem hlV (hEV he))

/-- The dimension-three kernel split uses a literal fixed involution to
exclude the exceptional natural cocycle. -/
theorem three_kernel_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  subst d
  let := D.elementary
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary_at h D structural A C hnone
  obtain ⟨l,hlR,hlV⟩ := exists_component_radical_noncentral_at h D structural A C hnone
  obtain ⟨e,f,hf⟩ := A.natural
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : a.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hl1 : a l ≠ 1 := by
    intro he
    have hcore : l ∈ pCore 2 L := hk ▸ (MonoidHom.mem_ker.mpr he)
    exact hlV (D.core_centralizes
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hcore)))
  have hl2 : a l * a l = 1 := by
    rw [← map_mul]
    have he : l*l = 1 := Subtype.ext (by
      change (l : G)*(l : G) = 1
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (l : G) hlR)
    rw [he,map_one]
  have hVQ : V ≤ Q := le_inf D.le_sylow (le_centralizer V)
  have hZQ : Z ≤ Q := le_inf inf_le_left (inf_le_right.trans (centralizer_le D.le_component))
  apply le_antisymm _ (sup_le hVQ hZQ)
  intro q hq
  obtain ⟨v,hv,hvq⟩ := kernel_action_twist D A C
    (((structural L h).2.2 V D).1) hq
  let x := v*q
  have hxQ : x ∈ Q := Q.mul_mem (hVQ hv) hq
  have hxR : x ∈ R := ⟨hxQ.1,hvq⟩
  let N := V.subgroupOf L
  let eN : N ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (subgroupOfEquivOfLe D.le_component).trans f
  let ρ := Representation.specialLinearNatural (k := ZMod 2) 3
  have heN (g : L) (w : Fin 3 → ZMod 2) :
      (eN.symm (Multiplicative.ofAdd (ρ (a g) w)) : L) =
        g * (eN.symm (Multiplicative.ofAdd w) : L) * g⁻¹ := by
    apply Subtype.ext
    change (f.symm (Multiplicative.ofAdd (ρ (a g) w)) : G) =
      (g : G) * (f.symm (Multiplicative.ofAdd w) : G) * (g : G)⁻¹
    simpa [a,ρ] using hf g (f.symm (Multiplicative.ofAdd w))
  let α : MulAut L := L.normalizerMonoidHom ⟨x,D.sylow_normalizes_component hxQ.1⟩
  have hdis (g : L) : α g * g⁻¹ ∈ N :=
    (kernel_commutator_eq D A C).le (commutator_mem_commutator hxQ g.property)
  have hfix (n : L) (hn : n ∈ a.ker) : α n = n := by
    apply Subtype.ext
    have hncore : n ∈ pCore 2 L := hk ▸ hn
    have hc := component_core_centralizes_kernel D A C (mem_map_of_mem L.subtype hncore) x hxQ
    change x*(n : G)*x⁻¹ = n
    change x * (n : G) = (n : G) * x at hc
    rw [hc,mul_inv_cancel_right]
  have hfixedl : α l = l := by
    apply Subtype.ext
    change x*(l : G)*x⁻¹ = l
    have hc : x * (l : G) = (l : G) * x := (le_centralizer R hxR l hlR).symm
    rw [hc,mul_inv_cancel_right]
  obtain ⟨n,hn⟩ := Representation.OneCohomology.automorphism_inner_of_fixed_element_of_subkernel
    N a ha eN ρ heN l (fun z hz =>
      Representation.OneCohomology.SLHigherNatural.SLThreeBinary.principal_of_zero_involution
        z (a l) hl1 hl2 hz) α hdis hfix hfixedl
  have hnV : ((n : L) : G) ∈ V := n.property
  have hnxZ : ((n : L) : G)*x ∈ Z := by
    refine ⟨(T : Subgroup G).mul_mem (D.le_sylow hnV) hxQ.1,?_⟩
    intro g hg
    have he := congrArg Subtype.val (hn ⟨g,hg⟩)
    change x*g*x⁻¹ = ((n : L) : G)⁻¹*g*((n : L) : G) at he
    calc
      g*(((n : L) : G)*x) = ((n : L) : G)*
        (((n : L) : G)⁻¹*g*((n : L) : G))*x := by group
      _ = ((n : L) : G)*(x*g*x⁻¹)*x := by rw [he]
      _ = (((n : L) : G)*x)*g := by group
  have hx : x ∈ V ⊔ Z := by
    have hh := (V ⊔ Z).mul_mem (mem_sup_left (V.inv_mem hnV)) (mem_sup_right hnxZ)
    simpa only [inv_mul_cancel_left] using hh
  have hh := (V ⊔ Z).mul_mem (mem_sup_left (V.inv_mem hv)) hx
  simpa only [x,inv_mul_cancel_left] using hh

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel
omit [Finite G] in
private theorem fixed_supplement_hyperplane_index_at
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, C.hyperplane, chosen_card A] at hh
  have hd : d = d - 1 + 1 := by have := A.dimension.1; omega
  have hc : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hd
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hc] at hh
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
  nlinarith

/-- The centralizer R has index two in the hyperplane centralizer in every
dimension. -/
theorem radical_hyperplane_index_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ((T : Subgroup G) ⊓ centralizer (U : Set G)).relIndex
      ((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)) = 2 := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let K := (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)
  have hRV : R ⊓ V = U ⊓ V := by
    rw [inf_assoc, inf_comm (centralizer _) V, chosen_centralizer_core A C,
      inf_eq_right.mpr (inf_le_right.trans D.le_sylow)]
  have hRK : R ≤ K := inf_le_inf_left _ (centralizer_le inf_le_left)
  have hs : R ⊔ V = K := by
    dsimp only [K]
    rw [hyperplane_pair_split_at h D structural A C hnone]
    dsimp only [R]
    rw [C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural L h).2.2 V D).1) D.le_sylow hnone]
    ac_rfl
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes R V
    (D.le_sylow.trans ((le_inf (T : Subgroup G).le_normalizer
      (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
        inf_normalizer_le_normalizer_inf))
  rw [hRV,hs] at hp
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) R K bot_le hRK
  rw [relIndex_bot_left,relIndex_bot_left] at hi
  have hv := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,fixed_supplement_hyperplane_index_at A C] at hv
  have hr := Nat.card_pos (α := R)
  have hw := Nat.card_pos (α := ↥(U ⊓ V))
  change R.relIndex K = 2
  rw [← hi, ← hv] at hp
  have he : Nat.card R * Nat.card ↥(U ⊓ V) * 2 =
      Nat.card R * Nat.card ↥(U ⊓ V) * R.relIndex K := by nlinarith only [hp]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr hw) he).symm

/-- The two-residual of the literal hyperplane normalizer fixes R. The
index-two elementary argument replaces the source's Thompson calculation
without requiring a complement or self-normalization. -/
theorem residual_normalizes_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    rigidityHyperplaneResidual L U V ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let K := (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)
  have hUK : U ≤ K := le_inf C.core_le_sylow (by
    let := C.elementary
    exact (le_centralizer U).trans (centralizer_le inf_le_left))
  have hVK : V ≤ K := le_inf D.le_sylow (by
    let := D.elementary
    exact (le_centralizer V).trans (centralizer_le inf_le_right))
  have hnot : ¬ IsElementaryAbelian 2 K := by
    intro hk
    let := hk
    have hu : U ≤ centralizer (V : Set G) :=
      hUK.trans ((le_centralizer K).trans (centralizer_le hVK))
    have hz : U ⊓ V = ⊥ := C.transvections.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hu)
    have hh := C.hyperplane
    rw [hz,card_bot] at hh
    have hd1 : 0 < d-1 := by have := A.dimension.1; omega
    have hp : 1 < 2^(d-1) := one_lt_pow₀ (by decide) (by omega)
    omega
  exact twoPerfect_le_normalizer_elementary_index_two _ K R
    (isPPerfect_embedded_pResidual 2 _)
    ((map_subtype_le _).trans (hyperplane_normalizer_normalizes_centralizer_at h D structural A C))
    (inf_le_inf_left _ (centralizer_le inf_le_left))
    (radical_elementary_at h D structural A C hnone)
    (radical_hyperplane_index_at h D structural A C hnone) hnot

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

/-- Both dimensional arguments split the original kernel. -/
theorem source_kernel_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  by_cases hd : d = 3
  · exact three_kernel_split_at h D structural A C hnone hd
  · exact higher_kernel_split D A C (by have := A.dimension.1; omega)

/-- The second literal centralizer decomposition in (*) in every dimension. -/
theorem source_centralizer_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  centralizer_split_of_kernel_split_at h D structural A C hnone (source_kernel_split_at h D structural A C hnone)

/-- Both decompositions in (*) use the original multiplication maps. -/
theorem source_centralizer_directProduct_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ e : U × ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (U : Set G)),
      ∀ u z, (e (u,z) : G) = (u : G) * (z : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) (core_disjoint_component_centralizer D A C)
    (le_centralizer_iff.mp (component_centralizer_le_core_centralizer D A C))
  exact ⟨e.trans (MulEquiv.subgroupCongr (source_centralizer_split_at h D structural A C hnone).symm),he⟩

/-- The two elementary central factors have the same order, as used in the
source's subsequent rank bound. No order-two bound is assumed. -/
theorem source_central_factors_card_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) =
      Nat.card ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  obtain ⟨e,_⟩ := source_centralizer_directProduct_at h D structural A C hnone
  obtain ⟨f,_⟩ := chosen_centralizer_core_directProduct_at h D structural A C hnone
  have hc := Nat.card_congr (e.trans f.symm).toEquiv
  rw [Nat.card_prod, Nat.card_prod] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- The literal hyperplane split, re-exported with the common centralizers. -/
theorem source_hyperplane_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      U ⊔ V ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) :=
  hyperplane_pair_split_at h D structural A C hnone

/-- The source Sylow product over C_T(L), in every dimension. -/
theorem source_sylow_split_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have he := sylow_split_over_kernel_at h D structural A
  rw [source_kernel_split_at h D structural A C hnone, ← sup_assoc,
    sup_eq_left.mpr (le_inf D.le_sylow D.le_component)] at he
  exact he

/-- The component's Sylow centralizer is central in T, after the literal
kernel split. Elementarity of R supplies its own internal commutativity. -/
theorem source_component_centralizer_central_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ centralizer (T : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary_at h D structural A C hnone
  have hZR : Z ≤ R := le_inf inf_le_left (component_centralizer_le_core_centralizer D A C)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hZR
  apply le_centralizer_iff.mp
  conv_lhs => rw [source_sylow_split_at h D structural A C hnone]
  exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le inf_le_right)))
    (le_centralizer Z)

/-- The second central factor is central in T as well: its T-commutator
lies both in U and in the disjoint factor C_T(I). -/
theorem source_pair_centralizer_central_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) ≤ centralizer (T : Set G) := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  have hZU := component_centralizer_le_core_centralizer D A C
  have hZT := source_component_centralizer_central_at h D structural A C hnone
  have hER : E ≤ (T : Subgroup G) ⊓ centralizer (U : Set G) :=
    le_inf inf_le_left (inf_le_right.trans
      (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  rw [← disjoint_iff.mp C.core_disjoint_sylow_pair_centralizer]
  refine le_inf ?_ (le_normalizer_iff_commutator_le_left.mp (sylow_normalizes_pair_centralizer C))
  apply commutator_le.mpr
  intro x hx t ht
  have hprod : x ∈ (U : Set G) * (Z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U Z (hZU.trans (Subgroup.centralizer_le_normalizer _)),
      ← source_centralizer_split_at h D structural A C hnone]
    exact hER hx
  obtain ⟨u,hu,z,hz,rfl⟩ := hprod
  have hc : ⁅z,t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZT hz t ht).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hc, mul_one, mul_inv_cancel, one_mul]
  exact (le_normalizer_iff_commutator_le_left.mp C.sylow_normalizes_core)
    (commutator_mem_commutator hu ht)

/-- The source's order-two bound for the two common central factors in the
all-dimensional calculation. -/
theorem source_component_centralizer_card_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≤ 2 := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let F := V ⊓ centralizer (T : Set G)
  have hZT : Z ≤ centralizer (T : Set G) := source_component_centralizer_central_at h D structural A C hnone
  have hET : E ≤ centralizer (T : Set G) := source_pair_centralizer_central_at h D structural A C hnone
  have hEZ : Disjoint E Z := disjoint_iff.mpr (by rw [inf_comm]; exact common_trivial h D C)
  have hFZ : Disjoint F Z := (kernel_disjoint D A).mono_left inf_le_left
  have hZE : Z ≤ normalizer (E : Set G) :=
    ((le_centralizer_iff.mp hET).trans' inf_le_left).trans (Subgroup.centralizer_le_normalizer _)
  have hZF : Z ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp ((inf_le_left.trans D.le_sylow).trans (le_centralizer_iff.mp hZT))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEQ : E ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    le_inf inf_le_left (hET.trans (centralizer_le D.le_sylow))
  have hEZF : E ≤ Z ⊔ F := by
    have hh : E ≤ (Z ⊔ V) ⊓ centralizer (T : Set G) := by
      rw [sup_comm Z V, ← source_kernel_split_at h D structural A C hnone]
      exact le_inf hEQ hET
    change E ≤ (Z ⊔ V) ⊓ centralizer (((T : Subgroup G) : Set G)) at hh
    rwa [inf_centralizer_sup_of_centralizing Z V (T : Subgroup G)
      (hZT.trans (centralizer_le D.le_sylow) |>.trans (Subgroup.centralizer_le_normalizer _)) hZT] at hh
  have hcard : Nat.card E * Nat.card Z ≤ Nat.card F * Nat.card Z := by
    rw [← card_sup_eq_mul_of_normalizes_of_disjoint E Z hZE hEZ,
      ← card_sup_eq_mul_of_normalizes_of_disjoint F Z hZF hFZ]
    have hi : E ⊔ Z ≤ F ⊔ Z := sup_le (hEZF.trans_eq (sup_comm Z F)) le_sup_right
    exact Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
  have he : Nat.card E ≤ Nat.card F := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
  rw [source_central_factors_card_at h D structural A C hnone]
  exact he.trans (chosen_sylow_fixed_card D A)

/-- Assembly of the all-dimensional record after the still-owned Sylow
intersection step. The common-centralizers owner must discharge `hdisjoint`;
this conditional application is not a completed source theorem. -/
theorem centralizers_of_sylow_disjoint_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hdisjoint : Disjoint ((T : Subgroup G) ⊓ L)
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    LocalRigidityCentralizers T L V U P where
  kernel_split := source_kernel_split_at h D structural A C hnone
  kernel_disjoint := kernel_disjoint D A
  centralizer_split := source_centralizer_split_at h D structural A C hnone
  centralizer_disjoint := core_disjoint_component_centralizer D A C
  common_trivial := common_trivial h D C
  elementary := radical_elementary_at h D structural A C hnone
  component_centralizer_card := source_component_centralizer_card_at h D structural A C hnone
  sylow_split := source_sylow_split_at h D structural A C hnone
  sylow_disjoint := hdisjoint
  component_centralizer_central := source_component_centralizer_central_at h D structural A C hnone
  pair_centralizer_central := source_pair_centralizer_central_at h D structural A C hnone
  hyperplane_centralizer := source_hyperplane_centralizer_at h D structural A C hnone
  residual_normalizes := residual_normalizes_at h D structural A C hnone

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
end

section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

/-- An involutory lift excludes the exceptional central SL₃ cover. -/
theorem three_component_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3) : L.pCoreIn 2 = V := by
  subst d
  let := h.quasisimple
  let q := ChapterC.blockCoreProjection (L := L)
  have hq : Function.Surjective q := ChapterC.blockCoreProjection_surjective
  have hqc : q.ker ≤ center (L ⧸ ChapterC.blockU L) := by
    rw [ChapterC.blockCoreProjection_ker]
    exact ChapterC.blockU_core_image_le_center
  have hqp : IsPGroup 2 q.ker := by
    rw [ChapterC.blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  let : Group.IsPerfect (L ⧸ ChapterC.blockU L) :=
    IsPPerfect.isPerfect_of_surjective_pGroup_kernel
      (C.block.2.1.quotient_twoPerfect _) q hq hqp
  obtain ⟨e, _, _⟩ := A.natural
  let f := e.toMonoidHom.comp q
  have hk : f.ker = q.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
  obtain ⟨l, hlR, hlV⟩ := exists_component_radical_noncentral_at h D structural A C hnone
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary_at h D structural A C hnone
  have hl2 : l ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (l : G) hlR)
  let x := QuotientGroup.mk' (ChapterC.blockU L) l
  have hfx : f x ≠ 1 := by
    intro hx
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := e.injective (by
      simpa only [f, q, x, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, ChapterC.blockCoreProjection, QuotientGroup.mk'_apply,
        QuotientGroup.lift_mk, map_one] using hx)
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp he
    exact hlV (D.core_centralizes
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hlcore)))
  have hf := BinaryLinearThree.CentralCover.kernel_eq_bot_of_involution f
    (e.surjective.comp hq) (hk ▸ hqc) (hk ▸ hqp) x
    (by simpa only [map_pow, map_one] using congrArg (QuotientGroup.mk' (ChapterC.blockU L)) hl2) hfx
  exact core_eq_of_blockProjection_injective D A C
    ((MonoidHom.ker_eq_bot_iff _).mp (hk ▸ hf))

/-- The complete common-centralizer record in dimension three. -/
theorem three_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3) : LocalRigidityCentralizers T L V U P :=
  centralizers_of_sylow_disjoint_at h D structural A C hnone
    (sylow_disjoint_of_component_core D A (three_component_core_at h D structural A C hnone hd))

/-- The complete common-centralizer record in dimension five. -/
theorem five_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 5) : LocalRigidityCentralizers T L V U P :=
  centralizers_of_sylow_disjoint_at h D structural A C hnone
    (sylow_disjoint_of_component_core D A (five_component_core h D A C hd))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
end

section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

private theorem sylow_le_component_of_intersection_ne_bot_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hne : ((T : Subgroup G) ⊓ L) ⊓
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) ≠ ⊥) : (T : Subgroup G) ≤ L := by
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let B := ((T : Subgroup G) ⊓ L) ⊓ Z
  have hlo : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot (H := B)).mpr hne
  have hhi : Nat.card Z ≤ 2 := source_component_centralizer_card_at h D structural A C hnone
  have he : B = Z := eq_of_le_of_card_ge inf_le_right (by omega)
  have hZL : Z ≤ L := he ▸ (inf_le_left.trans inf_le_right : B ≤ L)
  rw [source_sylow_split_at h D structural A C hnone]
  exact sup_le inf_le_right hZL

open scoped MatrixGroups
open GLS3.Chapter5.SchurPresentation

/-- The dimension-four Sylow factors are disjoint, using the literal image of U. -/
theorem four_sylow_disjoint_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 4) :
    Disjoint ((T : Subgroup G) ⊓ L)
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  subst d
  by_contra hn
  have hne := mt disjoint_iff.mpr hn
  have hTL := sylow_le_component_of_intersection_ne_bot_at h D structural A C hnone hne
  have hUL : U ≤ L := C.core_le_sylow.trans hTL
  let := h.quasisimple
  let q := ChapterC.blockCoreProjection (L := L)
  let r := QuotientGroup.mk' (ChapterC.blockU L)
  have hq : Function.Surjective q := ChapterC.blockCoreProjection_surjective
  have hqc : q.ker ≤ center (L ⧸ ChapterC.blockU L) := by
    rw [ChapterC.blockCoreProjection_ker]
    exact ChapterC.blockU_core_image_le_center
  have hqp : IsPGroup 2 q.ker := by
    rw [ChapterC.blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  let : Group.IsPerfect (L ⧸ ChapterC.blockU L) :=
    IsPPerfect.isPerfect_of_surjective_pGroup_kernel
      (C.block.2.1.quotient_twoPerfect _) q hq hqp
  let : IsQuasisimple (L ⧸ ChapterC.blockU L) :=
    PerfectCentralCovering.Cover.isQuasisimple
      { toMonoidHom := q, surjective := hq, ker_le_center := hqc, isPerfect := inferInstance }
  let e := A.natural.choose.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  let : IsQuasisimple (alternatingGroup (Fin 8)) := alternatingGroup_isQuasisimple 3
  let f : Covering (L ⧸ ChapterC.blockU L) (alternatingGroup (Fin 8)) :=
    { toMonoidHom := e.toMonoidHom.comp q
      surjective := e.surjective.comp hq }
  have hk : f.toMonoidHom.ker = q.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
  have hkne : f.toMonoidHom.ker ≠ ⊥ := by
    intro he
    have hi : Function.Injective q := (MonoidHom.ker_eq_bot_iff _).mp (hk ▸ he)
    exact hn (sylow_disjoint_of_component_core D A (core_eq_of_blockProjection_injective D A C hi))
  have hkcard : Nat.card f.toMonoidHom.ker = 2 := by
    have hdvd := GLS3.Chapter5.Covering.coveringKernel_card_dvd_of_universal
      (schurAlternatingCovering 3) (theorem_5_2_3_b_universality 3 (by decide) (by decide)) f
    rw [natCard_ker_schurAlternatingCovering] at hdvd
    have hlt := (Subgroup.one_lt_card_iff_ne_bot (H := f.toMonoidHom.ker)).mpr hkne
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  let t := T.subtype hTL
  let S := t.mapSurjective (QuotientGroup.mk'_surjective (ChapterC.blockU L))
  let B := (U.subgroupOf L).map r
  have hBS : B ≤ (S : Subgroup (L ⧸ ChapterC.blockU L)) :=
    map_mono (fun _ hu => C.core_le_sylow hu)
  have hSnorm : (S : Subgroup (L ⧸ ChapterC.blockU L)) ≤ normalizer (B : Set _) := by
    apply le_trans (map_mono (show (t : Subgroup L) ≤ normalizer (U.subgroupOf L : Set L) from ?_))
      (Subgroup.le_normalizer_map r)
    intro l hl
    exact Subgroup.le_normalizer_comap L.subtype (C.sylow_normalizes_core hl)
  have hBdis : Disjoint B f.toMonoidHom.ker := by
    apply disjoint_def.mpr
    rintro x ⟨l,hl,rfl⟩ hx
    have hqr : q (r l) = 1 := by
      apply e.injective
      exact hx.trans e.map_one.symm
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp (by
      simpa only [q, r, ChapterC.blockCoreProjection, QuotientGroup.mk'_apply,
        QuotientGroup.lift_mk] using hqr)
    have hlV : (l : G) ∈ V := (C.action_kernel.le ⟨hl, D.core_centralizes
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hlcore))⟩).2
    have hlblock : l ∈ ChapterC.blockU L := by
      have hh := LiteralNaturalBlock.blockLayer_eq D A C
      rw [← hh] at hlV
      obtain ⟨l',hl',he⟩ := hlV
      exact Subtype.coe_injective he ▸ hl'
    exact (QuotientGroup.eq_one_iff l).mpr hlblock
  let N := B.subgroupOf (S : Subgroup (L ⧸ ChapterC.blockU L))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hBS).mpr hSnorm
  have hN : N = ⊥ := Theory.SpecificGroups.SymmetricEight.DoubleSylow.normal_subgroup_eq_bot
    f hkcard S N (by rw [map_subgroupOf_eq_of_le hBS]; exact hBdis)
  have hB : B = ⊥ := by
    rw [← map_subgroupOf_eq_of_le hBS]
    change B.subgroupOf (S : Subgroup (L ⧸ ChapterC.blockU L)) = ⊥ at hN
    rw [hN, Subgroup.map_bot]
  have hUV : U ≤ V := by
    intro u hu
    let l : L := ⟨u,hUL hu⟩
    have hr : r l = 1 := by
      have hm : r l ∈ B := mem_map_of_mem r hu
      rwa [hB, mem_bot] at hm
    have hl := (QuotientGroup.eq_one_iff l).mp hr
    rw [← LiteralNaturalBlock.blockLayer_eq D A C]
    exact mem_map_of_mem L.subtype hl
  have hc := C.hyperplane
  rw [inf_eq_left.mpr hUV,C.dimension] at hc
  norm_num at hc

/-- The complete common-centralizer record in dimension four. -/
theorem four_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 4) : LocalRigidityCentralizers T L V U P :=
  centralizers_of_sylow_disjoint_at h D structural A C hnone
    (four_sylow_disjoint_at h D structural A C hnone hd)

/-- Both higher-dimensional branches, with every centralizer field discharged. -/
theorem higher_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 4 ∨ d = 5) : LocalRigidityCentralizers T L V U P := by
  rcases hd with hd | hd
  · exact four_centralizers_at h D structural A C hnone hd
  · exact five_centralizers_at h D structural A C hnone hd

/-- The complete common-centralizer and residual-normalizer calculation from
the original source hypotheses, in all three permitted dimensions. -/
theorem source_centralizers_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) : LocalRigidityCentralizers T L V U P := by
  by_cases hd : d = 3
  · exact three_centralizers_at h D structural A C hnone hd
  · exact higher_centralizers_at h D structural A C hnone (by have := A.dimension; omega)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
end
