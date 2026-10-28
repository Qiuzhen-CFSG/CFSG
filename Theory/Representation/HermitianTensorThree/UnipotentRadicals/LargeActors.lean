module
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Faithfulness
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# Large elementary actors on the descended Hermitian tensor

An inner elementary actor is conjugate into one of the two unitriangular
root planes. Once its binary rank exceeds 2n, two-coordinate linear
relations force the fixed matrices into a space of dimension at most 4n.
For an outer actor of rank greater than one, conjugate its involution to
the field swap. Its nontrivial inner intersection acts faithfully on both
three-dimensional sections of the six-dimensional fixed space, so each
section contributes at most two fixed-field dimensions.

Together these calculations prove the rank-at-least-3n clause of H.4.4(3)
in the full binary normalizer, including n = 1. They do not assert the
stronger inner rank-greater-than-n clause or the odd-torus exclusions.
The Chapter 12 HermitianGeometry consumer applies the result to the
original chosen orbit and discharges its saturation geometry premise.

The implementation import intentionally reuses the internal Sylow
conjugator and plane-fixed equations from UnipotentRadicals; no existing
public boundary or shared foundational module is changed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.4.4(3,6),
printed p.381, and 8.2.4, printed p.716 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.HermitianTensorThree.LargeActors
variable (n : ℕ) [NeZero n]

private theorem independent_coordinates {K D : Type*} [Field K] [Finite K] [Finite D]
    (f g : D → K) (hi : Function.Injective (fun d => (f d, g d)))
    (hc : Nat.card K < Nat.card D) (u v : K)
    (h : ∀ d, f d * u + g d * v = 0) : u = 0 ∧ v = 0 := by
  have hv : v = 0 := by
    by_contra hv
    have hf : Function.Injective f := by
      intro a b hab
      apply hi
      apply Prod.ext hab
      apply mul_right_cancel₀ hv
      linear_combination h a - h b - u * hab
    exact (not_le_of_gt hc) (Nat.card_le_card_of_injective f hf)
  refine ⟨?_, hv⟩
  by_contra hu
  have hg : Function.Injective g := by
    intro a b hab
    apply hi
    apply Prod.ext _ hab
    apply mul_right_cancel₀ hu
    linear_combination h a - h b - v * hab
  exact (not_le_of_gt hc) (Nat.card_le_card_of_injective g hg)

private theorem card_gt_field (B : Subgroup (U (E n)))
    (hr : 2*n < rank B) : Nat.card (E n) < Nat.card B := by
  rw [card_E]
  exact (Nat.pow_lt_pow_right Nat.one_lt_two hr).trans_le
    (Nat.pow_log_le_self 2 (Nat.card_pos (α := B).ne'))

omit [NeZero n] in
private theorem point_coordinates_injective (B : Subgroup (U (E n)))
    (hB : B ≤ V₁ (E n)) : Function.Injective (fun b : B => (b.val.x, b.val.c)) := by
  intro a b h
  apply Subtype.ext
  exact U.ext (congrArg Prod.fst h)
    (((mem_V₁ _ _).mp (hB a.property)).trans ((mem_V₁ _ _).mp (hB b.property)).symm)
    (congrArg Prod.snd h)

omit [NeZero n] in
private theorem plane_coordinates_injective (B : Subgroup (U (E n)))
    (hB : B ≤ V₂ (E n)) : Function.Injective (fun b : B => (b.val.c, sigma n b.val.y)) := by
  intro a b h
  apply Subtype.ext
  exact U.ext
    (((mem_V₂ _ _).mp (hB a.property)).trans ((mem_V₂ _ _).mp (hB b.property)).symm)
    ((sigma n).injective (congrArg Prod.snd h)) (congrArg Prod.fst h)

private theorem fixed_equation (B : Subgroup (U (E n)))
    (X : fixedSpace (UnipotentRadicals.ambientAction n) (B.map (UnipotentRadicals.unipotentHom n)))
    (b : B) : matrix (E n) b.val * X.val.val * adjoint n (matrix (E n) b.val) = X.val.val := by
  exact congrArg Subtype.val (X.property ⟨_, mem_map_of_mem _ b.property⟩)

private theorem point_fixed_conditions (B : Subgroup (U (E n)))
    (hB : B ≤ V₁ (E n)) (hr : 2*n < rank B)
    (X : fixedSpace (UnipotentRadicals.ambientAction n) (B.map (UnipotentRadicals.unipotentHom n))) :
    X.val.val 1 1 = 0 ∧ X.val.val 2 1 = 0 ∧ X.val.val 1 2 = 0 ∧ X.val.val 2 2 = 0 := by
  have hrel (j : Fin 3) (hj : j = 1 ∨ j = 2) (b : B) :
      b.val.x * X.val.val 1 j + b.val.c * X.val.val 2 j = 0 := by
    have he := congrArg (fun Y : Mat n => Y 0 j) (fixed_equation n B X b)
    have hy := (mem_V₁ _ _).mp (hB b.property)
    rcases hj with rfl | rfl <;>
      simp [matrix, adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, hy] at he <;>
      linear_combination he
  obtain ⟨h11,h21⟩ := independent_coordinates (fun b : B => b.val.x) (fun b : B => b.val.c)
    (point_coordinates_injective n B hB) (card_gt_field n B hr) _ _ (hrel 1 (Or.inl rfl))
  obtain ⟨h12,h22⟩ := independent_coordinates (fun b : B => b.val.x) (fun b : B => b.val.c)
    (point_coordinates_injective n B hB) (card_gt_field n B hr) _ _ (hrel 2 (Or.inr rfl))
  exact ⟨h11,h21,h12,h22⟩

private theorem plane_fixed_conditions (B : Subgroup (U (E n)))
    (hB : B ≤ V₂ (E n)) (hr : 2*n < rank B)
    (X : fixedSpace (UnipotentRadicals.ambientAction n) (B.map (UnipotentRadicals.unipotentHom n))) :
    X.val.val 2 2 = 0 ∧ X.val.val 1 2 = 0 ∧ X.val.val 0 2 = 0 := by
  have hc := card_gt_field n B hr
  have hi := plane_coordinates_injective n B hB
  have h22 : X.val.val 2 2 = 0 := by
    apply (independent_coordinates (fun b : B => b.val.c) (fun b : B => sigma n b.val.y)
      hi hc (X.val.val 2 2) 0 ?_).1
    intro b
    have he := congrArg (fun Y : Mat n => Y 0 2) (fixed_equation n B X b)
    have hx := (mem_V₂ _ _).mp (hB b.property)
    simp [matrix,adjoint,Matrix.mul_apply, Matrix.vecMul, dotProduct,Fin.sum_univ_three,hx] at he
    simpa using he
  have hrel (b : B) : b.val.c * X.val.val 2 1 + sigma n b.val.y * X.val.val 0 2 = 0 := by
    have he := congrArg (fun Y : Mat n => Y 0 1) (fixed_equation n B X b)
    have hx := (mem_V₂ _ _).mp (hB b.property)
    simp [matrix,adjoint,Matrix.mul_apply, Matrix.vecMul, dotProduct,Fin.sum_univ_three,hx,h22] at he
    linear_combination he
  obtain ⟨h21,h02⟩ := independent_coordinates (fun b : B => b.val.c)
    (fun b : B => sigma n b.val.y) hi hc _ _ hrel
  exact ⟨h22, by rw [← entry_conjugate n X.val 1 2,h21,map_zero],h02⟩

private theorem point_fixed_card (B : Subgroup (U (E n)))
    (hB : B ≤ V₁ (E n)) (hr : 2*n < rank B) :
    Nat.card (fixedSpace (UnipotentRadicals.ambientAction n)
      (B.map (UnipotentRadicals.unipotentHom n))) ≤ 2^(4*n) := by
  obtain ⟨b,hb⟩ : ∃ b : B, b.val.x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hi : Function.Injective (fun b : B => b.val.c) := by
      intro a b h
      exact point_coordinates_injective n B hB (Prod.ext ((hn a).trans (hn b).symm) h)
    exact (not_le_of_gt (card_gt_field n B hr)) (Nat.card_le_card_of_injective _ hi)
  let W := fixedSpace (UnipotentRadicals.ambientAction n) (B.map (UnipotentRadicals.unipotentHom n))
  have htrace (X : W) : sigma n (b.val.x * X.val.val 1 0 + b.val.c * X.val.val 2 0) =
      b.val.x * X.val.val 1 0 + b.val.c * X.val.val 2 0 := by
    obtain ⟨h11,h21,h12,h22⟩ := point_fixed_conditions n B hB hr X
    have hy := (mem_V₁ _ _).mp (hB b.property)
    have he := congrArg (fun Y : Mat n => Y 0 0) (fixed_equation n B X b)
    simp [matrix,adjoint,Matrix.mul_apply, Matrix.vecMul, dotProduct,Fin.sum_univ_three,hy,h11,h21,h12,h22] at he
    apply (CharTwo.add_eq_zero.mp ?_).symm
    rw [map_add,map_mul,map_mul,entry_conjugate,entry_conjugate]
    linear_combination he
  let f : W → (F n × F n) × E n := fun X =>
    ((⟨X.val.val 0 0,entry_conjugate n X.val 0 0⟩,
      ⟨b.val.x * X.val.val 1 0 + b.val.c * X.val.val 2 0,htrace X⟩), X.val.val 0 2)
  have hi : Function.Injective f := by
    intro X Y he
    have h00 := congrArg (fun z : (F n × F n) × E n => z.1.1.val) he
    have ht := congrArg (fun z : (F n × F n) × E n => z.1.2.val) he
    have h02 := congrArg (fun z : (F n × F n) × E n => z.2) he
    change X.val.val 0 0 = Y.val.val 0 0 at h00
    change X.val.val 0 2 = Y.val.val 0 2 at h02
    have h20 : X.val.val 2 0 = Y.val.val 2 0 := by
      rw [← entry_conjugate n X.val 2 0,← entry_conjugate n Y.val 2 0,h02]
    have h10 : X.val.val 1 0 = Y.val.val 1 0 := by
      apply mul_left_cancel₀ hb
      change b.val.x * X.val.val 1 0 + b.val.c * X.val.val 2 0 =
        b.val.x * Y.val.val 1 0 + b.val.c * Y.val.val 2 0 at ht
      rw [h20] at ht
      exact add_right_cancel ht
    have h01 : X.val.val 0 1 = Y.val.val 0 1 := by
      rw [← entry_conjugate n X.val 0 1,← entry_conjugate n Y.val 0 1,h10]
    obtain ⟨hx11,hx21,hx12,hx22⟩ := point_fixed_conditions n B hB hr X
    obtain ⟨hy11,hy21,hy12,hy22⟩ := point_fixed_conditions n B hB hr Y
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hx11,hx21,hx12,hx22,hy11,hy21,hy12,hy22,h00,h01,h02,h10,h20]
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_prod,Nat.card_prod,card_F,card_E,← pow_add,← pow_add] at hc
  convert hc using 1
  congr 1
  omega

private theorem plane_fixed_rank (B : Subgroup (U (E n)))
    (hB : B ≤ V₂ (E n)) (hr : 2*n < rank B) :
    Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
      (B.map (UnipotentRadicals.unipotentHom n))) ≤ 4*n := by
  have hle : fixedSpace (UnipotentRadicals.ambientAction n)
      (B.map (UnipotentRadicals.unipotentHom n)) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) := by
    intro X hX
    exact (UnipotentRadicals.mem_plane_fixed_iff n X).mpr
      (plane_fixed_conditions n B hB hr ⟨X,hX⟩)
  exact (Submodule.finrank_mono hle).trans_eq (UnipotentRadicals.finrank_plane_fixed n)

/-- An elementary subgroup of the inner image of rank greater than 2n
fixes at most 4n binary dimensions. -/
theorem inner_fixed_rank_le
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAL : A ≤ binaryImage n) (hr : 2*n < rank A) :
    Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) A) ≤ 4*n := by
  obtain ⟨c,hc⟩ := UnipotentRadicals.two_subgroup_conjugate_le_unipotent n A
    (IsElementaryAbelian.isPGroup 2 A) hAL
  let f := (MulAut.conj (binaryActionHom n c)).toMonoidHom
  let B := (A.map f).comap (UnipotentRadicals.unipotentHom n)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hi : Function.Injective ((UnipotentRadicals.unipotentHom n).subgroupComap (A.map f)) :=
    fun a b h => Subtype.ext (UnipotentRadicals.unipotentHom_injective n (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective _ hi
  have hm : B.map (UnipotentRadicals.unipotentHom n) = A.map f := map_comap_eq_self hc
  have hBr : 2*n < rank B := by
    rw [← rank_map_injective (UnipotentRadicals.unipotentHom n)
      (UnipotentRadicals.unipotentHom_injective n),hm,rank_map_conj]
    exact hr
  have hd : Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) A) =
      Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
        (B.map (UnipotentRadicals.unipotentHom n))) := by
    rw [hm]
    exact (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) A
      (binaryActionHom n c)).finrank_eq
  rw [hd]
  rcases elementary_le_plane (E n) B with hB | hB
  · have hcard := point_fixed_card n B hB hBr
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    exact (pow_le_pow_iff_right₀ Nat.one_lt_two).mp hcard
  · exact plane_fixed_rank n B hB hBr

open FieldSections

private theorem ker_rank_le_two {K D W : Type*} [Field K] [Group D]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K D W) (hρ : Function.Injective ρ)
    (hd : Module.finrank K W = 3) (a : D) (ha : a ≠ 1) :
    Module.finrank K (LinearMap.ker (ρ a - LinearMap.id)) ≤ 2 := by
  have hn : LinearMap.ker (ρ a - LinearMap.id) ≠ ⊤ := by
    intro he
    apply ha
    apply hρ
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.ker (ρ a - LinearMap.id) := he ▸ Submodule.mem_top
    exact sub_eq_zero.mp hv
  have hh := Submodule.finrank_lt hn
  rw [hd] at hh
  omega

private theorem field_fixed_rank_le (a : FieldSections.centralizer n) (ha : a ≠ 1) :
    Module.finrank (F n) (LinearMap.ker (fixedAction n a - LinearMap.id)) ≤ 4 := by
  let W := LinearMap.ker (fixedAction n a - LinearMap.id)
  let Q := LinearMap.ker (middleAction n a - LinearMap.id)
  let U := LinearMap.ker (movedAction n a - LinearMap.id)
  have hq := ker_rank_le_two (middleAction n) (middleAction_faithful n) (finrank_middle n) a ha
  have hu := ker_rank_le_two (movedAction n) (movedAction_faithful n) (finrank_moved n) a ha
  have hfix (X : W) : fixedAction n a X.val = X.val := sub_eq_zero.mp X.property
  let f : W →ₗ[F n] Q :=
    { toFun := fun X => ⟨(movedInFixed n).mkQ X.val, by
        change middleAction n a ((movedInFixed n).mkQ X.val) - (movedInFixed n).mkQ X.val = 0
        rw [middleAction_mk,hfix,sub_self]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let j : LinearMap.ker f →ₗ[F n] U :=
    { toFun := fun X =>
        ⟨⟨X.val.val.val, by
          have he : (movedInFixed n).mkQ X.val.val = 0 := congrArg Subtype.val X.property
          change X.val.val ∈ movedInFixed n
          exact (Submodule.Quotient.mk_eq_zero _).mp he⟩, by
            apply Subtype.ext
            change (movedAction n a _).val - X.val.val.val = 0
            rw [movedAction_apply]
            exact sub_eq_zero.mpr (by
              have he := congrArg Subtype.val (hfix X.val)
              rwa [fixedAction_apply] at he)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro X Y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : U => x.val.val) he
  have hk := (LinearMap.finrank_le_finrank_of_injective hj).trans hu
  have hr := (Submodule.finrank_le (LinearMap.range f)).trans hq
  have he := LinearMap.finrank_range_add_finrank_ker (K := F n) (V := W) (V₂ := Q) f
  change _ + _ = Module.finrank (F n) W at he
  change Module.finrank (F n) W ≤ 4
  omega

private theorem marked_outer_fixed_rank_le
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ binaryNormalizer n) (hs : fieldSwapBinary n ∈ A) (hr : 1 < rank A) :
    Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) A) ≤ 4*n := by
  let C := (binaryImage n).subgroupOf A
  have hC : C ≠ ⊥ := by
    intro hz
    have hi := OuterRank.Coefficients.elementary_relIndex_le_two n (normalizerCoverage n)
      A inferInstance hAN
    change C.index ≤ 2 at hi
    rw [hz,index_bot] at hi
    have hh := Nat.log_mono_right (b := 2) hi
    change rank A ≤ Nat.log 2 2 at hh
    norm_num at hh
    omega
  obtain ⟨b₀,hb₀⟩ := ne_bot_iff_exists_ne_one.mp hC
  let b : A := b₀.val
  have hb : b.val ∈ binaryImage n := b₀.property
  have hb1 : b ≠ 1 := fun he => hb₀ (Subtype.ext he)
  let a : FieldSections.centralizer n := ⟨b.val,hb,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm b (⟨fieldSwapBinary n,hs⟩ : A)))⟩
  have ha : a ≠ 1 := by
    intro he
    apply hb1
    apply Subtype.ext
    exact congrArg (fun x : FieldSections.centralizer n => x.val) he
  let W := fixedSpace (UnipotentRadicals.ambientAction n) A
  let Q := LinearMap.ker (fixedAction n a - LinearMap.id)
  let f : W → Q := fun X =>
    ⟨⟨X.val, (mem_fieldFixed n X.val).mpr (X.property ⟨fieldSwapBinary n,hs⟩)⟩, by
      apply Subtype.ext
      change (fixedAction n a _).val - X.val = 0
      rw [fixedAction_apply]
      exact sub_eq_zero.mpr (X.property b)⟩
  have hi : Function.Injective f := by
    intro X Y h
    exact Subtype.ext (congrArg (fun x : Q => x.val.val) h)
  have hc := Nat.card_le_card_of_injective f hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Module.natCard_eq_pow_finrank (K := F n),card_F,← pow_mul] at hc
  have hd := (pow_le_pow_iff_right₀ Nat.one_lt_two).mp hc
  apply hd.trans
  have h := Nat.mul_le_mul_left n (field_fixed_rank_le n a ha)
  simpa only [Q, Nat.mul_comm n 4] using h

/-- A noncyclic elementary subgroup containing an outer involution fixes
at most four fixed-field dimensions, also when n = 1. -/
theorem outer_fixed_rank_le
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ binaryNormalizer n) (hAL : ¬ A ≤ binaryImage n) (hr : 1 < rank A) :
    Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) A) ≤ 4*n := by
  obtain ⟨i,hiA,hiL⟩ := SetLike.not_le_iff_exists.mp hAL
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := A) i hiA)
    (fun h => hiL (h ▸ (binaryImage n).one_mem))
  obtain ⟨c,hc,hci⟩ := OuterRank.outer_involution_conjugate n (normalizerCoverage n)
    i (hAN hiA) hi2 hiL
  let B := A.map (MulAut.conj c).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (binaryNormalizer n).mul_mem ((binaryNormalizer n).mul_mem hc (hAN ha))
      ((binaryNormalizer n).inv_mem hc)
  have hs : fieldSwapBinary n ∈ B := hci ▸ mem_map_of_mem _ hiA
  have hBr : 1 < rank B := by dsimp only [B]; rwa [rank_map_conj]
  have hd := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) A c).finrank_eq
  exact hd.trans_le (marked_outer_fixed_rank_le n B hBN hs hBr)

/-- The large-actor clause of H.4.4(3) holds in the full binary normalizer,
including the outer-involution case at half-degree one. -/
theorem large_elementary_fixed_rank_le
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ binaryNormalizer n) (hr : 3*n ≤ rank A) :
    Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) A) ≤ 4*n := by
  have hn := NeZero.pos n
  by_cases hAL : A ≤ binaryImage n
  · exact inner_fixed_rank_le n A hAL (by omega)
  · exact outer_fixed_rank_le n A hAN hAL (by omega)

/-- The literal overgroup action has fixed codimension at least 5n for
an elementary actor of rank at least 3n. -/
theorem overgroup_large_elementary_fixedCodim
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : M ≤ binaryNormalizer n)
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hr : 3*n ≤ rank A) :
    5*n ≤ fixedCodim (overgroupAction n M) A := by
  let B := A.map M.subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map M.subtype
  have hB : B ≤ binaryNormalizer n := (map_subtype_le A).trans hM
  have hBr : 3*n ≤ rank B := by
    dsimp only [B]
    rwa [rank_map_injective M.subtype M.subtype_injective]
  have hd := large_elementary_fixed_rank_le n B hB hBr
  have hc := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) B
  rw [finrank_binary] at hc
  have he := fixedCodim_map_equivariant (overgroupAction n M)
    (UnipotentRadicals.ambientAction n) M.subtype (LinearEquiv.refl (ZMod 2) (Space n))
    (fun _ _ => rfl) A
  change fixedCodim (overgroupAction n M) A =
    fixedCodim (UnipotentRadicals.ambientAction n) B at he
  omega

end Representation.HermitianTensorThree.LargeActors
