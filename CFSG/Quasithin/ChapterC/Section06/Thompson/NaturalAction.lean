module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FullCentralizer
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Natural-action bounds in the original Thompson extension

The full normalizer action retains the original module kernel. Its coefficient
homomorphism has image of order at most two on an elementary subgroup. A
linear involution normalizing the upper-root group fixes its natural line,
hence is an upper-root actor itself. The same calculation places the full
centralizer of the two-core intersection in the Baumann subgroup.
The quotient size of either core by their intersection is the field order.

Source: Aschbacher–Smith C.6.1, the Thompson argument on printed p.165,
using the C.5.6(7) natural coordinates and centralizer identities.
-/

public section

open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}
variable {E F : Type*} [Field E] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite G] in
private theorem thompson_count (Q A : Subgroup G) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem thompson_root_apply (d : FullNaturalModel R K F) (t : Multiplicative F)
    (w : Multiplicative (Fin 2 → F)) :
    (d.tau (upperUnipotentHom F t) w).toAdd = ![w.toAdd 0 + t.toAdd * w.toAdd 1,w.toAdd 1] := by
  rw [d.natural]
  ext i
  fin_cases i <;> simp [upperUnipotentHom,transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem thompson_fixed_lift (h : Setup R K E) (d : FullNaturalModel R K F)
    (s : S R) (u : U K)
    (he : d.projection (moduleConjugate h.coordinates.normalizes s u) = d.projection u) :
    moduleConjugate h.coordinates.normalizes s u = u := by
  apply h.fixedLift
  have hc : (moduleConjugate h.coordinates.normalizes s u / u : U K) ∈ d.projection.ker := by
    change d.projection _ = 1
    rw [map_div,he,div_self']
  have hk := (d.kernel _).mp hc
  have hq := (h.coordinates.projection_kernel _).mpr hk
  rw [map_div,div_eq_one] at hq
  exact hq

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
/-- Every full root-line vector has a lift in both of the actual cores. -/
theorem Setup.thompson_root_line_lift (h : Setup R K E) (d : FullNaturalModel R K F)
    {x : G} (hx : x ∈ normalizer (R : Set G)) (c : F) :
    ∃ u : U K, d.projection u = Multiplicative.ofAdd ![c,0] ∧
      (u : G) ∈ Q R K ⊓ (Q R K).map (MulAut.conj x⁻¹).toMonoidHom := by
  obtain ⟨u,hu⟩ := d.surjective (Multiplicative.ofAdd ![c,0])
  refine ⟨u,hu, h.module_le_core u.property, ?_⟩
  rw [h.conjugate_core hx]
  refine ⟨h.module_le u.property,?_⟩
  apply centralizer_le (h.conjugate_le hx)
  intro s hs
  let s₀ : S R := ⟨s,hs⟩
  let sN : normalizer (K : Set G) := inclusion d.normalizes s₀
  have hm : d.action sN ∈ (upperUnipotent F).map d.tau :=
    d.image ▸ mem_map_of_mem d.action hs
  obtain ⟨g,⟨t,rfl⟩,he⟩ := hm
  have hf : d.projection (moduleConjugate h.coordinates.normalizes s₀ u) = d.projection u := by
    have hh := d.equivariant sN u
    change d.action sN (d.projection u) = d.projection (moduleConjugate h.coordinates.normalizes s₀ u) at hh
    rw [←hh,←he,hu]
    apply Multiplicative.toAdd.injective
    rw [thompson_root_apply]
    simp
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (thompson_fixed_lift h d s₀ u hf))

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
/-- An upper-root action differs from a Baumann element by the actual module kernel. -/
theorem FullNaturalModel.mem_baumann_of_upper (d : FullNaturalModel R K F)
    (hRK : R ≤ normalizer (K : Set G))
    (hker : R ⊓ centralizer (U K : Set G) ≤ S R)
    (a : R) (ha : d.action (inclusion hRK a) ∈ (upperUnipotent F).map d.tau) :
    (a : G) ∈ S R := by
  rw [←d.image] at ha
  obtain ⟨s,hs,he⟩ := ha
  have hc : s⁻¹ * inclusion hRK a ∈ d.action.ker := by
    change d.action (s⁻¹ * inclusion hRK a) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hcU : (s : G)⁻¹ * a ∈ centralizer (U K : Set G) := by
    exact (show s⁻¹ * inclusion hRK a ∈ (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) from d.action_kernel ▸ hc)
  have hcR : (s : G)⁻¹ * a ∈ R := R.mul_mem (R.inv_mem (show (s : G) ∈ R from (show S R ≤ R from inf_le_left) hs)) a.property
  have hh := (S R).mul_mem hs (hker ⟨hcR,hcU⟩)
  change (s : G) * ((s : G)⁻¹ * (a : G)) ∈ S R at hh
  simpa only [mul_inv_cancel_left] using hh

omit [Finite G] [Finite F] in
/-- In the original two-group, fixing the intersection of the natural cores
forces membership in the Baumann group. -/
theorem Setup.thompson_intersection_centralizer (h : Setup R K E)
    (d : FullNaturalModel R K F) (hR : IsPGroup 2 R)
    (hRK : R ≤ normalizer (K : Set G))
    (hker : R ⊓ centralizer (U K : Set G) ≤ S R)
    {x : G} (hx : x ∈ normalizer (R : Set G)) :
    R ⊓ centralizer ((Q R K ⊓ (Q R K).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ S R := by
  rintro a ⟨haR,haI⟩
  let aN : normalizer (K : Set G) := ⟨a,hRK haR⟩
  let π := (automorphismRepresentation d.action.range).comp d.action.rangeRestrict
  have hfix (c : F) : π aN ![c,0] = ![c,0] := by
    obtain ⟨u,hu,huI⟩ := h.thompson_root_line_lift d hx c
    have he : normalizerConjugate aN u = u := by
      apply Subtype.ext
      change a * (u : G) * a⁻¹ = u
      rw [←haI (u : G) huI,mul_inv_cancel_right]
    change (d.action aN (Multiplicative.ofAdd ![c,0])).toAdd = _
    rw [←hu,d.equivariant,he,hu]
    rfl
  obtain ⟨n,hn⟩ := hR.exists_pow_pow_eq_one (⟨a,haR⟩ : R)
  have hnN : aN ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun r : R => (r : G)) hn)
  obtain ⟨t,ht⟩ := natural_fixed_line_two_element π aN (d.semilinear aN) hfix n hnN
  apply d.mem_baumann_of_upper hRK hker ⟨a,haR⟩
  have he : d.action aN = d.tau (upperUnipotentHom F (Multiplicative.ofAdd t)) := by
    apply MulEquiv.ext
    intro w
    apply Multiplicative.toAdd.injective
    exact (ht w.toAdd).trans (thompson_root_apply d (Multiplicative.ofAdd t) w).symm
  change d.action aN ∈ _
  rw [he]
  exact mem_map_of_mem d.tau ⟨Multiplicative.ofAdd t,rfl⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
open Subgroup Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}
variable {E F : Type*} [Field E] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite G] [Finite F] in
/-- A linear involution in the original Sylow normalizer is an upper root. -/
theorem FullNaturalModel.linear_involution_mem_baumann (d : FullNaturalModel R K F)
    (hRK : R ≤ normalizer (K : Set G))
    (hker : R ⊓ centralizer (U K : Set G) ≤ S R)
    (a : R) (ha2 : a ^ 2 = 1)
    (hlin : ∀ (c : F) (v : Fin 2 → F), (d.action (inclusion hRK a) (Multiplicative.ofAdd (c • v))).toAdd =
      c • (d.action (inclusion hRK a) (Multiplicative.ofAdd v)).toAdd) :
    (a : G) ∈ S R := by
  let N := normalizer (K : Set G)
  let aN : N := inclusion hRK a
  let f := d.action aN
  let π := (automorphismRepresentation d.action.range).comp d.action.rangeRestrict
  let e₀ : Multiplicative (Fin 2 → F) := Multiplicative.ofAdd ![1,0]
  let B := (upperUnipotent F).map d.tau
  have haNorm : f ∈ normalizer (B : Set (MulAut (Multiplicative (Fin 2 → F)))) := by
    dsimp only [B]
    rw [←d.image]
    apply le_normalizer_map d.action
    apply mem_map_of_mem
    apply mem_normalizer_iff.mpr
    intro s
    change (s : G) ∈ S R ↔ (a : G) * (s : G) * (a : G)⁻¹ ∈ S R
    exact mem_normalizer_iff.mp (Stellmacher.normalizer_le_normalizer_baumann R (R.le_normalizer a.property)) (s : G)
  let z := d.tau (upperUnipotentHom F (Multiplicative.ofAdd 1))
  have hz : z ∈ B := mem_map_of_mem d.tau ⟨Multiplicative.ofAdd 1,rfl⟩
  have hconj : f⁻¹ * z * f ∈ B := by
    have hh := (mem_normalizer_iff.mp ((normalizer (B : Set (MulAut (Multiplicative (Fin 2 → F))))).inv_mem haNorm) z).mp hz
    simpa only [inv_inv] using hh
  obtain ⟨g,⟨t,rfl⟩,he⟩ := hconj
  have hrootFix : d.tau (upperUnipotentHom F t) e₀ = e₀ := by
    apply Multiplicative.toAdd.injective
    rw [thompson_root_apply]
    simp [e₀]
  have hzfix : z (f e₀) = f e₀ := by
    have hh := congrArg (fun k : MulAut (Multiplicative (Fin 2 → F)) => k e₀) he
    change d.tau (upperUnipotentHom F t) e₀ = f.symm (z (f e₀)) at hh
    rw [hrootFix] at hh
    simpa only [f.apply_symm_apply] using (congrArg f hh).symm
  have hsecond : (f e₀).toAdd 1 = 0 := by
    have hh := congrArg (fun w : Multiplicative (Fin 2 → F) => w.toAdd 0) hzfix
    dsimp only [z] at hh
    rw [thompson_root_apply] at hh
    simpa using hh
  let c := (f e₀).toAdd 0
  have hform : (f e₀).toAdd = ![c,0] := by
    ext i
    fin_cases i
    · rfl
    · exact hsecond
  have hf2 : f * f = 1 := by
    calc
      f * f = d.action (inclusion hRK (a * a)) := by simp only [map_mul]; rfl
      _ = d.action (inclusion hRK 1) := congrArg (fun r : R => d.action (inclusion hRK r)) (by simpa only [pow_two] using ha2)
      _ = 1 := by rw [map_one,map_one]
  have hsquare : c * c = 1 := by
    have hh := congrArg (fun k : MulAut (Multiplicative (Fin 2 → F)) => (k e₀).toAdd 0) hf2
    change (f (f e₀)).toAdd 0 = 1 at hh
    have hc : f e₀ = Multiplicative.ofAdd (c • (![1,0] : Fin 2 → F)) := by
      apply Multiplicative.toAdd.injective
      rw [hform]
      ext i
      fin_cases i <;> simp
    rw [hc] at hh
    change (d.action (inclusion hRK a) (Multiplicative.ofAdd (c • (![1,0] : Fin 2 → F)))).toAdd 0 = 1 at hh
    rw [hlin] at hh
    exact hh
  have hc1 : c = 1 := by
    have hh : c ^ 2 = 1 := by simpa only [pow_two] using hsquare
    rcases sq_eq_one_iff.mp hh with hh | hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  have hfix (c' : F) : π aN ![c',0] = ![c',0] := by
    have hvec : (![c',0] : Fin 2 → F) = c' • ![1,0] := by ext i; fin_cases i <;> simp
    change (d.action (inclusion hRK a) (Multiplicative.ofAdd ![c',0])).toAdd = _
    rw [hvec,hlin]
    change c' • (f e₀).toAdd = _
    rw [hform,hc1]
  have haN2 : aN ^ (2 ^ 1) = 1 := by
    change inclusion hRK (a ^ (2 ^ 1)) = 1
    norm_num only [pow_one] at *
    rw [ha2,map_one]
  obtain ⟨t,ht⟩ := natural_fixed_line_two_element π aN (d.semilinear aN) hfix 1 haN2
  apply d.mem_baumann_of_upper hRK hker a
  have he : f = d.tau (upperUnipotentHom F (Multiplicative.ofAdd t)) := by
    apply MulEquiv.ext
    intro w
    apply Multiplicative.toAdd.injective
    exact (ht w.toAdd).trans (thompson_root_apply d (Multiplicative.ofAdd t) w).symm
  change f ∈ _
  rw [he]
  exact mem_map_of_mem d.tau ⟨Multiplicative.ofAdd t,rfl⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
open Subgroup Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}
variable {E F : Type*} [Field E] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The coefficient map bounds every elementary subgroup of R modulo Baum(R). -/
theorem FullNaturalModel.elementary_card_bound (d : FullNaturalModel R K F)
    (hRK : R ≤ normalizer (K : Set G))
    (hker : R ⊓ centralizer (U K : Set G) ≤ S R)
    (A : Subgroup G) (hAR : A ≤ R) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 2 * Nat.card (A ⊓ S R : Subgroup G) := by
  let : IsElementaryAbelian 2 A := hA
  let π := (automorphismRepresentation d.action.range).comp d.action.rangeRestrict
  let φ : A →* (F ≃+* F) :=
    (Representation.SL2NaturalOffenders.fieldAction π d.semilinear).comp
      ((inclusion hRK).comp (inclusion hAR))
  have hlin (a : φ.ker) : (a.val : G) ∈ S R := by
    apply d.linear_involution_mem_baumann hRK hker (inclusion hAR a.val)
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (A := A) a.val a.val.property
    · have hh := (Representation.SL2NaturalOffenders.fieldAction_eq_one_iff π d.semilinear
        (inclusion hRK (inclusion hAR a.val))).mp a.property
      exact hh
  let j : φ.ker → (A ⊓ S R : Subgroup G) := fun a => ⟨a.val,a.val.property,hlin a⟩
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (A ⊓ S R : Subgroup G) => (z : G)) he
  exact (Representation.SL2NaturalOffenders.card_le_two_mul_fieldAction_ker A hA φ).trans
    (Nat.mul_le_mul_left 2 (Nat.card_le_card_of_injective j hj))

omit [Finite G] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
/-- The marked natural field is exactly the quotient size of S over its core. -/
theorem Setup.thompson_core_index (h : Setup R K E) (d : FullNaturalModel R K F) :
    (Q R K).relIndex (S R) = Nat.card F := by
  have hi := relIndex_ker ((S R).subgroupOf (normalizer (K : Set G))) d.action
  rw [d.action_kernel,d.image,card_map_of_injective (natural_action_injective d.tau d.natural),card_upperUnipotent] at hi
  simpa only [relIndex_subgroupOf d.normalizes,h.core,inf_relIndex_left] using hi

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
/-- The two-core intersection has natural-field codimension in either core. -/
theorem Setup.thompson_core_intersection_card (h : Setup R K E) (d : FullNaturalModel R K F)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    Nat.card (Q R K ⊓ (Q R K).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) * Nat.card F =
      Nat.card (Q R K) := by
  let Q' := (Q R K).map (MulAut.conj x⁻¹).toMonoidHom
  have hQS : Q R K ≤ S R := h.core ▸ inf_le_left
  have hQ'S : Q' ≤ S R := (h.conjugate_core hx).le.trans inf_le_left
  have hN : S R ≤ normalizer (Q R K : Set G) :=
    (show S R ≤ K ⊔ S R from le_sup_right).trans
      ((K ⊔ S R).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ S R) (pCore 2 (K ⊔ S R : Subgroup G))))
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q R K) Q' (hQ'S.trans hN)
  have hc := thompson_count (Q R K) (S R)
  rw [inf_eq_left.mpr hQS,h.thompson_core_index d] at hc
  rw [card_map_of_injective (MulAut.conj x⁻¹).injective,←h.core_span hx hnc,←hc] at hp
  have he : Nat.card (Q R K) * Nat.card (Q R K) =
      Nat.card (Q R K) * (Nat.card (Q R K ⊓ Q' : Subgroup G) * Nat.card F) := by
    calc
      _ = Nat.card (Q R K ⊓ Q' : Subgroup G) * (Nat.card (Q R K) * Nat.card F) := hp
      _ = _ := by ac_rfl
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos he).symm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
