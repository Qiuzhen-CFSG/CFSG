module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OuterTwists
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Displacement

/-!
# The actual Todd correction on the point-plane overlap

Tetrad parity detects the full-word displacement on the natural module of
six parts. The displacement is principal precisely for even words. Since a
Todd twist fixes the whole cocode, an inner conjugator on the overlap would
lie in that cocode; parity therefore proves that every odd-word restriction
is outer on the literal overlap, not just on the point group.

Averaging an odd word over a specified odd-order subgroup gives a fixed odd
word. Its twist belongs to the same original outer class, fixes the subgroup
pointwise, and preserves both flags and its normalizer in S intersect M.
These are the beta construction and choice used in AS91 (8.2), p.606.
The full overlap classification and edge-reversal equation remain separate.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Sporadic.Mathieu.M24LocalGeometry Representation.OneCohomology
open scoped BigOperators Pointwise

private theorem binary_neg {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (v : U) : -v = v := by
  rw [←neg_one_smul (ZMod 2) v,show (-1 : ZMod 2) = 1 from rfl,one_smul]

private theorem binary_sub_comm {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (v u : U) : v-u=u-v := by
  rw [sub_eq_add_neg,sub_eq_add_neg,binary_neg,binary_neg,add_comm]

/-- Tetrad parity of the actual full-word Todd displacement. -/
theorem toddCocycle_parity (S : Sextet) (w : Full) (g : sextetStabilizer S) :
    (sextetCocodeParity S (toddCocycle w g.val)).val =
      (BinaryPermutation.constants (SextetPart S)).mkQ
        (sextetParity S w - BinaryPermutation.representation (SextetPart S)
          (sextetPartPerm S g) (sextetParity S w)) := by
  obtain ⟨v,hv,he⟩ := toddCocycle_representative w g.val
  rw [he,sextetCocodeParity_mk,hv,map_sub,sextetParity_equivariant]

/-- The restriction to a native sextet has a principal top displacement
exactly for even full words. -/
theorem toddCocycle_parity_principal_iff (S : Sextet) (w : Full) :
    (∃ v : BinaryPermutation.natural (SextetPart S), ∀ g : sextetStabilizer S,
      sextetCocodeParity S (toddCocycle w g.val) =
        BinaryPermutation.naturalRepresentation (SextetPart S) (sextetPartPerm S g) v - v) ↔
      w ∈ Core := by
  constructor
  · rintro ⟨v,hv⟩
    have he : principal (BinaryPermutation.alternatingNaturalRepresentation (SextetPart S)) v =
        BinaryPermutation.naturalDisplacement (SextetPart S) (sextetParity S w) := by
      apply Subtype.ext
      funext s
      obtain ⟨g,hg⟩ := SextetLayers.CoordinateTransport.nativePartPerm_surjective S s.val
      apply Subtype.ext
      have hh := congrArg Subtype.val (hv g).symm
      rw [toddCocycle_parity,hg] at hh
      exact hh.trans (congrArg (BinaryPermutation.constants (SextetPart S)).mkQ
        (binary_sub_comm _ _))
    have hw := (BinaryPermutation.naturalDisplacement_principal_iff (SextetPart S)
      (by rw [Nat.card_eq_fintype_card,card_sextetPart]; decide)
      (by rw [card_sextetPart]; decide) (sextetParity S w)).mp ⟨v,he⟩
    change (∑ B : SextetPart S, sextetParity S w B) = 0 at hw
    rw [sextetParity_sum] at hw
    exact hw
  · intro hw
    refine ⟨sextetCocodeParity S (codeInCore.mkQ ⟨w,hw⟩),fun g => ?_⟩
    rw [toddCocycle_even (⟨w,hw⟩ : Core),map_sub,sextetCocodeParity_equivariant]
    exact binary_sub_comm _ _

/-- Addition of full words is composition of the actual Todd automorphisms. -/
theorem toddTwist_add (w u : Full) : toddTwist (w+u) = toddTwist w * toddTwist u := by
  have hc (g : M24) : toddCocycle (w+u) g = toddCocycle w g + toddCocycle u g := by
    apply cocodeIntoFull_injective
    simp only [map_add,toddCocycle_intoFull]
    abel
  apply MulEquiv.ext
  intro g
  rw [MulAut.mul_apply,toddTwist_apply,toddTwist_apply,toddTwist_apply]
  apply SemidirectProduct.ext
  · change g.left * Multiplicative.ofAdd (toddCocycle (w+u) g.right) =
      (g.left * Multiplicative.ofAdd (toddCocycle u g.right)) *
        Multiplicative.ofAdd (toddCocycle w g.right)
    rw [hc]
    change g.left * (Multiplicative.ofAdd (toddCocycle w g.right) *
      Multiplicative.ofAdd (toddCocycle u g.right)) = _
    ac_rfl
  · rfl

/-- All odd full words give the same outer class, with a literal cocode conjugator. -/
theorem toddTwist_odd_class (w : Full) (hw : w ∉ Core) :
    ∃ v : Cocode, toddTwist w =
      MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd v) : ToddGroup) *
        toddTwist toddOddWord := by
  have he : w+toddOddWord ∈ Core := by
    change BinaryPermutation.augmentation (Fin 24) (w+toddOddWord) = 0
    rw [map_add]
    have hw1 : BinaryPermutation.augmentation (Fin 24) w = 1 := by
      have hc : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
      exact (hc _).resolve_left hw
    have ho1 : BinaryPermutation.augmentation (Fin 24) toddOddWord = 1 := by
      have hc : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
      exact (hc _).resolve_left toddOddWord_not_even
    rw [hw1,ho1]; decide
  refine ⟨codeInCore.mkQ ⟨w+toddOddWord,he⟩,?_⟩
  rw [←toddTwist_even (⟨w+toddOddWord,he⟩ : Core),←toddTwist_add]
  congr 1
  have hz : toddOddWord+toddOddWord=0 := by
    nth_rw 1 [←binary_neg toddOddWord]
    exact neg_add_cancel toddOddWord
  rw [add_assoc,hz,add_zero]

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

theorem pointTwist_coordinates (w : Full) (m : a.P.M) :
    a.P.toddEquiv.symm (pointTwist a w m) = toddTwist w (a.P.toddEquiv.symm m) := by
  rw [pointTwist_eq_congr]
  exact a.P.toddEquiv.symm_apply_apply _

/-- The actual point-side realization of I = M intersect H. -/
abbrev pointOverlap := (centralizer z).subgroupOf a.P.M

/-- Restriction of the full-word automorphism to the literal overlap. -/
noncomputable def overlapToddTwist (w : Full) : MulAut (pointOverlap a) :=
  ((pointTwist a w).subgroupMap (pointOverlap a)).trans
    (MulEquiv.subgroupCongr (pointTwist_overlap a w))

theorem overlapToddTwist_val (w : Full) (x : pointOverlap a) :
    (overlapToddTwist a w x).val = pointTwist a w x.val := rfl

private noncomputable def overlapVector (v : ToddVector) : pointOverlap a :=
  ⟨a.P.toddEquiv (SemidirectProduct.inl v), by
    apply (a.point_plane_todd_overlap _).mpr
    change (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inl v))).right • _ = _
    rw [a.P.toddEquiv.symm_apply_apply]
    exact one_smul _ _⟩

private noncomputable def overlapComplement (s : sextetStabilizer a.sextet) : pointOverlap a :=
  ⟨a.P.toddEquiv (SemidirectProduct.inr s.val), by
    apply (a.point_plane_todd_overlap _).mpr
    change (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inr s.val))).right • _ = _
    rw [a.P.toddEquiv.symm_apply_apply]
    exact s.property⟩

/-- Innerness on I already forces even parity. The proof fixes the actual
cocode pointwise, then detects the displacement on the same six native parts. -/
theorem overlapToddTwist_inner_iff (w : Full) :
    (∃ x : pointOverlap a, overlapToddTwist a w = MulAut.conj x) ↔ w ∈ Core := by
  constructor
  · rintro ⟨x,hx⟩
    let t : ToddGroup := a.P.toddEquiv.symm x.val
    have hv (v : ToddVector) :
        t * SemidirectProduct.inl v * t⁻¹ = SemidirectProduct.inl v := by
      have hh := MulEquiv.congr_fun hx (overlapVector a v)
      have hh' := congrArg (fun n : pointOverlap a => a.P.toddEquiv.symm n.val) hh
      rw [overlapToddTwist_val,pointTwist_coordinates] at hh'
      change toddTwist w (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inl v))) =
        a.P.toddEquiv.symm (x.val * a.P.toddEquiv (SemidirectProduct.inl v) * x.val⁻¹) at hh'
      simpa only [map_mul,map_inv,MulEquiv.symm_apply_apply,toddTwist_vector] using hh'.symm
    have ht : t.right = 1 := by
      apply cocode_faithful
      apply LinearMap.ext
      intro v
      have hh := congrArg SemidirectProduct.left (mul_inv_eq_iff_eq_mul.mp (hv (Multiplicative.ofAdd v)))
      change t.left * toddAction t.right (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd v * toddAction 1 t.left at hh
      rw [map_one,MulAut.one_apply,mul_comm (Multiplicative.ofAdd v)] at hh
      rw [map_one]
      exact congrArg Multiplicative.toAdd (mul_left_cancel hh)
    apply (toddCocycle_parity_principal_iff a.sextet w).mp
    refine ⟨sextetCocodeParity a.sextet t.left.toAdd,fun s => ?_⟩
    have hh := MulEquiv.congr_fun hx (overlapComplement a s)
    have hh' := congrArg (fun n : pointOverlap a => a.P.toddEquiv.symm n.val) hh
    have he : toddTwist w (SemidirectProduct.inr s.val) =
        t * SemidirectProduct.inr s.val * t⁻¹ := by
      rw [overlapToddTwist_val,pointTwist_coordinates] at hh'
      change toddTwist w (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inr s.val))) =
        a.P.toddEquiv.symm (x.val * a.P.toddEquiv (SemidirectProduct.inr s.val) * x.val⁻¹) at hh'
      simpa only [map_mul,map_inv,MulEquiv.symm_apply_apply] using hh'
    rw [toddTwist_apply] at he
    have hh := congrArg (fun y : ToddGroup => y.left.toAdd) he
    simp only [SemidirectProduct.mul_left,
      SemidirectProduct.mul_right,SemidirectProduct.left_inr,SemidirectProduct.right_inr,
      SemidirectProduct.inv_left,ht,map_one,MulAut.one_apply,mul_one,one_mul,inv_one] at hh
    change toddCocycle w s.val = t.left.toAdd + cocodeRepresentation s.val (-t.left.toAdd) at hh
    rw [hh,map_neg,←sub_eq_add_neg,map_sub,sextetCocodeParity_equivariant]
    exact binary_sub_comm _ _
  · intro hw
    refine ⟨overlapVector a (Multiplicative.ofAdd (codeInCore.mkQ ⟨w,hw⟩)),?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply a.P.toddEquiv.symm.injective
    rw [overlapToddTwist_val,pointTwist_coordinates]
    change toddTwist w (a.P.toddEquiv.symm x.val) =
      a.P.toddEquiv.symm ((overlapVector a (Multiplicative.ofAdd (codeInCore.mkQ ⟨w,hw⟩))).val *
        x.val * (overlapVector a (Multiplicative.ofAdd (codeInCore.mkQ ⟨w,hw⟩))).val⁻¹)
    rw [toddTwist_even (⟨w,hw⟩ : Core),MulAut.conj_apply,map_mul,map_mul,map_inv]
    simp only [overlapVector,MulEquiv.symm_apply_apply]

/-- In particular beta_I is outer, not only beta on the whole Todd group. -/
theorem overlapToddOddTwist_not_inner :
    ¬ ∃ x : pointOverlap a, overlapToddTwist a toddOddWord = MulAut.conj x := by
  rw [overlapToddTwist_inner_iff]
  exact toddOddWord_not_even

/-- Every Todd twist has displacement in the original point radical. -/
theorem pointTwist_displacement (w : Full) (m : a.P.M) :
    ((pointTwist a w m * m⁻¹ : a.P.M) : G) ∈ a.P.E := by
  have he : pointTwist a w m * m⁻¹ ∈ a.P.projection.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,pointTwist_projection,mul_inv_cancel]
  rwa [a.P.projection_ker] at he

/-- A subgroup containing E is preserved with its literal embedding in M. -/
theorem pointTwist_subgroup (w : Full) (U : Subgroup G) (hU : a.P.E ≤ U) :
    (U.subgroupOf a.P.M).map (pointTwist a w).toMonoidHom = U.subgroupOf a.P.M := by
  have hm (m : a.P.M) (hm : m.val ∈ U) : (pointTwist a w m).val ∈ U := by
    have he := U.mul_mem (hU (pointTwist_displacement a w m)) hm
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,inv_mul_cancel_right] using he
  apply le_antisymm
  · rintro _ ⟨m,hm',rfl⟩
    exact hm m hm'
  · intro m hm'
    have hs : pointTwist a w (pointTwist a w m) = m := by
      have hh := MulEquiv.congr_fun (pointTwist_sq a w) m
      exact hh
    exact ⟨pointTwist a w m,hm m hm',hs⟩

/-- Both earlier flags are preserved by the same full-word correction. -/
theorem pointTwist_flags (w : Full) :
    ((centralizer z).subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
        (centralizer z).subgroupOf a.P.M ∧
    (a.L.G₂.subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
        a.L.G₂.subgroupOf a.P.M ∧
    (a.d.S.subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
        a.d.S.subgroupOf a.P.M := by
  refine ⟨pointTwist_overlap a w,pointTwist_subgroup a w _ ?_,
    pointTwist_subgroup a w _ a.E_le_S⟩
  have hS : a.d.S ≤ a.L.G₂ := by
    rw [←a.S_image]
    rintro _ ⟨s,_,rfl⟩
    exact s.property
  exact a.E_le_S.trans hS

/-- Choose an odd full word fixed by an arbitrary specified odd-order
subgroup of the original point group. This averages its actual M24 action. -/
theorem exists_odd_fixed_word (Y : Subgroup a.P.M) (hY : Odd (Nat.card Y)) :
    ∃ w : Full, w ∉ Core ∧ ∀ y : Y, fullRepresentation (a.P.projection y.val) w = w := by
  classical
  let := Fintype.ofFinite Y
  let w : Full := ∑ y : Y, fullRepresentation (a.P.projection y.val) toddOddWord
  have ho : BinaryPermutation.augmentation (Fin 24) toddOddWord = 1 := by
    have hc : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
    exact (hc _).resolve_left toddOddWord_not_even
  have hw : BinaryPermutation.augmentation (Fin 24) w = 1 := by
    change BinaryPermutation.augmentation (Fin 24)
      (∑ y : Y, fullRepresentation (a.P.projection y.val) toddOddWord) = 1
    rw [map_sum]
    have he (y : Y) : BinaryPermutation.augmentation (Fin 24)
        (fullRepresentation (a.P.projection y.val) toddOddWord) = 1 := by
      exact (BinaryPermutation.augmentation_permute (Fin 24) (a.P.projection y.val).val toddOddWord).trans ho
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact (Nat.card_eq_fintype_card (α := Y) ▸ hY).natCast_zmod_two
  refine ⟨w,fun he => one_ne_zero (hw.symm.trans he),fun y => ?_⟩
  change fullRepresentation (a.P.projection y.val)
    (∑ x : Y, fullRepresentation (a.P.projection x.val) toddOddWord) = _
  rw [map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun x => by
    change fullRepresentation (a.P.projection y.val)
      (fullRepresentation (a.P.projection x.val) toddOddWord) =
        fullRepresentation (a.P.projection (y*x).val) toddOddWord
    rw [Subgroup.coe_mul,map_mul,map_mul,Module.End.mul_apply])

/-- A fixed full word makes the actual Todd automorphism fix the chosen
subgroup pointwise, including the cocode components of its elements. -/
theorem pointTwist_fixes_of_fixed_word (w : Full) (m : a.P.M)
    (hm : fullRepresentation (a.P.projection m) w = w) : pointTwist a w m = m := by
  apply a.P.toddEquiv.symm.injective
  rw [pointTwist_coordinates,toddTwist_apply]
  apply SemidirectProduct.ext
  · change (a.P.toddEquiv.symm m).left *
      Multiplicative.ofAdd (toddCocycle w (a.P.projection m)) = (a.P.toddEquiv.symm m).left
    rw [toddCocycle_of_fixed_word w _ hm]
    exact mul_one _
  · rfl

/-- The selected correction preserves the exact normalizer inside S intersect M. -/
theorem pointTwist_relative_normalizer (w : Full) (Y : Subgroup a.P.M)
    (hY : ∀ y : Y, pointTwist a w y.val = y.val) :
    ((a.d.S.subgroupOf a.P.M) ⊓ normalizer (Y : Set a.P.M)).map
        (pointTwist a w).toMonoidHom =
      (a.d.S.subgroupOf a.P.M) ⊓ normalizer (Y : Set a.P.M) := by
  have he : Y.map (pointTwist a w).toMonoidHom = Y := by
    ext y
    constructor
    · rintro ⟨v,hv,rfl⟩
      change pointTwist a w v ∈ Y
      rw [hY ⟨v,hv⟩]
      exact hv
    · intro hy
      exact ⟨y,hy,hY ⟨y,hy⟩⟩
  rw [Subgroup.map_inf _ _ _ (pointTwist a w).injective,
    (pointTwist_flags a w).2.2,map_equiv_normalizer_eq,he]

/-- Beta can be chosen in its original outer class to fix the specified
odd subgroup and preserve both flags and the literal relative normalizer.
No local comparison maps or edge-compatibility premise is supplied. -/
theorem exists_odd_point_correction (Y : Subgroup a.P.M) (hY : Odd (Nat.card Y)) :
    ∃ (w : Full) (v : Cocode), w ∉ Core ∧
      pointTwist a w =
        MulAut.conj (a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v))) *
          pointTwist a toddOddWord ∧
      pointTwist a w ^ 2 = 1 ∧
      (∀ y : Y, pointTwist a w y.val = y.val) ∧
      (¬ ∃ x : pointOverlap a, overlapToddTwist a w = MulAut.conj x) ∧
      ((centralizer z).subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
        (centralizer z).subgroupOf a.P.M ∧
      (a.L.G₂.subgroupOf a.P.M).map (pointTwist a w).toMonoidHom = a.L.G₂.subgroupOf a.P.M ∧
      ((a.d.S.subgroupOf a.P.M) ⊓ normalizer (Y : Set a.P.M)).map
          (pointTwist a w).toMonoidHom =
        (a.d.S.subgroupOf a.P.M) ⊓ normalizer (Y : Set a.P.M) := by
  obtain ⟨w,hw,hfix⟩ := exists_odd_fixed_word a Y hY
  obtain ⟨v,hv⟩ := toddTwist_odd_class w hw
  have he : pointTwist a w =
      MulAut.conj (a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v))) *
        pointTwist a toddOddWord := by
    rw [pointTwist_eq_congr,hv,map_mul,MulAut.congr_conj,←pointTwist_eq_congr]
  have hf (y : Y) := pointTwist_fixes_of_fixed_word a w y.val (hfix y)
  exact ⟨w,v,hw,he,pointTwist_sq a w,hf,
    fun hh => hw ((overlapToddTwist_inner_iff a w).mp hh),
    (pointTwist_flags a w).1,(pointTwist_flags a w).2.1,
    pointTwist_relative_normalizer a w Y hf⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
