module
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpace

/-!
# Displacement avoids the fixed attachment of the whole six-letter cover

A permutation centralizing a transposition preserves its moved pair. On the
transposition-fixed hyperplane, every displacement therefore vanishes at those
two coordinates. Its span misses the constant line. The natural quotient has
no component-fixed vectors, giving the same conclusion for both whole covers.
The group application retains a central edge supplement and the literal
quotient map; no complement to the fixed line is chosen.

Source: MS93 (3.6), printed p.871, the paired Frattini calculation. The graph
application is in Exponent.Plane and Exponent.Source.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates

private theorem swap_fixed_displacement_coordinate
    (i j : Fin 6) (hij : i ≠ j) (g : Equiv.Perm (Fin 6))
    (hg : g * Equiv.swap i j = Equiv.swap i j * g)
    (v : core (Fin 6)) (hv : coreRepresentation (Fin 6) (Equiv.swap i j) v = v) :
    (coreRepresentation (Fin 6) g v - v).val i = 0 := by
  have hji : v.val j = v.val i := by
    have hh := congrArg (fun w : core (Fin 6) => w.val i) hv
    simpa only [coreRepresentation_apply,representation_apply,Equiv.symm_swap,
      Equiv.swap_apply_left] using hh
  have hmove : Equiv.swap i j (g.symm i) ≠ g.symm i := by
    intro he
    have hh := Equiv.congr_fun hg (g.symm i)
    change g (Equiv.swap i j (g.symm i)) = Equiv.swap i j (g (g.symm i)) at hh
    rw [he,g.apply_symm_apply,Equiv.swap_apply_left] at hh
    exact hij hh
  have hi := Equiv.eq_or_eq_of_swap_apply_ne_self hmove
  change v.val (g.symm i) - v.val i = 0
  rcases hi with hi | hi
  · rw [hi,sub_self]
  · rw [hi,hji,sub_self]

private theorem natural_fixed_zero (v : natural (Fin 6))
    (hv : v ∈ fixedSpace (naturalRepresentation (Fin 6)) (alternatingGroup (Fin 6))) : v = 0 := by
  let := alternatingNatural_isIrreducible (Ω := Fin 6) (by decide)
  have hf := Representation.OneCohomology.fixed_eq_bot_of_faithful_irreducible
    (alternatingNaturalRepresentation (Fin 6))
    ((naturalRepresentation_injective (Fin 6) (by decide)).comp Subtype.val_injective)
  exact (Submodule.mem_bot (R := ZMod 2)).mp (hf ▸ hv)

/-- A centralizing actor moves the transposition-fixed hyperplane away from
its component-fixed attachment, on either whole six-letter cover. -/
theorem fixed_hyperplane_movement_disjoint
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hm : SixCover.IsNaturalOrCore ρ (MonoidHom.id _))
    (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap) (B : Subgroup (Equiv.Perm (Fin 6)))
    (hB : B ≤ centralizer (zpowers t : Set (Equiv.Perm (Fin 6)))) :
    Disjoint (subspaceCommutator ρ (fixedSpace ρ (zpowers t)) B)
      (fixedSpace ρ (alternatingGroup (Fin 6))) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  rintro v ⟨hv,hvf⟩
  change v = 0
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩ <;> simp only [MonoidHom.id_apply] at hE
  · apply E.injective
    rw [map_zero]
    apply natural_fixed_zero
    intro g
    change naturalRepresentation (Fin 6) g.val (E v) = E v
    exact (hE g.val v).symm.trans (congrArg E (hvf g))
  · obtain ⟨i,j,hij,rfl⟩ := ht
    let f : V →ₗ[ZMod 2] ZMod 2 :=
      (LinearMap.proj i).comp ((core (Fin 6)).subtype.comp E.toLinearMap)
    have hzero : subspaceCommutator ρ (fixedSpace ρ (zpowers (Equiv.swap i j))) B ≤ f.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,w,hw,rfl⟩
      change (E (ρ g w - w)).val i = 0
      rw [map_sub,hE]
      apply swap_fixed_displacement_coordinate i j hij g (hB hg _ (mem_zpowers _)).symm (E w)
      exact (hE (Equiv.swap i j) w).symm.trans
        (congrArg E (hw ⟨Equiv.swap i j,mem_zpowers _⟩))
    have hc : (E v).val ∈ constants (Fin 6) :=
      (core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 6)) (E v)).mp
        (fun g => (hE g.val v).symm.trans (congrArg E (hvf g)))
    obtain ⟨c,hc⟩ := (mem_constants_iff _).mp hc
    have hi : (E v).val i = 0 := hzero hv
    have hc0 : c = 0 := (hc i).symm.trans hi
    apply E.injective
    rw [map_zero]
    apply Subtype.ext
    funext k
    exact (hc k).trans hc0

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
open NormalElementaryQuotient

/-- Lift the fixed-hyperplane calculation through the literal whole-cover
representation, retaining any central edge supplement. -/
theorem commutator_inf_fixed_of_transposition
    {M : Type*} [Group M] (W : Subgroup M) [W.Normal] [IsElementaryAbelian 2 W]
    (q : M →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set M)) (K : Subgroup M)
    (hK : K.map q = alternatingGroup (Fin 6))
    (hm : SixCover.IsNaturalOrCore (NormalElementaryQuotient.representation W q hq hk)
      (MonoidHom.id _))
    (A T S V : Subgroup M) (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hA : A.map q = zpowers t) (hTA : T ≤ centralizer (A : Set M))
    (hSA : S ≤ centralizer (A : Set M)) (hST : S ≤ centralizer (T : Set M))
    (hV : V ≤ W ⊔ S) (hVA : V ≤ centralizer (A : Set M)) :
    ⁅T,V⁆ ⊓ centralizer (K : Set M) = ⊥ := by
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let W0 := W ⊓ centralizer (A : Set M)
  have hbound : ⁅T,V⁆ ≤ ⁅T,W0⁆ := by
    apply commutator_le.mpr
    intro a ha v hv
    obtain ⟨w,hw,s,hs,he⟩ := mem_sup_of_normal_left.mp (hV hv)
    have hwA : w ∈ centralizer (A : Set M) := by
      have hh := (centralizer (A : Set M)).mul_mem (hVA hv)
        ((centralizer (A : Set M)).inv_mem (hSA hs))
      rw [←he,mul_inv_cancel_right] at hh
      exact hh
    have has : Commute a s := hST hs a ha
    rw [←he,commutatorElement_mul_right_eq_mul_conj,has.commutator_eq]
    simp only [mul_one,mul_inv_cancel_right]
    exact commutator_mem_commutator ha ⟨hw,hwA⟩
  have hCW : ⁅T,V⁆ ≤ W := hbound.trans
    ((commutator_mono le_rfl (show W0 ≤ W from inf_le_left)).trans (commutator_le_right _ _))
  have hmap : T.map q ≤ centralizer (zpowers t : Set (Equiv.Perm (Fin 6))) := by
    rw [←hA]
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact (map_mul q b a).symm.trans ((congrArg q (hTA ha b hb)).trans (map_mul q a b))
  have hWfix : subgroupSpace W W0 ≤ fixedSpace ρ (zpowers t) := by
    rw [←hA]
    exact subgroupSpace_fixed_of_centralizes W q hq hk W0 A
      (le_centralizer_iff.mp (show W0 ≤ centralizer (A : Set M) from inf_le_right))
  have hspace : subgroupSpace W ⁅T,V⁆ ≤
      subspaceCommutator ρ (fixedSpace ρ (zpowers t)) (T.map q) := by
    apply (subgroupSpace_mono W hbound).trans
    rw [commutator_comm T W0,subgroupSpace_commutator W q hq hk W0 T inf_le_left]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,hv,rfl⟩
    exact Submodule.subset_span ⟨a,ha,v,hWfix hv,rfl⟩
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨hx,hxK⟩
  let v : Additive W := Additive.ofMul ⟨x,hCW hx⟩
  have hv : v ∈ subspaceCommutator ρ (fixedSpace ρ (zpowers t)) (T.map q) := hspace hx
  have hvK : v ∈ fixedSpace ρ (alternatingGroup (Fin 6)) := by
    rw [←hK]
    exact (mem_fixedSpace_image W q hq hk K v).mpr hxK
  have hz : v = 0 := (Submodule.mem_bot (R := ZMod 2)).mp
    ((disjoint_iff.mp (fixed_hyperplane_movement_disjoint ρ hm t ht (T.map q) hmap)) ▸ ⟨hv,hvK⟩)
  exact show x = 1 from congrArg (fun w : Additive W => w.toMul.val) hz

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
