module
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore
/-!
# Cores between a diagonal component and a swapping centralizer

Restriction to the fixed diagonal maps the centralizer of the factor swap
into Aut(S). The automorphism normal form for a centerless quasisimple S
shows that this restriction has kernel {1, swap}. Any intermediate group
containing the inner diagonal consequently has p-core in the cyclic swap
subgroup, provided O_p(S)=1. A faithful component action transports this
bound to the original group, preserving the actual intermediate subgroup.

This concerns the action on the two group components, not the natural
orthogonal module: a factor swap on the latter cannot be identified with
adjugation without an additional representation comparison.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, case (3) of
14.4.2, printed pp.1006–1007.
-/

@[expose] public section
namespace ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
open Subgroup Theory.GroupTheory
variable {S : Type*} [Group S]
def swap : MulAut (S × S) := MulEquiv.prodComm
abbrev SwapCentralizer (S : Type*) [Group S] :=
  centralizer ({swap (S := S)} : Set (MulAut (S × S)))

theorem diagonal_fixed (a : SwapCentralizer S) (s : S) :
    (a.val (s,s)).2 = (a.val (s,s)).1 := by
  have h := MulEquiv.congr_fun (mem_centralizer_singleton_iff.mp a.property) (s,s)
  exact (congrArg Prod.fst h).symm

def diagonalAction : SwapCentralizer S →* MulAut S where
  toFun a := {
    toFun s := (a.val (s,s)).1
    invFun s := (a.val.symm (s,s)).1
    left_inv s := by
      have hd := diagonal_fixed a s
      have he : ((a.val (s,s)).1, (a.val (s,s)).1) = a.val (s,s) := Prod.ext rfl hd.symm
      change (a.val.symm ((a.val (s,s)).1, (a.val (s,s)).1)).1 = s
      rw [he, MulEquiv.symm_apply_apply]
    right_inv s := by
      have hd := diagonal_fixed a⁻¹ s
      have he : ((a.val.symm (s,s)).1, (a.val.symm (s,s)).1) = a.val.symm (s,s) :=
        Prod.ext rfl hd.symm
      change (a.val ((a.val.symm (s,s)).1, (a.val.symm (s,s)).1)).1 = s
      rw [he, MulEquiv.apply_symm_apply]
    map_mul' s t := by
      change (a.val ((s,s)*(t,t))).1 = _
      rw [map_mul]
      rfl }
  map_one' := by ext s; rfl
  map_mul' a b := by
    ext s
    change (a.val (b.val (s,s))).1 =
      (a.val ((b.val (s,s)).1,(b.val (s,s)).1)).1
    rw [show ((b.val (s,s)).1,(b.val (s,s)).1) = b.val (s,s) from
      Prod.ext rfl (diagonal_fixed b s).symm]

/-- Inner conjugation by a diagonal pair. -/
def diagonalInner : S →* MulAut (S × S) :=
  (MulAut.conj : (S × S) →* MulAut (S × S)).comp (MonoidHom.id S |>.prod (MonoidHom.id S))

theorem diagonalInner_mem (s : S) : diagonalInner s ∈ SwapCentralizer S := by
  apply mem_centralizer_singleton_iff.mpr
  ext x <;> rfl

theorem diagonalAction_inner (s : S) :
    diagonalAction ⟨diagonalInner s, diagonalInner_mem s⟩ = MulAut.conj s := by
  ext x
  rfl

variable [Finite S] [IsQuasisimple S]

theorem diagonalAction_kernel (hZ : center S = ⊥) (a : SwapCentralizer S)
    (ha : diagonalAction a = 1) : a.val = 1 ∨ a.val = swap := by
  have hid (s : S) : (a.val (s,s)).1 = s := MulEquiv.congr_fun ha s
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form hZ a.val with
    ⟨b,c,hbc⟩ | ⟨b,c,hbc⟩
  · have hb : b = 1 := by
      ext s
      simpa [hbc, MulEquiv.prodCongr] using hid s
    have hc : c = 1 := by
      ext s
      have hd := diagonal_fixed a s
      simpa [hbc, hb, MulEquiv.prodCongr] using hd.trans (hid s)
    left
    rw [hbc, hb, hc]
    rfl
  · have hb : b = 1 := by
      ext s
      simpa [hbc, MulEquiv.prodCongr] using hid s
    have hc : c = 1 := by
      ext s
      have hd := diagonal_fixed a s
      simpa [hbc, hb, MulEquiv.prodCongr] using hd.trans (hid s)
    right
    rw [hbc, hb, hc]
    rfl

/-- Every subgroup between the inner diagonal and the swap centralizer has
its p-core contained in the cyclic swap subgroup. -/
theorem sandwich_core_le_swap (p : ℕ) (hZ : center S = ⊥) (hp : pCore p S = ⊥)
    (A : Subgroup (MulAut (S × S))) (hA : A ≤ SwapCentralizer S)
    (hinner : diagonalInner.range ≤ A) : A.pCoreIn p ≤ zpowers (swap (S := S)) := by
  let f : A →* MulAut S := diagonalAction.comp (inclusion hA)
  have hi : ∀ s : S, MulAut.conj s ∈ f.range := by
    intro s
    refine ⟨⟨diagonalInner s, hinner ⟨s,rfl⟩⟩, ?_⟩
    exact diagonalAction_inner s
  have hcore := Theory.GroupTheory.automorphism_core_eq_bot p
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hZ) hp f.range hi
  have hm : (pCore p A).map f.rangeRestrict ≤ pCore p f.range :=
    le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
      pCore_isPGroup.map f.rangeRestrict⟩
  rintro a ⟨a, ha, rfl⟩
  have hz : f.rangeRestrict a = 1 := by
    have hz := hm (mem_map_of_mem _ ha)
    simpa only [hcore, mem_bot] using hz
  have hf : f a = 1 := congrArg Subtype.val hz
  change a.val ∈ zpowers swap
  rcases diagonalAction_kernel hZ (inclusion hA a) hf with h | h
  · rw [show a.val = 1 from h]
    exact one_mem _
  · rw [show a.val = swap from h]
    exact mem_zpowers _

/-- Transport the sandwich calculation through a faithful marked action on
 the two components. The middle subgroup may be strictly smaller than the
 involution centralizer. -/
theorem core_le_of_square_action {Q : Type*} [Group Q] [Finite Q]
    (p : ℕ) (hZ : center S = ⊥) (hp : pCore p S = ⊥)
    (ρ : Q →* MulAut (S × S)) (hρ : Function.Injective ρ)
    (i : Q) (hi : ρ i = swap) (A : Subgroup Q)
    (hAi : A ≤ centralizer ({i} : Set Q))
    (hinner : diagonalInner.range ≤ A.map ρ) : A.pCoreIn p ≤ zpowers i := by
  have hA : A.map ρ ≤ SwapCentralizer S := by
    rintro a ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← hi, ← map_mul, ← map_mul]
    exact congrArg ρ (mem_centralizer_singleton_iff.mp (hAi hb))
  have hb := sandwich_core_le_swap p hZ hp (A.map ρ) hA hinner
  rw [← map_pCoreIn_of_injective p A ρ hρ, ← hi, ← MonoidHom.map_zpowers] at hb
  exact (map_le_map_iff_of_injective hρ).mp hb
end ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
