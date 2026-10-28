module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Paired strict intersections for the five-dimensional point-core cover

Let R = ⟨(45),(01)(23),(02)(13)⟩ act on the augmentation core of the
six-letter permutation module. An R-invariant subspace containing C(R)
and of dimension at most three meets its image under the fixed even
five-cycle (12345) only in the constant line. The inverse cycle has the
same property, and both conjugate point cores generate S₆ with (45).

For a nonconstant vector in the intersection, a finite certificate finds
four independent vectors among the constant vector, the duad vector,
and the two R-orbits of that vector and its inverse image. Their sixteen
linear combinations contradict the order bound on the subspace.
This retains the entire augmentation cover, including its constant line.

Source application: Meierfrankenfeld--Stellmacher (1993), (5.5) and
(5.12)(1), printed pp.915,924--925. The compatible graph intersection
is the consumer of this full-cover calculation.
-/

public section
open Subgroup BinaryPermutation Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCorePairing
private abbrev M := Fin 6 → ZMod 2
private def shift : Equiv.Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5
private def pair45 : M := ![0,0,0,0,1,1]
private def candidates (x : M) : Fin 4 → M :=
  ![x,representation (Fin 6) shift⁻¹ x,
    representation (Fin 6) (swap01*swap23) x,
    representation (Fin 6) (swap01*swap23) (representation (Fin 6) shift⁻¹ x)]
private def word (x : M) (i j : Fin 4) (b : Fin 4 → ZMod 2) : M :=
  b 0 • (fun _ => 1) + b 1 • pair45 + b 2 • candidates x i + b 3 • candidates x j

set_option maxRecDepth 3000 in
private theorem independent_certificate : ∀ x : M,
    (∑ i, x i) = 0 → (¬ ∀ i, x i = x 0) →
    ∃ i j : Fin 4, Function.Injective (word x i j) := by
  decide +kernel



private def oneCore : core (Fin 6) := ⟨fun _ => 1,by rw [mem_core]; decide⟩
private def pairCore : core (Fin 6) := ⟨pair45,by rw [mem_core]; decide⟩
private def candidatesCore (x : core (Fin 6)) : Fin 4 → core (Fin 6) :=
  ![x,coreRepresentation (Fin 6) shift⁻¹ x,
    coreRepresentation (Fin 6) (swap01*swap23) x,
    coreRepresentation (Fin 6) (swap01*swap23) (coreRepresentation (Fin 6) shift⁻¹ x)]
private def wordCore (x : core (Fin 6)) (i j : Fin 4) (b : Fin 4 → ZMod 2) : core (Fin 6) :=
  b 0 • oneCore + b 1 • pairCore + b 2 • candidatesCore x i + b 3 • candidatesCore x j

private theorem pairCore_fixed : pairCore ∈ fixedSpace (coreRepresentation (Fin 6)) pointCore := by
  rintro ⟨g,hg⟩
  change coreRepresentation (Fin 6) g pairCore = pairCore
  rw [pointCore_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  | one => rfl
  | mul a b _ _ ha hb =>
    rw [map_mul,Module.End.mul_apply,hb,ha]
  | inv a _ ha =>
    have hh := congrArg (coreRepresentation (Fin 6) a⁻¹) ha
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh.symm

private theorem oneCore_fixed : oneCore ∈ fixedSpace (coreRepresentation (Fin 6)) pointCore := by
  intro g
  rfl

private theorem intersection_le_constants (W : Submodule (ZMod 2) (core (Fin 6)))
    (hsmall : Nat.card W < 16)
    (hfixed : fixedSpace (coreRepresentation (Fin 6)) pointCore ≤ W)
    (hinv : ∀ r ∈ pointCore, ∀ x ∈ W, coreRepresentation (Fin 6) r x ∈ W) :
    W ⊓ W.map (coreRepresentation (Fin 6) shift) ≤ coreConstants (Ω := Fin 6) := by
  intro x hx
  change x.val ∈ constants (Fin 6)
  apply (mem_constants_iff x.val).mpr
  by_contra hn
  have hn' : ¬ ∀ i, x.val i = x.val 0 := by
    intro hh
    exact hn ⟨x.val 0,hh⟩
  obtain ⟨i,j,hij⟩ := independent_certificate x.val ((mem_core (Fin 6) x.val).mp x.property) hn'
  have hback : coreRepresentation (Fin 6) shift⁻¹ x ∈ W := by
    obtain ⟨y,hy,he⟩ := hx.2
    rw [←he,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    exact hy
  have hr : swap01*swap23 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hcan (k : Fin 4) : candidatesCore x k ∈ W := by
    fin_cases k
    · exact hx.1
    · exact hback
    · exact hinv _ hr x hx.1
    · exact hinv _ hr _ hback
  have hword (b : Fin 4 → ZMod 2) : wordCore x i j b ∈ W :=
    W.add_mem (W.add_mem (W.add_mem
      (W.smul_mem _ (hfixed oneCore_fixed)) (W.smul_mem _ (hfixed pairCore_fixed)))
      (W.smul_mem _ (hcan i))) (W.smul_mem _ (hcan j))
  let f : (Fin 4 → ZMod 2) → W := fun b => ⟨wordCore x i j b,hword b⟩
  have hfi : Function.Injective f := by
    intro b c he
    apply hij
    have hcanval (k : Fin 4) : (candidatesCore x k).val = candidates x.val k := by
      fin_cases k <;> rfl
    simpa only [f,wordCore,Submodule.coe_add,Submodule.coe_smul,oneCore,pairCore,hcanval,word]
      using congrArg (fun v : W => v.val.val) he
  have hh := Nat.card_le_card_of_injective f hfi
  have hh' : 16 ≤ Nat.card W := by
    norm_num only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,ZMod.card] at hh
    exact hh
  omega

private theorem shift_even : shift ∈ alternatingGroup (Fin 6) := by decide +kernel

private theorem crossing_generate (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hn : ¬ Commute swap45 t) : pointCore ⊔ zpowers t = ⊤ := by
  have hcore : (subspaceStabilizer (naturalRepresentation (Fin 6)) NaturalGeometry.canonicalLine).pCoreIn 2 = pointCore := by
    have hh : subspaceStabilizer (naturalRepresentation (Fin 6)) NaturalGeometry.canonicalLine = H1 := by
      ext x
      exact (NaturalPairing.mem_stabilizer_iff_map _ _).trans (NaturalGeometry.canonicalLine_stabilizer x)
    rw [hh,H1_core_eq_pointCore]
  have hs : swap45 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hall := PointCoreGeneration.point_core_generate NaturalGeometry.canonicalLine
    NaturalGeometry.canonicalLine_finrank swap45 t (by exact ⟨4,5,by decide,rfl⟩) ht (hcore ▸ hs) hn
  rwa [hcore] at hall

private theorem shift_generates :
    pointCore.map (MulAut.conj shift).toMonoidHom ⊔ zpowers swap45 = ⊤ := by
  have hh := crossing_generate (Equiv.swap 3 4) (by exact ⟨3,4,by decide,rfl⟩)
    (by change swap45 * Equiv.swap 3 4 ≠ Equiv.swap 3 4 * swap45; decide +kernel)
  have he : (MulAut.conj shift).toMonoidHom (Equiv.swap (3 : Fin 6) 4) = swap45 := by decide +kernel
  have hh := congrArg (Subgroup.map (MulAut.conj shift).toMonoidHom) hh
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj shift).toMonoidHom (MulAut.conj shift).surjective] at hh
  exact hh


private theorem inverse_shift_generates :
    pointCore.map (MulAut.conj shift⁻¹).toMonoidHom ⊔ zpowers swap45 = ⊤ := by
  have hh := crossing_generate (Equiv.swap 1 5) (by exact ⟨1,5,by decide,rfl⟩)
    (by change swap45 * Equiv.swap 1 5 ≠ Equiv.swap 1 5 * swap45; decide +kernel)
  have he : (MulAut.conj shift⁻¹).toMonoidHom (Equiv.swap (1 : Fin 6) 5) = swap45 := by decide +kernel
  have hh := congrArg (Subgroup.map (MulAut.conj shift⁻¹).toMonoidHom) hh
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,he,
    map_top_of_surjective (MulAut.conj shift⁻¹).toMonoidHom (MulAut.conj shift⁻¹).surjective] at hh
  exact hh

/-- A strict invariant subspace of the five-dimensional augmentation core
admits paired even conjugators. The same fixed five-cycle works for every
subspace satisfying the hypotheses. -/
theorem exists_paired_card (W : Submodule (ZMod 2) (core (Fin 6)))
    (hsmall : Nat.card W < 16)
    (hfixed : fixedSpace (coreRepresentation (Fin 6)) pointCore ≤ W)
    (hinv : ∀ r ∈ pointCore, ∀ x ∈ W, coreRepresentation (Fin 6) r x ∈ W) :
    ∃ g : alternatingGroup (Fin 6),
      (pointCore.map (MulAut.conj g.val).toMonoidHom ⊔ zpowers swap45 = ⊤) ∧
      (pointCore.map (MulAut.conj g.val⁻¹).toMonoidHom ⊔ zpowers swap45 = ⊤) ∧
      W ⊓ W.map (coreRepresentation (Fin 6) g.val) ≤ coreConstants (Ω := Fin 6) ∧
      W ⊓ W.map (coreRepresentation (Fin 6) g.val⁻¹) ≤ coreConstants (Ω := Fin 6) := by
  have hf := intersection_le_constants W hsmall hfixed hinv
  refine ⟨⟨shift,shift_even⟩,shift_generates,inverse_shift_generates,hf,?_⟩
  intro x hx
  have hfx : coreRepresentation (Fin 6) shift x ∈ W := by
    obtain ⟨y,hy,he⟩ := hx.2
    rw [←he,←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    exact hy
  have hh := hf (show coreRepresentation (Fin 6) shift x ∈
      W ⊓ W.map (coreRepresentation (Fin 6) shift) from ⟨hfx,⟨x,hx.1,rfl⟩⟩)
  change (coreRepresentation (Fin 6) shift x).val ∈ constants (Fin 6) at hh
  obtain ⟨c,hc⟩ := (mem_constants_iff _).mp hh
  change x.val ∈ constants (Fin 6)
  apply (mem_constants_iff _).mpr
  refine ⟨c,fun i => ?_⟩
  have hi := hc (shift i)
  change x.val (shift.symm (shift i)) = c at hi
  simpa only [Equiv.symm_apply_apply] using hi


/-- Dimension-three form of the paired full-cover intersection theorem. -/
theorem exists_paired (W : Submodule (ZMod 2) (core (Fin 6)))
    (hsmall : Module.finrank (ZMod 2) W ≤ 3)
    (hfixed : fixedSpace (coreRepresentation (Fin 6)) pointCore ≤ W)
    (hinv : ∀ r ∈ pointCore, ∀ x ∈ W, coreRepresentation (Fin 6) r x ∈ W) :
    ∃ g : alternatingGroup (Fin 6),
      (pointCore.map (MulAut.conj g.val).toMonoidHom ⊔ zpowers swap45 = ⊤) ∧
      (pointCore.map (MulAut.conj g.val⁻¹).toMonoidHom ⊔ zpowers swap45 = ⊤) ∧
      W ⊓ W.map (coreRepresentation (Fin 6) g.val) ≤ coreConstants (Ω := Fin 6) ∧
      W ⊓ W.map (coreRepresentation (Fin 6) g.val⁻¹) ≤ coreConstants (Ω := Fin 6) := by
  apply exists_paired_card W _ hfixed hinv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hh : 2 ^ Module.finrank (ZMod 2) W ≤ 2 ^ 3 :=
    Nat.pow_le_pow_right (by decide) hsmall
  omega

/-- Codimension-two form of the paired full-cover intersection theorem. -/
theorem exists_paired_of_codim (W : Submodule (ZMod 2) (core (Fin 6)))
    (hsmall : 2 ≤ Module.finrank (ZMod 2) ((core (Fin 6)) ⧸ W))
    (hfixed : fixedSpace (coreRepresentation (Fin 6)) pointCore ≤ W)
    (hinv : ∀ r ∈ pointCore, ∀ x ∈ W, coreRepresentation (Fin 6) r x ∈ W) :
    ∃ g : alternatingGroup (Fin 6),
      (pointCore.map (MulAut.conj g.val).toMonoidHom ⊔ zpowers swap45 = ⊤) ∧
      (pointCore.map (MulAut.conj g.val⁻¹).toMonoidHom ⊔ zpowers swap45 = ⊤) ∧
      W ⊓ W.map (coreRepresentation (Fin 6) g.val) ≤ coreConstants (Ω := Fin 6) ∧
      W ⊓ W.map (coreRepresentation (Fin 6) g.val⁻¹) ≤ coreConstants (Ω := Fin 6) := by
  apply exists_paired W _ hfixed hinv
  have hh := W.finrank_quotient_add_finrank
  rw [finrank_core] at hh
  norm_num only [Fintype.card_fin] at hh
  omega

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCorePairing

