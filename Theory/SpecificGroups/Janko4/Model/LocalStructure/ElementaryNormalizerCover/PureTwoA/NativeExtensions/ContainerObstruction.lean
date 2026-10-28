module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.Images
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level6

/-!
# The marked pair has no unique extraspecial core container

The full ambient double centralizer of the kernel pair 818/1449 is the pair
itself. Indeed, the full binary kernel centralizes the pair and is
self-centralizing; three certified Mathieu actors then leave only the four
pair elements fixed. A product of existing star transversals cycles the
three nonidentity elements. Its actual ambient lift normalizes the pair,
so the full ambient centralizer of the pair normalizer is trivial.

Consequently that normalizer cannot normalize any conjugate of the
extraspecial first-centralizer core: it would fix the core's central
involution. If one such core contains the pair, conjugating it by a pair
normalizer produces a distinct such container. This disproves the
seed-only unique-container assertion for this literal native marking.

Kleidman--Wilson (1988), Section 2.1, p.489, uses a unique extraspecial
container for the printed AAA(2) four-group. That assertion cannot be
instantiated with the present native pair. This does not exclude uniqueness
for a larger elementary extension under additional geometric hypotheses,
nor contradict the full maximal-two-local cover. The extension-dependent
sextet/exceptional geometry remains to be established. All finite data here
use the existing native ATLAS action and certified star transversals.
-/

set_option Elab.async false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality QuotientCount.Image KernelCount
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
set_option backward.isDefEq.respectTransparency true


private theorem pair_le_kernel : nativePair ≤ embeddedKernel := by
  apply (closure_le _).mpr
  rintro x (rfl | rfl) <;>
    exact mem_map_of_mem M.subtype (maskValue matrixA_mul_self matrixB_pow_four _).property

private theorem pair_image_generator (j : Fin 5) :
    Stabilizer.generator j ∈ localPairCentralizer.map starHom := by
  obtain ⟨x,hx⟩ := starHom_surjective (Stabilizer.generator j)
  refine ⟨x,?_,hx⟩
  have hf (m : ℕ) (hm : SylowCore.starMask (Stabilizer.generator j) m = m) :
      x * kernelValue m * x⁻¹ = kernelValue m := by
    rw [kernel_conjugation]
    change kernelValue (SylowCore.starMask (starHom x) m) = _
    rw [hx,hm]
  rintro y (rfl | rfl)
  · exact (mul_inv_eq_iff_eq_mul.mp (hf 818 (generator_fixed j).1)).symm
  · exact (mul_inv_eq_iff_eq_mul.mp (hf 1449 (generator_fixed j).2)).symm

private theorem fixed_masks : ∀ m : Fin 2048,
    SylowCore.starMask (Stabilizer.generator 0) m.val = m.val →
    SylowCore.starMask (Stabilizer.generator 1) m.val = m.val →
    SylowCore.starMask (Stabilizer.generator 2) m.val = m.val →
    m.val = 0 ∨ m.val = 818 ∨ m.val = 1449 ∨ m.val = 1691 := by
  decide +kernel

/-- The marked pair is its full ambient double centralizer. -/
theorem nativePair_double_centralizer :
    centralizer (centralizer (nativePair : Set Model) : Set Model) = nativePair := by
  apply le_antisymm
  · intro z hz
    have hEC : embeddedKernel ≤ centralizer (nativePair : Set Model) := by
      let : IsElementaryAbelian 2 kernel := localKernel_elementary _ _
      let : IsElementaryAbelian 2 embeddedKernel := IsElementaryAbelian.map M.subtype
      exact embeddedKernel.le_centralizer.trans (centralizer_le pair_le_kernel)
    have hzE : z ∈ embeddedKernel := by
      have hh := (centralizer_le hEC) hz
      rwa [centralizer_embedded_localKernel] at hh
    obtain ⟨v,hv,rfl⟩ := hzE
    obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨v,hv⟩
    have he : kernelValue m.val = v := congrArg Subtype.val hm
    have hf (j : Fin 5) : SylowCore.starMask (Stabilizer.generator j) m.val = m.val := by
      obtain ⟨g,hg,hproj⟩ := pair_image_generator j
      have hgc : (g : Model) ∈ centralizer (nativePair : Set Model) := by
        rw [centralizer_eq_local_map]
        exact mem_map_of_mem M.subtype hg
      have hc : g * kernelValue m.val * g⁻¹ = kernelValue m.val := by
        apply Subtype.ext
        rw [he]
        change (g : Model) * (v : Model) * (g : Model)⁻¹ = v
        have hh := hz _ hgc
        change (g : Model) * (v : Model) = (v : Model) * (g : Model) at hh
        rw [hh,mul_inv_cancel_right]
      rw [kernel_conjugation] at hc
      change kernelValue (SylowCore.starMask (starHom g) m.val) = kernelValue m.val at hc
      rw [hproj] at hc
      exact kernelValue_injective (SylowCore.Transport.starMask_lt _ _) m.isLt hc
    have hx : (kernelValue 818 : Model) ∈ nativePair := subset_closure (by simp)
    have hy : (kernelValue 1449 : Model) ∈ nativePair := subset_closure (by simp)
    rw [← he]
    rcases fixed_masks m (hf 0) (hf 1) (hf 2) with h | h | h | h
    · rw [h,kernelValue_zero]; exact nativePair.one_mem
    · rw [h]; exact hx
    · rw [h]; exact hy
    · rw [h,show 1691 = Nat.xor 818 1449 from rfl,kernelValue_xor]
      exact nativePair.mul_mem hx hy
  · exact le_centralizer_iff.mpr le_rfl


open StarOrderCertificate
private def cycleStar : StarGroup :=
  ⟨rep0 18 * rep2 21 * rep4 16 * rep5 8 * rep6 2, by
    have h0 := level0_le
    have h1 := level1_le.trans h0
    have h2 := level2_le.trans h1
    have h3 := level3_le.trans h2
    have h4 := level4_le.trans h3
    have h5 := level5_le.trans h4
    have h6 := level6_le.trans h5
    exact StarGroup.mul_mem (StarGroup.mul_mem (StarGroup.mul_mem (StarGroup.mul_mem
      (word_mem gen0 StarGroup (fun i => h0 (gen_mem _ i)) _)
      (word_mem gen2 StarGroup (fun i => h2 (gen_mem _ i)) _))
      (word_mem gen4 StarGroup (fun i => h4 (gen_mem _ i)) _))
      (word_mem gen5 StarGroup (fun i => h5 (gen_mem _ i)) _))
      (word_mem gen6 StarGroup (fun i => h6 (gen_mem _ i)) _)⟩

private def pairMask : Fin 3 → ℕ := ![818,1449,1691]
private def cycleIndex : Fin 3 → Fin 3 := ![1,2,0]

private theorem cycle_masks : ∀ i : Fin 3,
    SylowCore.starMask cycleStar (pairMask i) = pairMask (cycleIndex i) := by
  decide +kernel

private theorem pair_coordinates (z : Model) (hz : z ∈ nativePair) :
    z = 1 ∨ ∃ i : Fin 3, z = (kernelValue (pairMask i) : Model) := by
  have hsq (m : ℕ) : (kernelValue m : Model) * kernelValue m = 1 :=
    congrArg (fun x : M => (x : Model)) (kernelValue_square m)
  have hh := (mem_closure_pair_iff (kernelValue 818 : Model) (kernelValue 1449)
    (hsq 818) (hsq 1449) ((kernelValue_commute _ _).map M.subtype) z).mp hz
  rcases hh with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · refine Or.inr ⟨2,?_⟩
    rw [h]
    exact congrArg (fun x : M => (x : Model)) (kernelValue_xor 818 1449).symm

private theorem pairMask_mem (i : Fin 3) :
    (kernelValue (pairMask i) : Model) ∈ nativePair := by
  have hx : (kernelValue 818 : Model) ∈ nativePair := subset_closure (by simp)
  have hy : (kernelValue 1449 : Model) ∈ nativePair := subset_closure (by simp)
  fin_cases i
  · exact hx
  · exact hy
  · change (kernelValue (Nat.xor 818 1449) : Model) ∈ nativePair
    rw [kernelValue_xor]
    exact nativePair.mul_mem hx hy

/-- A literal ambient normalizer element cycles the three nonidentity members. -/
theorem nativePair_cycle : ∃ g ∈ normalizer (nativePair : Set Model),
    ∀ z ∈ nativePair, (MulAut.conj g) z = z → z = 1 := by
  obtain ⟨g,hg⟩ := starHom_surjective cycleStar
  have hact (i : Fin 3) : (MulAut.conj (g : Model)) (kernelValue (pairMask i)) =
      (kernelValue (pairMask (cycleIndex i)) : Model) := by
    change ((g * kernelValue (pairMask i) * g⁻¹ : M) : Model) = _
    apply congrArg (fun x : M => (x : Model))
    rw [kernel_conjugation]
    change kernelValue (SylowCore.starMask (starHom g) (pairMask i)) = _
    rw [hg,cycle_masks]
  have hle : nativePair.map (MulAut.conj (g : Model)).toMonoidHom ≤ nativePair := by
    rintro _ ⟨z,hz,rfl⟩
    rcases pair_coordinates z hz with rfl | ⟨i,rfl⟩
    · simp
    · rw [show (MulAut.conj (g : Model)).toMonoidHom (kernelValue (pairMask i)) =
        (MulAut.conj (g : Model)) (kernelValue (pairMask i)) from rfl,hact]
      exact pairMask_mem _
  have hnorm : (g : Model) ∈ normalizer (nativePair : Set Model) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj (g : Model)).injective])
  refine ⟨g,hnorm,?_⟩
  intro z hz hfix
  rcases pair_coordinates z hz with h | ⟨i,rfl⟩
  · exact h
  have he : pairMask (cycleIndex i) = pairMask i := by
    have hh := (hact i).symm.trans hfix
    have hlt : ∀ j, pairMask j < 2048 := by decide +kernel
    exact kernelValue_injective (hlt _) (hlt _) (Subtype.ext hh)
  have hn : ∀ j, pairMask (cycleIndex j) ≠ pairMask j := by decide +kernel
  exact (hn i he).elim

/-- No nonidentity ambient element centralizes the whole pair normalizer. -/
theorem nativePair_normalizer_centralizer :
    centralizer (normalizer (nativePair : Set Model) : Set Model) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hzP : z ∈ nativePair := by
    rw [← nativePair_double_centralizer]
    exact centralizer_le (centralizer_le_normalizer _) hz
  obtain ⟨g,hg,hfix⟩ := nativePair_cycle
  apply mem_bot.mpr
  apply hfix z hzP
  change g * z * g⁻¹ = z
  rw [hz g hg,mul_inv_cancel_right]


/-- The whole normalizer of the marked pair normalizes no conjugate first core. -/
theorem nativePair_normalizer_not_le_core_normalizer (g : Model) :
    ¬ normalizer (nativePair : Set Model) ≤
      normalizer (firstCore.map (MulAut.conj g).toMonoidHom : Set Model) := by
  intro hN
  rw [← map_equiv_normalizer_eq,normalizer_firstCore] at hN
  have hz : (MulAut.conj g) a ∈
      centralizer (normalizer (nativePair : Set Model) : Set Model) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hN hx
    have hh := mem_centralizer_singleton_iff.mp hy
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) hh
  rw [nativePair_normalizer_centralizer] at hz
  have ha : a = 1 := (MulAut.conj g).injective
    ((mem_bot.mp hz).trans (map_one (MulAut.conj g)).symm)
  have ho := orderOf_a
  rw [ha,orderOf_one] at ho
  contradiction

private theorem map_conj_comp (A : Subgroup Model) (g n : Model) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom =
      A.map (MulAut.conj (n*g)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- A conjugate extraspecial first core containing the native pair is never
its unique such container. The witness is moved by an actual pair normalizer. -/
theorem nativePair_core_container_not_unique (g : Model)
    (hP : nativePair ≤ firstCore.map (MulAut.conj g).toMonoidHom) :
    ∃ k : Model, nativePair ≤ firstCore.map (MulAut.conj k).toMonoidHom ∧
      firstCore.map (MulAut.conj k).toMonoidHom ≠
        firstCore.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨n,hn,hbad⟩ := SetLike.not_le_iff_exists.mp
    (nativePair_normalizer_not_le_core_normalizer g)
  refine ⟨n*g,?_,?_⟩
  · have ht := map_mono (f := (MulAut.conj n).toMonoidHom) hP
    have hn' := mem_normalizer_iff_map_conj_eq.mp hn
    change nativePair.map (MulAut.conj n).toMonoidHom = nativePair at hn'
    rw [hn',map_conj_comp] at ht
    exact ht
  · intro he
    apply hbad
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (firstCore.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj n).toMonoidHom = _
    rw [map_conj_comp,he]

/-- The native pair does not satisfy the source-style unique core-container assertion. -/
theorem nativePair_no_unique_core_container :
    ¬ ∃! Q : Subgroup Model, nativePair ≤ Q ∧
      ∃ g : Model, Q = firstCore.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨Q,⟨hP,g,rfl⟩,huniq⟩
  obtain ⟨k,hk,hne⟩ := nativePair_core_container_not_unique g hP
  exact hne (huniq _ ⟨hk,k,rfl⟩)

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
