module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.CentralizerReduction

/-!
# A central 2A involution for the native sextet lifts

Each of the thirty non-octad four-groups in the sextet E16 has the same four
fixed points in the native Mathieu action. Their tetrad defines the actual
kernel element with mask 335. The kernel orbit certificates prove that it is
in class 2A. A centralizer element permutes the four points and therefore fixes
the sum of their pair labels, so the whole centralizer fixes this involution.

For a source lift containing the original 2B seed, that seed places the full
centralizer in max1. The finite calculation then applies without a supplied
ambient positioning premise. The literal residual quotient and all conjugators
are retained, including the exact order-sixteen exceptional image and seed line.
The new involution belongs to the canonical subgroup Ω₁(Z(C(X))). At maximal
TWO-local level this enlargement preserves the whole normalizer. For an
arbitrary radical whose normalizer normalizes X, the enlargement lies in the
same radical, and the local normalizer and 2-core retain their original maps.

This establishes a central-involution step for the small sextet configurations.
Containment of C(X) in the extraspecial core, after excluding E/F placement,
and the subsequent pure-2A normalizer analysis remain necessary for the cover.
No such core containment is inferred from centralization alone.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988),
Proposition 2.2.3, p.491. The finite action uses the previously certified native
M22 sextet marking and the ATLAS kernel coordinates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetCentralizer
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry FusionCertificate ElementarySylow SextetKernel
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

private def point : Fin 4 → Fin 24 := ![5,8,13,14]

private def action (i : Fin 16) (j : Fin 24) : Fin 24 :=
  StarOrderCertificate.relabel.symm
    (CommonFour.extendPoint (pointTable (candidateIndex 0 i))
      (StarOrderCertificate.relabel j))

private theorem point_injective : Function.Injective point := by decide +kernel

private theorem fixed_points : ∀ (k : Fin 30) (j : Fin 24),
    (action (nonOctadPair k 0) j = j ∧ action (nonOctadPair k 1) j = j) ↔
      ∃ i : Fin 4, point i = j := by decide +kernel

private theorem partition_label : ∀ (a b c d : Fin 4),
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    Nat.xor (pairLabel (point a) (point b)) (pairLabel (point c) (point d)) = 335 := by
  intro a
  fin_cases a <;> decide +kernel

private theorem star_action (x : M) (i : Fin 16) (hx : projection x = imageElement i)
    (j : Fin 24) : (starHom x).val j = action i j :=
  KernelAction.star_points x _ hx j

/-- The actual kernel element represented by the fixed tetrad. -/
@[expose] def centralInvolution : Model := kernelValue 335

theorem centralInvolution_mem_kernel : centralInvolution ∈ E := kernelValue_mem_E 335

theorem centralInvolution_ne_one : centralInvolution ≠ 1 := by
  intro he
  have h := kernelValue_injective (by decide : 335 < 2048) (by decide : 0 < 2048)
    ((show kernelValue 335 = 1 from Subtype.ext he).trans kernelValue_zero.symm)
  contradiction

theorem centralInvolution_first : IsConj a centralInvolution := by
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    (kernelValue 335) (maskValue _ _ _).property
    (fun h => centralInvolution_ne_one (congrArg Subtype.val h))
  · have hback : g⁻¹ * kernelValue 1 * (g⁻¹)⁻¹ = kernelValue 335 := by
      rw [show kernelValue 1 = localKernelSeed matrixA_mul_self matrixB_pow_four from
        maskValue_one _ _, hg]
      simp [mul_assoc]
    have hp := congrArg Subtype.val (starHom_pair g⁻¹ 0 1)
    change g⁻¹ * kernelValue 1 * (g⁻¹)⁻¹ =
      kernelValue (pairLabel ((starHom g⁻¹).val 0) ((starHom g⁻¹).val 1)) at hp
    have he := kernelValue_injective (pairLabel_lt _ _) (by decide : 335 < 2048)
      (hp.symm.trans hback)
    have hn : ∀ i j : Fin 24, pairLabel i j ≠ 335 := by decide +kernel
    exact (hn _ _ he).elim
  · obtain ⟨q,hq⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
    have hc : IsConj centralInvolution (kernelPair matrixA_mul_self matrixB_pow_four : Model) :=
      M.subtype.map_isConj (isConj_iff.mpr ⟨g,hg.symm⟩)
    exact (hc.trans (isConj_iff.mpr ⟨q,hq.symm⟩)).symm

theorem centralInvolution_order : orderOf centralInvolution = 2 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp centralInvolution_first
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a

private theorem tetrad_fixed (c : M)
    (hfix : ∀ i : Fin 4, ∃ j : Fin 4, point j = (starHom c).val (point i)) :
    Commute (c : Model) centralInvolution := by
  choose f hf using hfix
  have hfinj : Function.Injective f := by
    intro i j h
    exact point_injective ((starHom c).val.injective ((hf i).symm.trans
      ((congrArg point h).trans (hf j))))
  have he := partition_label (f 0) (f 1) (f 2) (f 3)
    (hfinj.ne (by decide)) (hfinj.ne (by decide)) (hfinj.ne (by decide))
    (hfinj.ne (by decide)) (hfinj.ne (by decide)) (hfinj.ne (by decide))
  simp only [hf] at he
  have hmask : kernelValue 335 = kernelValue (pairLabel (point 0) (point 1)) *
      kernelValue (pairLabel (point 2) (point 3)) := by
    rw [← kernelValue_xor]
    rfl
  have hc : c * kernelValue 335 * c⁻¹ = kernelValue 335 := by
    rw [hmask]
    change (MulAut.conj c).toMonoidHom (_ * _) = _
    rw [map_mul]
    rw [show (MulAut.conj c).toMonoidHom (kernelValue (pairLabel (point 0) (point 1))) =
      kernelValue (pairLabel ((starHom c).val (point 0)) ((starHom c).val (point 1))) from
        congrArg Subtype.val (starHom_pair c (point 0) (point 1))]
    rw [show (MulAut.conj c).toMonoidHom (kernelValue (pairLabel (point 2) (point 3))) =
      kernelValue (pairLabel ((starHom c).val (point 2)) ((starHom c).val (point 3))) from
        congrArg Subtype.val (starHom_pair c (point 2) (point 3))]
    rw [← kernelValue_xor,he,← hmask]
  exact congrArg (fun x : M => (x : Model)) (mul_inv_eq_iff_eq_mul.mp hc)

/-- The whole ambient centralizer fixes the source tetrad involution. -/
theorem centralizer_le_involution_centralizer (X : Subgroup Model)
    (k : Fin 30)
    (himage : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralizer (X : Set Model) ≤ centralizer ({centralInvolution} : Set Model) := by
  intro c hc
  let c0 : M := ⟨c,hCM hc⟩
  apply mem_centralizer_singleton_iff.mpr
  apply tetrad_fixed c0
  intro i
  apply (fixed_points k _).mp
  have fixed (d : Fin 2) : action (nonOctadPair k d) ((starHom c0).val (point i)) =
      (starHom c0).val (point i) := by
    obtain ⟨x,hx,hpi⟩ := himage d
    have hcomm : Commute x c0 := Subtype.ext (hc x hx)
    have hp := congrArg (fun p => p.val (point i))
      (hcomm.map starHom).eq
    have hi : action (nonOctadPair k d) (point i) = point i := by
      have h := (fixed_points k (point i)).mpr ⟨i,rfl⟩
      fin_cases d
      · exact h.1
      · exact h.2
    change (starHom x).val ((starHom c0).val (point i)) =
      (starHom c0).val ((starHom x).val (point i)) at hp
    simpa only [star_action x _ hpi,hi] using hp
  exact ⟨fixed 0,fixed 1⟩

private theorem involution_mem_central_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (t : Model) (ht2 : orderOf t = 2)
    (hC : centralizer (X : Set Model) ≤ centralizer ({t} : Set Model)) :
    t ∈ omegaCenterIn (centralizer (X : Set Model)) := by
  have hcomm (c : Model) (hc : c ∈ centralizer (X : Set Model)) : c * t = t * c :=
    mem_centralizer_singleton_iff.mp (hC hc)
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_,hcomm,?_⟩
  · intro x hx
    exact hcomm x (X.le_centralizer hx)
  · rw [← ht2]
    exact pow_orderOf_eq_one t

/-- The marked 2A involution belongs to the canonical central-omega enlargement,
not merely to an abstract group with the expected isomorphism type. -/
theorem centralInvolution_mem_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (k : Fin 30)
    (himage : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralInvolution ∈ omegaCenterIn (centralizer (X : Set Model)) :=
  involution_mem_central_omega X centralInvolution centralInvolution_order
    (centralizer_le_involution_centralizer X k himage hCM)

private theorem conjugate_comp (X : Subgroup Model) (g h : Model) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one (X : Subgroup Model) :
    X.map (MulAut.conj (1 : Model)).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (X : Set Model)).one_mem

private theorem pull_centralizer (X : Subgroup Model) (g t : Model)
    (hC : centralizer (X.map (MulAut.conj g).toMonoidHom : Set Model) ≤
      centralizer ({t} : Set Model)) :
    centralizer (X : Set Model) ≤ centralizer ({(MulAut.conj g⁻¹) t} : Set Model) := by
  intro c hc
  have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hc
  rw [map_centralizer_equiv] at hm
  have ht := mem_centralizer_singleton_iff.mp (hC hm)
  apply mem_centralizer_singleton_iff.mpr
  apply (MulAut.conj g).injective
  have he : (MulAut.conj g) ((MulAut.conj g⁻¹) t) = t := by simp [mul_assoc]
  rw [map_mul,map_mul,he]
  exact ht

/-- The small sextet lifts have a literal 2A involution central in their
full centralizers. The octad alternatives already give whole-normalizer coverage.
The stronger extraspecial-core containment is not a hypothesis or a conclusion. -/
theorem sextetLift_normalizer_or_central_involution (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hX : X ≤ residualLift M22ChapterH.Sextet.innerTranslations)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (seed : Model) ∈ X) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (Nat.card X ≤ 128 ∧ ∃ s : M,
      centralizer (X : Set Model) ≤
        centralizer ({(MulAut.conj (s : Model)⁻¹) centralInvolution} : Set Model) ∧
      (MulAut.conj (s : Model)⁻¹) centralInvolution ∈
        omegaCenterIn (centralizer (X : Set Model))) := by
  have hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x := by
    intro hp
    exact first_not_isConj_second (hp _ hseed (by
      intro he
      have ho := seed_order
      rw [he,orderOf_one] at ho
      contradiction))
  rcases sextetLift_normalizer_or_small X hX hzero hn with h | ⟨hc,s,k,hYM,hki,_⟩
  · exact Or.inl h
  right
  let e := MulAut.conj (s : Model)
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hseedY : e (seed : Model) ∈ Y := mem_map_of_mem _ hseed
  have hE : E.map e.toMonoidHom = E := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [embedded_localKernel_normalizer_eq_max1]
    exact s.property
  have hseedE : (seed : Model) ∈ E := by
    simpa only [show kernelValue 1 = seed from maskValue_one _ _] using kernelValue_mem_E 1
  have htE : e (seed : Model) ∈ E := hE ▸ mem_map_of_mem e.toMonoidHom hseedE
  have hnot : ¬ IsConj a (e (seed : Model)) := by
    intro hh
    exact first_not_isConj_second (hh.trans (isConj_iff.mpr ⟨(s : Model)⁻¹,by
      simp [e,mul_assoc]⟩))
  have ht1 : e (seed : Model) ≠ 1 := by
    intro he
    have hs1 : (seed : Model) = 1 := e.injective (he.trans (map_one e).symm)
    have ho := seed_order
    rw [hs1,orderOf_one] at ho
    contradiction
  have hCM : centralizer (Y : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hseedY)).trans
      (kernel_nonfirst_centralizer_le_max1 _ htE ht1 hnot)
  have hC := pull_centralizer X (s : Model) centralInvolution
    (centralizer_le_involution_centralizer Y k hki hCM)
  exact ⟨hc,s,hC,involution_mem_central_omega X _
    (((MulAut.conj (s : Model)⁻¹).orderOf_eq centralInvolution).trans centralInvolution_order) hC⟩

/-- A conjugate sextet lift with its own second-class seed retains the entire
centralizer bound, without assuming that its normalizer lies in max1. -/
theorem sextet_conjugate_normalizer_or_central_involution (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (g : Model)
    (hX : X ≤ (residualLift M22ChapterH.Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (MulAut.conj g) (seed : Model) ∈ X) :
    (∃ k : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom) ∨
    (Nat.card X ≤ 128 ∧ ∃ t : Model, IsConj a t ∧
      centralizer (X : Set Model) ≤ centralizer ({t} : Set Model) ∧
      t ∈ omegaCenterIn (centralizer (X : Set Model))) := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hY : Y ≤ residualLift M22ChapterH.Sextet.innerTranslations := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hh
  have hseedY : (seed : Model) ∈ Y := by
    have he : (MulAut.conj g⁻¹) ((MulAut.conj g) (seed : Model)) = (seed : Model) := by
      simp [mul_assoc]
    exact he ▸ mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hseed
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  rcases sextetLift_normalizer_or_central_involution Y hY
      (intrinsicForm_zero_map X Y (MulAut.conj g⁻¹) rfl hzero) hseedY with ⟨k,hk⟩ | ⟨hc,s,hC,_⟩
  · left
    refine ⟨g*k,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj k).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj (g*k)).toMonoidHom := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hh
    exact hk.imp (transfer _) (transfer _)
  · right
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective] at hc
    let t := (MulAut.conj g) ((MulAut.conj (s : Model)⁻¹) centralInvolution)
    have ht : IsConj a t := centralInvolution_first.trans
      ((isConj_iff.mpr ⟨(s : Model)⁻¹,rfl⟩).trans (isConj_iff.mpr ⟨g,rfl⟩))
    have hCt : centralizer (X : Set Model) ≤ centralizer ({t} : Set Model) := by
      have hh := pull_centralizer X g⁻¹ _ hC
      simpa only [inv_inv] using hh
    refine ⟨hc,t,ht,hCt,involution_mem_central_omega X t ?_ hCt⟩
    obtain ⟨u,hu⟩ := isConj_iff.mp ht
    rw [← hu]
    exact ((MulAut.conj u).orderOf_eq a).trans orderOf_a

/-- In the original residual marking, the unresolved sextet alternative now
has an actual first-class involution in its canonical central omega.
The exceptional E8 image retains its exact order and original seed-line kernel. -/
theorem zero_form_seed_normalizer_or_central_involution_or_eight
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (Nat.card X ≤ 128 ∧ ∃ t : Model, IsConj a t ∧
      centralizer (X : Set Model) ≤ centralizer ({t} : Set Model) ∧
      t ∈ omegaCenterIn (centralizer (X : Set Model))) ∨
    (Nat.card X = 16 ∧ X ⊓ embeddedKernel = zpowers (seed : Model) ∧
      ∃ n : residual, X ≤ (residualLift (smallContainer 0)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∧
      (X.comap residualInclusion).map residualProjection =
        (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
  rcases zero_form_seed_normalizer_or_exceptional X hzero hseed with h | ⟨n,hn⟩ | he
  · exact Or.inl h
  · have hfix : (MulAut.conj (residualInclusion n)) (seed : Model) = (seed : Model) := by
      change residualInclusion n * (seed : Model) * (residualInclusion n)⁻¹ = _
      have hc : residualInclusion n * (seed : Model) = (seed : Model) * residualInclusion n :=
        mem_centralizer_singleton_iff.mp n.val.property
      rw [hc, mul_inv_cancel_right]
    rcases sextet_conjugate_normalizer_or_central_involution X (residualInclusion n) hn
        hzero (hfix.symm ▸ hseed) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr he)

/-- Maximality among two-locals preserves the whole normalizer on the
canonical enlargement in the sextet branch. Its 2A involution is explicit;
the selected 2B seed remains in the enlarged elementary group. -/
theorem maximal_sextet_normalizer_enlargement (X H : Subgroup Model)
    [IsElementaryAbelian 2 X] (g : Model)
    (hX : X ≤ (residualLift M22ChapterH.Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (MulAut.conj g) (seed : Model) ∈ X)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    (∃ k : Model, H = M_F.map (MulAut.conj k).toMonoidHom ∨
      H = max1.map (MulAut.conj k).toMonoidHom) ∨
    (let W := omegaCenterIn (centralizer (X : Set Model));
      X ≤ W ∧ (MulAut.conj g) (seed : Model) ∈ W ∧
      H = normalizer (W : Set Model) ∧
      ∃ t : Model, IsConj a t ∧ t ∈ W ∧
        centralizer (X : Set Model) ≤ centralizer ({t} : Set Model)) := by
  rcases sextet_conjugate_normalizer_or_central_involution X g hX hzero hseed with
      ⟨k,hk⟩ | ⟨_,t,ht,hC,htW⟩
  · left
    refine ⟨k,?_⟩
    rcases hk with hk | hk
    · exact Or.inl (hH.eq_of_le (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k))
        (hHX ▸ hk))
    · exact Or.inr (hH.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k))
        (hHX ▸ hk))
  · right
    dsimp only
    have hXW := elementary_le_centralizer_omegaCenter X
    have ht1 : t ≠ 1 := by
      intro he
      have ha := isConj_one_left.mp (he ▸ ht)
      have ho := orderOf_a
      rw [ha,orderOf_one] at ho
      contradiction
    have hW : omegaCenterIn (centralizer (X : Set Model)) ≠ ⊥ :=
      fun he => ht1 (mem_bot.mp (he ▸ htW))
    exact ⟨hXW,hXW hseed,
      hH.eq_of_le ⟨_,hW,IsElementaryAbelian.isPGroup 2 _,rfl⟩
        (hHX ▸ normalizer_le_centralizer_omegaCenter_normalizer X),t,ht,htW,hC⟩

/-- Literal radical restriction for the sextet enlargement. In the remaining
branch the first-class involution belongs to the same arbitrary radical P,
and both the local normalizer and its full 2-core map back to the original ones. -/
theorem radical_sextet_normalizer_enlargement (P X : Subgroup Model)
    (hP : P.IsPRadical 2) [IsElementaryAbelian 2 X] (g : Model)
    (hX : X ≤ (residualLift M22ChapterH.Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (MulAut.conj g) (seed : Model) ∈ X)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ H : Subgroup Model, IsTwoLocal H ∧
      ((∃ k : Model, H = M_F.map (MulAut.conj k).toMonoidHom ∨
          H = max1.map (MulAut.conj k).toMonoidHom) ∨
        (H = normalizer (omegaCenterIn (centralizer (X : Set Model)) : Set Model) ∧
          omegaCenterIn (centralizer (X : Set Model)) ≤ P ∧
          ∃ t : Model, IsConj a t ∧ t ∈ P ∧
            centralizer (X : Set Model) ≤ centralizer ({t} : Set Model))) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨H,hlocal,hrow,hNH⟩ : ∃ H : Subgroup Model, IsTwoLocal H ∧
      ((∃ k : Model, H = M_F.map (MulAut.conj k).toMonoidHom ∨
          H = max1.map (MulAut.conj k).toMonoidHom) ∨
        (H = normalizer (omegaCenterIn (centralizer (X : Set Model)) : Set Model) ∧
          omegaCenterIn (centralizer (X : Set Model)) ≤ P ∧
          ∃ t : Model, IsConj a t ∧ t ∈ P ∧
            centralizer (X : Set Model) ≤ centralizer ({t} : Set Model))) ∧
      normalizer (P : Set Model) ≤ H := by
    rcases sextet_conjugate_normalizer_or_central_involution X g hX hzero hseed with
        ⟨k,hk⟩ | ⟨_,t,ht,hC,htW⟩
    · rcases hk with hk | hk
      · exact ⟨_,nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k),
          Or.inl ⟨k,Or.inl rfl⟩,hNX.trans hk⟩
      · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k),
          Or.inl ⟨k,Or.inr rfl⟩,hNX.trans hk⟩
    · let W := omegaCenterIn (centralizer (X : Set Model))
      have hNW : normalizer (P : Set Model) ≤ normalizer (W : Set Model) :=
        hNX.trans (normalizer_le_centralizer_omegaCenter_normalizer X)
      have hWP : W ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
        P W hP.isPGroup (IsElementaryAbelian.isPGroup 2 W) hP.2.le hNW
      have ht1 : t ≠ 1 := by
        intro he
        have ha := isConj_one_left.mp (he ▸ ht)
        have ho := orderOf_a
        rw [ha,orderOf_one] at ho
        contradiction
      have hW : W ≠ ⊥ := fun he => ht1 (mem_bot.mp (he ▸ htW))
      exact ⟨_,⟨W,hW,IsElementaryAbelian.isPGroup 2 W,rfl⟩,
        Or.inr ⟨rfl,hWP,t,ht,hWP htW,hC⟩,hNW⟩
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨H,hlocal,hrow,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetCentralizer
