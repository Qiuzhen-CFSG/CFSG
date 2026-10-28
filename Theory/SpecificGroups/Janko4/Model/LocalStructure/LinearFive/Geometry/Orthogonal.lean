module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Form
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FormReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondCharacter

/-!
# Exact orthogonal subgroups of the native octad pullback

For an outside-E involution, the displacement by the kernel seed is a pair
mask which that involution swaps. The native second-centralizer character
therefore makes this displacement outer. The square-one catalogue then shows
that the full-centralizer residual intersects Q in exactly F or its seed
conjugate, not merely an overgroup of that elementary subgroup.

This proves the self-centralizing orthogonal occurrence used in
Kleidman--Wilson (1988), Proposition 2.2.2, pp.490--491. The final application
places every zero-form elementary subgroup of Q in E or a literal F-conjugate.
The transport theorem uses the actual embedded solvable residual.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Subgroup Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LargeCenterRadicals.OuterHalf
open InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY localKernelSeed basis

private theorem star_pair (g : M) (i j : Fin 24) :
    g * kernelValue (pairLabel i j) * g⁻¹ =
      kernelValue (pairLabel ((starHom g).val i) ((starHom g).val j)) :=
  congrArg Subtype.val (starHom_pair g i j)

private theorem pair_to_seed (i j : Fin 24) (hij : i ≠ j) :
    ∃ g : M, g * kernelValue (pairLabel i j) * g⁻¹ = kernelValue 1 := by
  have hn : kernelValue (pairLabel i j) ≠ 1 := by
    intro he
    have hl := kernelValue_injective (pairLabel_lt i j) (by decide) (he.trans kernelValue_zero.symm)
    exact hij ((pairLabel_eq_zero_iff i j).mp hl)
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    (kernelValue (pairLabel i j)) (maskValue _ _ _).property hn
  · exact ⟨g,hg.symm.trans (maskValue_one _ _).symm⟩
  · have he : kernelValue (pairLabel ((starHom g).val i) ((starHom g).val j)) = kernelValue 3 :=
      (star_pair g i j).symm.trans (hg.symm.trans (maskValue_three _ _).symm)
    have hl := kernelValue_injective (pairLabel_lt _ _) (by decide) he
    have hh : ∀ i j : Fin 24, pairLabel i j ≠ 3 := by decide +kernel
    exact (hh _ _ hl).elim

/-- Swapping a kernel pair acts in the outer half of its full centralizer. -/
theorem not_inner_of_star_swap (x : M) (i j : Fin 24) (hij : i ≠ j)
    (hi : (starHom x).val i = j) (hj : (starHom x).val j = i) :
    ¬ InnerRelated (kernelValue (pairLabel i j) : Model) (x : Model) := by
  obtain ⟨g,hg⟩ := pair_to_seed i j hij
  let y : M := g*x*g⁻¹
  have hlabel : pairLabel ((starHom g).val i) ((starHom g).val j) = 1 :=
    kernelValue_injective (pairLabel_lt _ _) (by decide) ((star_pair g i j).symm.trans hg)
  have hp : ∀ a b : Fin 24, pairLabel a b = 1 →
      (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) := by decide +kernel
  have hact (k : Fin 24) : (starHom y).val ((starHom g).val k) =
      (starHom g).val ((starHom x).val k) := by
    simp [y, map_mul, map_inv]
  have hswap : (starHom y).val 0 = 1 := by
    rcases hp _ _ hlabel with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hi,hb] using hact i
    · simpa only [hb,hj,ha] using hact j
  intro h
  have ht := innerRelated_map (MulAut.conj (g : Model)).toMonoidHom h
  have hg' : (MulAut.conj (g : Model)) (kernelValue (pairLabel i j) : Model) =
      (InvolutionCentralizers.Second.seed : Model) :=
    congrArg (fun a : M => (a : Model)) (hg.trans (maskValue_one _ _))
  change InnerRelated ((MulAut.conj (g : Model)) (kernelValue (pairLabel i j) : Model)) (y : Model) at ht
  rw [hg'] at ht
  change InnerRelated (InvolutionCentralizers.Second.seed : Model) (y : Model) at ht
  have hy : y ∈ localCentralizer := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (map_subtype_le _ ht)
  have hf := ((innerRelated_second_iff_star ⟨y,hy⟩).mp ht).1
  rw [hswap] at hf
  exact (by decide : (1 : Fin 24) ≠ 0) hf

private theorem projection_star (g : M) : projection g = starGroupEquivM24 (starHom g) := by
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four (QuotientGroup.mk' _ g) = _
  rw [localQuotientEquivM24_apply]
  rfl

private theorem star_mark (g : M) (i : Fin 24) :
    (projection g).val (StarOrderCertificate.relabel i) =
      StarOrderCertificate.relabel ((starHom g).val i) := by
  rw [projection_star, starGroupEquivM24_apply]
  simp

private theorem outside_star_points (x : M) (hxQ : (x : Model) ∈ Q) (hxE : (x : Model) ∉ E) :
    (starHom x).val 0 = 0 ∧ (starHom x).val 1 ≠ 1 := by
  have hxA : projection x ∈ A := by
    obtain ⟨y,hy,he⟩ := hxQ
    exact (M.subtype_injective he) ▸ hy
  have hn : projection x ≠ 1 := by
    intro he
    apply hxE
    refine ⟨x,?_,rfl⟩
    rw [←MathieuHallActors.projection_ker]
    exact he
  constructor
  · apply StarOrderCertificate.relabel.injective
    rw [←star_mark]
    exact (MathieuCode.mem_octadPointwiseKernel O _).mp hxA _ (by decide +kernel)
  · intro he
    have hm := (MathieuCode.octad_kernel_fixed_point_iff O _ hxA hn
      (StarOrderCertificate.relabel 1)).mp (by
        change (projection x).val _ = _
        rw [star_mark,he])
    exact (by decide +kernel : StarOrderCertificate.relabel 1 ∉ O.val) hm

/-- The seed displacement of an outside involution swaps its own kernel pair. -/
theorem seed_displacement_not_inner (x : M) (hxQ : (x : Model) ∈ Q)
    (hxE : (x : Model) ∉ E) (hx2 : orderOf (x : Model) = 2) :
    ¬ InnerRelated (x : Model) (seed * (x : Model) * seed⁻¹ * (x : Model)⁻¹) := by
  have hx : x*x=1 := M.subtype_injective (by
    change (x : Model)*(x : Model)=1
    simpa only [hx2,pow_two] using pow_orderOf_eq_one (x : Model))
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right hx
  have hs : (kernelValue 1)⁻¹ = kernelValue 1 := inv_eq_of_mul_eq_one_right (kernelValue_square 1)
  obtain ⟨h0,h1⟩ := outside_star_points x hxQ hxE
  let j := (starHom x).val 1
  have hj : (starHom x).val j = 1 := by
    have hh := congrArg (fun z : M => (starHom z).val 1) hx
    simpa only [map_mul,map_one,Subgroup.coe_mul,Subgroup.coe_one,Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply] using hh
  have hd : seed * (x : Model) * seed⁻¹ * (x : Model)⁻¹ =
      (kernelValue (pairLabel 1 j) : Model) := by
    change ((kernelValue 1*x*(kernelValue 1)⁻¹*x⁻¹ : M) : Model) = _
    apply congrArg (fun a : M => (a : Model))
    rw [hs]
    calc
      _ = kernelValue 1 * (x * kernelValue (pairLabel 0 1) * x⁻¹) := by
        rw [show kernelValue (pairLabel 0 1) = kernelValue 1 from rfl]
        group
      _ = kernelValue 1 * kernelValue (pairLabel 0 j) := by rw [star_pair, h0]
      _ = kernelValue (pairLabel 1 j) := by
        rw [← kernelValue_xor]
        have hc : ∀ k : Fin 24, Nat.xor (pairLabel 0 1) (pairLabel 0 k) = pairLabel 1 k := by
          decide +kernel
        exact congrArg kernelValue (hc j)
  have hne : kernelValue (pairLabel 1 j) ≠ 1 := by
    intro he
    exact h1 ((pairLabel_eq_zero_iff 1 j).mp
      (kernelValue_injective (pairLabel_lt _ _) (by decide) (he.trans kernelValue_zero.symm))).symm
  have hd2 : orderOf (kernelValue (pairLabel 1 j) : Model) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact congrArg (fun a : M => (a : Model)) (kernelValue_square _)
    · intro he; exact hne (Subtype.ext he)
  have hc : Commute (x : Model) (kernelValue (pairLabel 1 j) : Model) := by
    have hh := star_pair x 1 j
    rw [hj, pairLabel_symm j 1] at hh
    exact congrArg (fun a : M => (a : Model)) (mul_inv_eq_iff_eq_mul.mp hh)
  rw [hd]
  intro hi
  exact not_inner_of_star_swap x 1 j (Ne.symm h1) rfl hj
    ((innerRelated_symm _ _ hx2 hd2 hc).mp hi)

open scoped IsMulCommutative
attribute [local instance] F_elementary

private theorem seed_conj_twice (x : Model) :
    seed * (seed * x * seed⁻¹) * seed⁻¹ = x := by
  have hi : seed⁻¹ = seed := inv_eq_of_mul_eq_one_right seed_square
  rw [hi]
  calc
    _ = (seed*seed)*x*(seed*seed) := by group
    _ = x := by rw [seed_square]; simp

private theorem kernel_seed_commute (e : Model) (he : e ∈ E) : Commute seed e := by
  obtain ⟨z,hz,rfl⟩ := mem_map.mp he
  exact (congrArg (fun a : M => (a : Model)) (kernel_commute z hz 1).eq).symm

/-- The actual residual intersection at an outside-E element of F is F itself. -/
theorem F_x_eq_F (x : Model) (hx : x ∈ F) (hxE : x ∉ E) : F_x x = F := by
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have hx2 : orderOf x = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hx1
  apply le_antisymm _ (F_le_F_x x hx hx1)
  intro y hy
  obtain ⟨e,he,f,hf,rfl⟩ := Q_factorization y hy.1
  let I := (solvableResidual (centralizer ({x} : Set Model))).map
    (centralizer ({x} : Set Model)).subtype
  have hfI : f ∈ I := F_innerRelated x f hx hf hx1
  have heI : e ∈ I := by
    simpa only [mul_inv_cancel_right] using I.mul_mem hy.2 (I.inv_mem hfI)
  have hec : Commute e x := mem_centralizer_singleton_iff.mp (map_subtype_le _ heI)
  have he2 : e*e=1 := by
    obtain ⟨z,hz,rfl⟩ := mem_map.mp he
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    exact congrArg (fun a : M => (a : Model))
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)
  have hxs : x*x=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hexs : (e*x)*(e*x)=1 := by
    calc
      _ = (e*e)*(x*x) := by rw [mul_assoc, ← mul_assoc x, ← hec.eq]; group
      _ = 1 := by rw [he2,hxs,one_mul]
  rcases Q_square_one_occurrences (e*x) (Q.mul_mem (Q_contains_E he) (F_le_Q hx)) hexs with h | h | h
  · exact (hxE (by simpa only [inv_mul_cancel_left] using E.mul_mem (E.inv_mem he) h)).elim
  · exact F.mul_mem (by simpa only [mul_inv_cancel_right] using F.mul_mem h (F.inv_mem hx)) hf
  · have hconj : seed * (e*x) * seed⁻¹ ∈ F := by
      obtain ⟨z,hz,hzex⟩ := mem_map.mp h
      change seed*z*seed⁻¹ = e*x at hzex
      rw [← hzex,seed_conj_twice]
      exact hz
    have hk : e*(seed*x*seed⁻¹*x⁻¹) ∈ F := by
      have hh := F.mul_mem hconj (F.inv_mem hx)
      have heq : (seed*(e*x)*seed⁻¹)*x⁻¹ = e*(seed*x*seed⁻¹*x⁻¹) := by
        rw [← mul_assoc seed, (kernel_seed_commute e he).eq]
        group
      exact heq ▸ hh
    have hkI : e*(seed*x*seed⁻¹*x⁻¹) ∈ I := F_innerRelated x _ hx hk hx1
    have hdI : seed*x*seed⁻¹*x⁻¹ ∈ I := by
      simpa only [inv_mul_cancel_left] using I.mul_mem (I.inv_mem heI) hkI
    exact (seed_displacement_not_inner ⟨x,Q_le_M (F_le_Q hx)⟩ (F_le_Q hx) hxE hx2 hdI).elim


private theorem seed_conj_mem_iff (H : Subgroup Model) (hs : seed ∈ H) (x : Model) :
    seed*x*seed⁻¹ ∈ H ↔ x ∈ H :=
  (mem_normalizer_iff.mp (H.le_normalizer hs) x).symm

private theorem seed_conj_mem_F_x_iff (x y : Model) :
    seed*y*seed⁻¹ ∈ F_x (seed*x*seed⁻¹) ↔ y ∈ F_x x := by
  change (seed*y*seed⁻¹ ∈ Q ∧ InnerRelated ((MulAut.conj seed) x) ((MulAut.conj seed) y)) ↔
    (y ∈ Q ∧ InnerRelated x y)
  rw [seed_conj_mem_iff Q (Q_contains_E seed_mem_E),innerRelated_equiv]

/-- The other native occurrence is the exact residual intersection as well. -/
theorem F_x_eq_secondF (x : Model) (hx : x ∈ secondF) (hxE : x ∉ E) :
    F_x x = secondF := by
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have hxF : seed*x*seed⁻¹ ∈ F := by
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hx
    change seed*(seed*z*seed⁻¹)*seed⁻¹ ∈ F
    rwa [seed_conj_twice]
  have hxE' : seed*x*seed⁻¹ ∉ E := fun h => hxE ((seed_conj_mem_iff E seed_mem_E x).mp h)
  have heq := F_x_eq_F _ hxF hxE'
  apply le_antisymm _ (secondF_le_F_x x hx hx1)
  intro y hy
  have hy' := (seed_conj_mem_F_x_iff x y).mpr hy
  rw [heq] at hy'
  exact mem_map.mpr ⟨seed*y*seed⁻¹,hy',seed_conj_twice y⟩

/-- Exact orthogonality in Q for every source involution outside E. -/
theorem outside_involution_F_x (x : Model) (hxQ : x ∈ Q) (hxE : x ∉ E)
    (hx2 : orderOf x = 2) :
    (x ∈ F ∧ F_x x = F) ∨ (x ∈ secondF ∧ F_x x = secondF) := by
  rcases outside_involution_orthogonal_occurrence x hxQ hxE hx2 with ⟨h,_⟩ | ⟨h,_⟩
  · exact Or.inl ⟨h,F_x_eq_F x h hxE⟩
  · exact Or.inr ⟨h,F_x_eq_secondF x h hxE⟩

/-- The residual subgroup at an outside involution is elementary of order 1024,
self-centralizing, and a literal conjugate of the native F. -/
theorem outside_involution_F_x_spec (x : Model) (hxQ : x ∈ Q) (hxE : x ∉ E)
    (hx2 : orderOf x = 2) :
    x ∈ F_x x ∧ IsElementaryAbelian 2 (F_x x) ∧ Nat.card (F_x x) = 1024 ∧
      centralizer (F_x x : Set Model) = F_x x ∧
      ∃ g : Model, (g = 1 ∨ g = seed) ∧ F.map (MulAut.conj g).toMonoidHom = F_x x := by
  rcases outside_involution_F_x x hxQ hxE hx2 with ⟨hx,h⟩ | ⟨hx,h⟩
  · rw [h]
    refine ⟨hx,F_elementary,F_card,centralizer_F,1,Or.inl rfl,?_⟩
    exact mem_normalizer_iff_map_conj_eq.mp (normalizer (F : Set Model)).one_mem
  · rw [h]
    exact ⟨hx,secondF_elementary,secondF_card,centralizer_secondF,seed,Or.inr rfl,rfl⟩

/-- Literal transport of both the octad pullback and the full-centralizer
residual under any ambient conjugator. -/
theorem F_x_conjugate (g x : Model) :
    (F_x x).map (MulAut.conj g).toMonoidHom =
      Q.map (MulAut.conj g).toMonoidHom ⊓
        (solvableResidual (centralizer ({g*x*g⁻¹} : Set Model))).map
          (centralizer ({g*x*g⁻¹} : Set Model)).subtype := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨mem_map.mpr ⟨z,hz.1,rfl⟩,innerRelated_map (MulAut.conj g).toMonoidHom hz.2⟩
  · rintro ⟨⟨z,hz,rfl⟩,hy⟩
    exact mem_map.mpr ⟨z,⟨hz,(innerRelated_equiv (MulAut.conj g) x z).mp hy⟩,rfl⟩

/-- KW 2.2.2(i)--(ii) for the actual octad pullback. The zero intrinsic form
forces the whole elementary subgroup into one of the two native occurrences. -/
theorem zero_form_Q_placement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXQ : X ≤ Q) (hform : intrinsicElementaryForm X = 0) :
    X ≤ E ∨ X ≤ F ∨ X ≤ secondF := by
  by_cases hXE : X ≤ E
  · exact Or.inl hXE
  obtain ⟨x,hx,hxE⟩ := SetLike.not_le_iff_exists.mp hXE
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have hx2 : orderOf x = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hx1
  have hX : X ≤ F_x x := le_inf hXQ
    (ElementaryNormalizerCover.zero_form_le_involution_residual X hform x hx hx1)
  rcases outside_involution_F_x x (hXQ hx) hxE hx2 with ⟨_,h⟩ | ⟨_,h⟩
  · exact Or.inr (Or.inl (h ▸ hX))
  · exact Or.inr (Or.inr (h ▸ hX))

end Janko4.LocalStructure.LinearFive.Geometry
