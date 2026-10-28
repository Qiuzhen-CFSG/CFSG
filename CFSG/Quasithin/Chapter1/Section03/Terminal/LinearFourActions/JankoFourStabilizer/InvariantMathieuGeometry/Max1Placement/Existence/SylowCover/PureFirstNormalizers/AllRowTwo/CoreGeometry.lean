module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ExtraspecialReduction

/-!
# Intrinsic point cores and the all-row-two normalizer action

The 8192-element census kernel is identified with the actual embedded
O₂(C(a)), using its normality and the certified centralizer-core order.
Consequently an all-row-two elementary group X lies in O₂(C(x)) for every
nonidentity x in X. Extraspecial commutators show that each of these entire
cores normalizes X and supplies the shear y ↦ xy. These shears make N(X)
transitive on X minus identity. Thus X has no proper nontrivial subgroup
invariant under its whole normalizer; in particular, selecting an invariant
four-group cannot resolve the source branch when |X| > 4.

The intersection I(X) of these intrinsic point cores contains X, centralizes
X, is a nontrivial two-group, and is preserved by N(X). If N(X) is maximal
among TWO-locals, N(X) = N(I(X)). The arbitrary-radical application retains
the full normalizer and the literal subgroup restriction and two-core maps.
Identifying N(I(X)) with a named native local remains open: the intersection
reduction does not assert the missing max4-eight container or local cover.

Source context: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988),
Corollary 1.2.2(a) and Section 2.1, printed pp.488--489. The proofs here are
native consequences of the checked census and extraspecial centralizers;
they do not assume the source's disputed unrestricted line-containment step.
The normalizer-shear argument is the pure counterpart of the existing
`ExtraspecialOrbit` argument. No new finite certificate is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
open ElementaryNormalizerCover
open Cardinality.LocalInvolutionCensus Cardinality.LocalInvolutionCensus.Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB

private theorem q_kernel_card : Nat.card q.ker = 8192 := by
  let f : Fin 8192 → q.ker := fun i => ⟨localKernelProduct i,q_localKernelProduct i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply LowerBound.kernelProduct_injective
      apply sourceSubgroupEquivLocal.injective
      exact congrArg (fun u : q.ker => (u : H)) hij
    · intro u
      have hq : localQuotientMap u = localQuotientMap 1 := by
        simpa only [coe_q,map_one,Subgroup.coe_one] using
          congrArg (fun z : Q => z.val) u.property
      obtain ⟨i,hi⟩ := local_fiber Cardinality.Thompson.max2_card.le u 1 hq
      exact ⟨i,Subtype.ext (by simpa only [mul_one] using hi.symm)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 8192)

/-- The census kernel is the actual ambient two-core of the first centralizer. -/
theorem firstKernel_eq_firstCore : firstKernel = firstCore := by
  let e : H ≃* InvolutionCentralizers.First.centralizer := Cardinality.Thompson.max2EquivCentralizer
  let K := q.ker.map e.toMonoidHom
  have hcard : Nat.card K = 8192 :=
    (card_map_of_injective e.injective).trans q_kernel_card
  let : K.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hP : IsPGroup 2 K := IsPGroup.of_card (n := 13) hcard
  have hle : K ≤ pCore 2 InvolutionCentralizers.First.centralizer :=
    le_sSup ⟨inferInstance,hP⟩
  have heq : K = pCore 2 InvolutionCentralizers.First.centralizer :=
    eq_of_le_of_card_ge hle (by rw [InvolutionCentralizers.First.centralizer_twoCore_card,hcard]; decide)
  have hemb : firstKernel = K.map InvolutionCentralizers.First.centralizer.subtype := by
    dsimp only [K]
    rw [map_map]
    change q.ker.map eH = _
    congr 1
    ext u
    exact (Cardinality.Thompson.max2EquivCentralizer_coe u).symm
  rw [hemb,heq]
  rfl

/-- Each nonidentity source element supplies its actual intrinsic centralizer
core as a simultaneous container for the whole elementary group. -/
theorem le_point_core (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (x : Model) (hx : x ∈ X) (hx1 : x ≠ 1) :
    X ≤ (centralizer ({x} : Set Model)).pCoreIn 2 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hpure x hx hx1)
  have hm := le_kernel_of_conjugator X hpure hno g (by change g*a*g⁻¹ ∈ X; rwa [hg])
  rw [firstKernel_eq_firstCore,firstCore_conjugate] at hm
  change X ≤ (centralizer ({g*a*g⁻¹} : Set Model)).pCoreIn 2 at hm
  rwa [hg] at hm

private theorem core_normalizes_of_center_le (R X : Subgroup Model)
    [IsExtraspecial 2 R] (hXR : X ≤ R)
    (hZ : (center R).map R.subtype ≤ X) : R ≤ normalizer (X : Set Model) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  apply (commutator_mono le_rfl hXR).trans
  rw [← map_subtype_commutator]
  exact (map_mono (IsExtraspecial.quotient_elementary_abelian 2 R).commutator_le_center_of_central_quotient).trans hZ

private theorem center_element_cases (R : Subgroup Model) [IsExtraspecial 2 R]
    (z : R) (hz : z ∈ center R) (hz1 : z ≠ 1) {u : R}
    (hu : u ∈ center R) : u = 1 ∨ u = z := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · exact Or.inr (congrArg Subtype.val
      (((Nat.card_eq_two_iff' (1 : center R)).mp (IsExtraspecial.center_order_p 2 R)).unique
        (show (⟨u,hu⟩ : center R) ≠ 1 from fun h => hu1 (congrArg Subtype.val h))
        (show (⟨z,hz⟩ : center R) ≠ 1 from fun h => hz1 (congrArg Subtype.val h))))

private theorem core_shear (R : Subgroup Model) [IsExtraspecial 2 R]
    (z : R) (hz : z ∈ center R) (hz1 : z ≠ 1)
    (u : R) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ q : R, q*u*q⁻¹ = z*u := by
  have hunc : u ∉ center R := fun hu => (center_element_cases R z hz hz1 hu).elim hu1 huz
  obtain ⟨q,hq⟩ : ∃ q : R, q*u ≠ u*q := by
    by_contra! hh
    exact hunc (mem_center_iff.mpr hh)
  have hc : ⁅q,u⁆ ∈ center R :=
    (IsExtraspecial.quotient_elementary_abelian 2 R).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hc1 : ⁅q,u⁆ ≠ 1 := fun he => hq (commutatorElement_eq_one_iff_mul_comm.mp he)
  exact ⟨q,eq_mul_of_mul_inv_eq ((center_element_cases R z hz hz1 hc).resolve_left hc1)⟩

/-- The full point core, not only the selected elementary group, normalizes X. -/
theorem point_core_le_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (x : Model) (hx : x ∈ X) (hx1 : x ≠ 1) :
    (centralizer ({x} : Set Model)).pCoreIn 2 ≤ normalizer (X : Set Model) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hpure x hx hx1)
  let e := MulAut.conj g
  let R := firstCore.map e.toMonoidHom
  have hR : R = (centralizer ({x} : Set Model)).pCoreIn 2 := by
    change firstCore.map (MulAut.conj g).toMonoidHom = _
    rw [firstCore_conjugate]
    change (centralizer ({g*a*g⁻¹} : Set Model)).pCoreIn 2 = _
    rw [hg]
  let : IsExtraspecial 2 firstCore := firstCore_extraspecial
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv
    (firstCore.equivMapOfInjective e.toMonoidHom e.injective) inferInstance
  have hXR : X ≤ R := hR ▸ le_point_core X hpure hno x hx hx1
  have hzR : x ∈ R := hXR hx
  let z : R := ⟨x,hzR⟩
  have hz : z ∈ center R := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp ((pCoreIn_le 2 _) (hR ▸ u.property))
  have hz1 : z ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
  have hZ : (center R).map R.subtype ≤ X := by
    rintro u ⟨v,hv,rfl⟩
    rcases center_element_cases R z hz hz1 hv with rfl | rfl
    · exact X.one_mem
    · exact hx
  rw [← hR]
  exact core_normalizes_of_center_le R X hXR hZ

/-- A native core element performs the shear y ↦ xy on the whole source
subgroup; its membership in the actual whole normalizer is proved. -/
theorem normalizer_shear (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (x y : Model) (hx : x ∈ X) (hy : y ∈ X)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) :
    ∃ q ∈ normalizer (X : Set Model), (MulAut.conj q) y = x*y := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hpure x hx hx1)
  let e := MulAut.conj g
  let R := firstCore.map e.toMonoidHom
  have hR : R = (centralizer ({x} : Set Model)).pCoreIn 2 := by
    change firstCore.map (MulAut.conj g).toMonoidHom = _
    rw [firstCore_conjugate]
    change (centralizer ({g*a*g⁻¹} : Set Model)).pCoreIn 2 = _
    rw [hg]
  let : IsExtraspecial 2 firstCore := firstCore_extraspecial
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv
    (firstCore.equivMapOfInjective e.toMonoidHom e.injective) inferInstance
  have hXR : X ≤ R := hR ▸ le_point_core X hpure hno x hx hx1
  let z : R := ⟨x,hXR hx⟩
  have hz : z ∈ center R := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp ((pCoreIn_le 2 _) (hR ▸ u.property))
  obtain ⟨q,hq⟩ := core_shear R z hz
    (fun he => hx1 (congrArg Subtype.val he)) (⟨y,hXR hy⟩ : R)
    (fun he => hy1 (congrArg Subtype.val he)) (fun he => hyx (congrArg Subtype.val he))
  exact ⟨q,point_core_le_normalizer X hpure hno x hx hx1 (hR ▸ q.property),
    congrArg Subtype.val hq⟩

/-- The whole normalizer is transitive on nonidentity members of X. The
transporter is a shear from the intrinsic core at the product of the points. -/
theorem normalizer_transitive (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (x y : Model) (hx : x ∈ X) (hy : y ∈ X) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ normalizer (X : Set Model), (MulAut.conj g) x = y := by
  by_cases he : x = y
  · exact ⟨1,one_mem _,by simpa using he⟩
  have hxx : x*x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx
  have hz1 : y*x ≠ 1 := by
    intro hh
    have hh' := congrArg (fun z => z*x) hh
    have hyx : y = x := by simpa only [mul_assoc,hxx,mul_one,one_mul] using hh'
    exact he hyx.symm
  have hxz : x ≠ y*x := by
    intro hh
    exact hy1 (mul_right_cancel (show y*x = 1*x by simpa only [one_mul] using hh.symm))
  obtain ⟨q,hq,heq⟩ := normalizer_shear X hpure hno (y*x) x (X.mul_mem hy hx) hx hz1 hx1 hxz
  exact ⟨q,hq,by simpa only [mul_assoc,hxx,mul_one] using heq⟩

/-- There is no proper nontrivial subgroup of X invariant under its whole
normalizer. In particular one cannot select an invariant four-group. -/
theorem invariant_subgroup_eq_bot_or_eq (X Y : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (hYX : Y ≤ X) (hn : normalizer (X : Set Model) ≤ normalizer (Y : Set Model)) :
    Y = ⊥ ∨ Y = X := by
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  obtain ⟨y,hy⟩ := ne_bot_iff_exists_ne_one.mp hY
  have hy1 : (y : Model) ≠ 1 := fun he => hy (Subtype.ext he)
  apply Or.inr
  apply le_antisymm hYX
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ Y.one_mem
  obtain ⟨g,hg,he⟩ := normalizer_transitive X hpure hno y x (hYX y.property) hx hy1 hx1
  have heY := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  rw [← heY]
  exact ⟨y,y.property,he⟩

/-- In the task's order range, no plane of X is whole-normalizer invariant. -/
theorem no_invariant_plane (X Y : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (hYX : Y ≤ X) (hYcard : Nat.card Y = 4) :
    ¬ normalizer (X : Set Model) ≤ normalizer (Y : Set Model) := by
  intro hn
  rcases invariant_subgroup_eq_bot_or_eq X Y hpure hno hYX hn with h | h
  · simp [h] at hYcard
  · rw [h] at hYcard
    omega

/-- The intersection of the actual embedded two-cores at all nonidentity
members of X. Unlike a chosen plane, this construction is canonical. -/
@[expose] def commonCore (X : Subgroup Model) : Subgroup Model :=
  ⨅ x : Model, ⨅ (_ : x ∈ X), ⨅ (_ : x ≠ 1), (centralizer ({x} : Set Model)).pCoreIn 2

theorem mem_commonCore_iff (X : Subgroup Model) (u : Model) :
    u ∈ commonCore X ↔ ∀ x ∈ X, x ≠ 1 → u ∈ (centralizer ({x} : Set Model)).pCoreIn 2 := by
  simp only [commonCore,mem_iInf]

theorem le_commonCore (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X) : X ≤ commonCore X := by
  intro u hu
  apply (mem_commonCore_iff X u).mpr
  intro x hx hx1
  exact le_point_core X hpure hno x hx hx1 hu

theorem commonCore_le_point_core (X : Subgroup Model) (x : Model)
    (hx : x ∈ X) (hx1 : x ≠ 1) :
    commonCore X ≤ (centralizer ({x} : Set Model)).pCoreIn 2 := by
  intro u hu
  exact (mem_commonCore_iff X u).mp hu x hx hx1

theorem commonCore_le_centralizer (X : Subgroup Model) :
    commonCore X ≤ centralizer (X : Set Model) := by
  intro u hu x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · exact (mem_centralizer_singleton_iff.mp
      (pCoreIn_le 2 _ (commonCore_le_point_core X x hx hx1 hu))).symm

theorem commonCore_isPGroup (X : Subgroup Model) (hX : X ≠ ⊥) :
    IsPGroup 2 (commonCore X) := by
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hX
  exact (isPGroup_pCoreIn 2 _).to_le
    (commonCore_le_point_core X x x.property (fun he => hx (Subtype.ext he)))

private theorem point_core_map (x : Model) (e : Model ≃* Model) :
    ((centralizer ({x} : Set Model)).pCoreIn 2).map e.toMonoidHom =
      (centralizer ({e x} : Set Model)).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ e.injective,map_centralizer_equiv,Set.image_singleton]

/-- The entire source normalizer preserves the canonical core intersection. -/
theorem normalizer_le_commonCore_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (commonCore X : Set Model) := by
  apply le_normalizer_iff.mpr
  intro g hg u hu
  apply (mem_commonCore_iff X _).mpr
  intro x hx hx1
  let e := MulAut.conj g
  have hx' : e.symm x ∈ X := by
    have he := mem_normalizer_iff_map_conj_eq.mp ((normalizer (X : Set Model)).inv_mem hg)
    change X.map (MulAut.conj g⁻¹).toMonoidHom = X at he
    have hm := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx
    rw [he] at hm
    simpa only [e, MulAut.conj_symm_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hm
  have hx1' : e.symm x ≠ 1 := fun he => hx1 (by
    have hh := congrArg e he
    simpa only [MulEquiv.apply_symm_apply,map_one] using hh)
  have hm := mem_map_of_mem e.toMonoidHom
    ((mem_commonCore_iff X u).mp hu (e.symm x) hx' hx1')
  rw [point_core_map,MulEquiv.apply_symm_apply] at hm
  exact hm

/-- Maximal TWO-locality identifies the original normalizer with that of the
actual nontrivial core intersection; no named-local placement is assumed. -/
theorem maximal_normalizer_eq_commonCore_normalizer
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hX : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    normalizer (X : Set Model) = normalizer (commonCore X : Set Model) := by
  have hne : commonCore X ≠ ⊥ := by
    intro h
    exact hX (le_bot_iff.mp (h ▸ le_commonCore X hpure hno))
  exact hmax.eq_of_le ⟨commonCore X,hne,commonCore_isPGroup X hX,rfl⟩
    (normalizer_le_commonCore_normalizer X)

/-- The arbitrary radical consumer restricts along the unchanged ambient
normalizer after the canonical intersection reduction. Identifying this
normalizer with a named native local is still required by the final cover. -/
theorem radical_restriction_commonCore
    (P X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hP : P.IsPRadical 2) (hX : X ≠ ⊥)
    (hPX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ X)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    let M := normalizer (commonCore X : Set Model)
    IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  let M := normalizer (commonCore X : Set Model)
  have he : normalizer (X : Set Model) = M :=
    maximal_normalizer_eq_commonCore_normalizer X hX hpure hno hmax
  have hNM : normalizer (P : Set Model) ≤ M := hPX.trans he.le
  have hPM : P ≤ M := P.le_normalizer.trans hNM
  have hNN := hNM.trans M.le_normalizer
  have hc := hP.normalizer_core_subgroupOf M hPM hNN
  have hlocal : IsTwoLocal M := by rw [← he]; exact hmax.1
  refine ⟨hlocal,hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hc,map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
