module

public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Jordan.ClosedSubgroup
public import Theory.AlgebraicGroup.Jordan.FiniteOrder
public import Theory.AlgebraicGroup.Jordan.Intersection
public import Theory.AlgebraicGroup.Morphism.Power
public import Theory.AlgebraicGroup.Tori.Monomial
public import Theory.AlgebraicGroup.Tori.Power

universe u

/-! Semisimplicity of torus and subtorus elements. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma algebraicGroupIso_isSemisimpleElement_iff
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : AlgebraicGroup.Iso G H) (g : Variety.Point G) :
    IsSemisimpleElement G g ↔
      IsSemisimpleElement H (e.hom.onPoints g) := by
  constructor
  · exact morphism_preserves_semisimpleElement e.hom g
  · intro hg
    have hback := morphism_preserves_semisimpleElement e.inv
      (e.hom.onPoints g) hg
    simpa only [e.hom_inv_id] using hback

/-- Every element of a torus is semisimple. -/
public theorem IsTorus.all_semisimple
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T) :
    ∀ t : Variety.Point T, IsSemisimpleElement T t := by
  intro t
  rcases hT with ⟨n, ⟨e⟩⟩
  have hdiag := dVariety_all_semisimple n (e.inv.onPoints t)
  have himage :=
    (algebraicGroupIso_isSemisimpleElement_iff e (e.inv.onPoints t)).mp hdiag
  simpa only [e.inv_hom_id] using himage

/-- Every element of a subtorus is semisimple. -/
public lemma IsSubtorus.all_semisimple
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} (hT : IsSubtorus T) :
    ∀ t : Variety.Point T.carrierVariety,
      IsSemisimpleElement T.carrierVariety t :=
  IsTorus.all_semisimple hT

/-- If an algebraic-group morphism has torus kernel and torus target, then
every element of its source is semisimple. -/
public theorem semisimple_of_torus_kernel_to_torus
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : Theory.AlgebraicGroup.Morphism G T)
    (hker : IsSubtorus f.kernelClosedSubgroup)
    (hT : IsTorus T) :
    ∀ x : Variety.Point G, IsSemisimpleElement G x := by
  let K0 := f.kernelClosedSubgroup
  have hkerSemi : ∀ x, x ∈ f.kernel → IsSemisimpleElement G x := by
    intro x hx
    have hxK : x ∈ (K0 : Set (Variety.Point G)) := hx
    let xK : Variety.Point K0.carrierVariety :=
      K0.pointEquiv.symm ⟨x, hxK⟩
    have hxKsemi : IsSemisimpleElement K0.carrierVariety xK :=
      hker.all_semisimple xK
    exact (closedSubgroup_semisimpleElement_iff K0 hxK).mpr hxKsemi
  intro x
  let dG := jordanDecomposition x
  let imageDecomposition : JordanDecomposition (f.onPoints x) :=
    { semisimplePart := f.onPoints dG.semisimplePart
      unipotentPart := f.onPoints dG.unipotentPart
      eq_mul := by
        calc
          f.onPoints x = f.onPoints
              (dG.semisimplePart * dG.unipotentPart) :=
            congrArg f.onPoints dG.eq_mul
          _ = f.onPoints dG.semisimplePart *
              f.onPoints dG.unipotentPart := map_mul f.onPoints _ _
      commute := dG.commute.map f.onPoints
      semisimple := morphism_preserves_semisimpleElement f _ dG.semisimple
      unipotent := morphism_preserves_unipotentElement f _ dG.unipotent }
  let trivialDecomposition : JordanDecomposition (f.onPoints x) :=
    { semisimplePart := f.onPoints x
      unipotentPart := 1
      eq_mul := by simp
      commute := Commute.one_right _
      semisimple := hT.all_semisimple (f.onPoints x)
      unipotent := one_isUnipotentElement T }
  have himage : imageDecomposition = trivialDecomposition :=
    imageDecomposition.unique trivialDecomposition
  have hxuKer : dG.unipotentPart ∈ f.kernel := by
    change f.onPoints dG.unipotentPart = 1
    exact congrArg JordanDecomposition.unipotentPart himage
  have hxueq : dG.unipotentPart = 1 :=
    semisimple_unipotent_eq_one dG.unipotentPart
      (hkerSemi dG.unipotentPart hxuKer) dG.unipotent
  rw [dG.eq_mul, hxueq, mul_one]
  exact dG.semisimple

/-- Every kernel element of a finite-kernel morphism from a connected
algebraic group to a torus is semisimple. -/
public theorem connected_finiteKernel_to_torus_kernel_isSemisimple
    {G T : Variety k} [AlgebraicGroup G] [AlgebraicGroup T]
    (f : Theory.AlgebraicGroup.Morphism G T)
    (hG : Variety.IsConnected G)
    (hker : Finite f.kernel)
    (hT : IsTorus T) :
    ∀ x, x ∈ f.kernel → IsSemisimpleElement G x := by
  have hGcomm := connected_isMulCommutative_of_finiteKernel
    f hG hker hT.isMulCommutative
  intro x hx
  let xK : f.kernel := ⟨x, hx⟩
  let : Finite f.kernel := hker
  let n := orderOf xK
  have hn : 0 < n := orderOf_pos xK
  have hxpow : x ^ n = 1 :=
    congrArg Subtype.val (pow_orderOf_eq_one xK)
  by_cases hp : ringChar k = 0
  · apply finiteOrder_coprimeChar_implies_semisimple x n hn
    · rw [hp]
      exact fun h => (Nat.ne_of_gt hn) (Nat.eq_zero_of_zero_dvd h)
    · exact hxpow
  · let : Fact (Nat.Prime (ringChar k)) :=
      ⟨CharP.char_prime_of_ne_zero k hp⟩
    let powMor := commutativeNpowMorphism G hGcomm (ringChar k)
    have hTpowInj : Function.Injective
        (fun y : Variety.Point T => y ^ ringChar k) := by
      simpa only [pow_one] using
        (IsTorus.pow_primePower_bijective hT (ringChar k) 1).1
    have hpowKerSubset : powMor.kernel ≤ f.kernel := by
      intro y hy
      have hypow : y ^ ringChar k = 1 := by
        change powMor.onPoints y = 1 at hy
        change (npowMorphism G (ringChar k)).toFun y = 1 at hy
        rwa [npowMorphism_apply] at hy
      change f.onPoints y = 1
      apply hTpowInj
      change f.onPoints y ^ ringChar k = 1 ^ ringChar k
      rw [← map_pow, hypow]
      simp
    have hpowKerFinite : Finite powMor.kernel := by
      let embed : powMor.kernel → f.kernel := fun y =>
        ⟨y.1, hpowKerSubset y.2⟩
      exact Finite.of_injective embed (by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : f.kernel => z.1) hab)
    have hpowSurj : Function.Surjective powMor.onPoints := by
      have : Finite
          (Variety.Point powMor.kernelClosedSubgroup.carrierVariety) :=
        (powMor.kernelClosedSubgroup.pointEquiv.finite_iff).2 hpowKerFinite
      have hkerDim :
          Variety.dimension powMor.kernelClosedSubgroup.carrierVariety = 0 :=
        (dimension_zero_iff_finite_points
          powMor.kernelClosedSubgroup.carrierVariety).2 inferInstance
      have himageDim :
          Variety.dimension powMor.imageClosedSubgroup.carrierVariety =
            Variety.dimension G := by
        have hdim := morphism_dimension_eq_kernel_add_image powMor
        rw [hkerDim, zero_add] at hdim
        exact hdim.symm
      have hcontains :=
        (closedSubgroup_dimension_eq_iff_contains_identityComponent
          G powMor.imageClosedSubgroup).mp himageDim
      have hidentity : identityComponent G = Set.univ :=
        (identityComponent_eq_univ_iff_isConnected G).mpr hG
      intro z
      have hz : z ∈ powMor.imageClosedSubgroup.toSubgroup := by
        apply hcontains
        rw [hidentity]
        trivial
      change z ∈ powMor.image at hz
      exact hz
    let powK : f.kernel → f.kernel := fun y => y ^ ringChar k
    have hpowKSurj : Function.Surjective powK := by
      intro z
      obtain ⟨y, hy⟩ := hpowSurj z.1
      have hypow : y ^ ringChar k = z.1 := by
        change (npowMorphism G (ringChar k)).toFun y = z.1 at hy
        rwa [npowMorphism_apply] at hy
      have hyker : y ∈ f.kernel := by
        change f.onPoints y = 1
        apply hTpowInj
        change f.onPoints y ^ ringChar k = 1 ^ ringChar k
        rw [← map_pow, hypow]
        have hzker := z.property
        change f.onPoints z.1 = 1 at hzker
        simpa only [one_pow] using hzker
      refine ⟨⟨y, hyker⟩, ?_⟩
      apply Subtype.ext
      exact hypow
    have hpowKInj : Function.Injective powK :=
      (Finite.injective_iff_surjective).2 hpowKSurj
    have hnchar : ¬ ringChar k ∣ n := by
      intro hdiv
      have hcard : ringChar k ∣ Nat.card f.kernel :=
        hdiv.trans (orderOf_dvd_natCard xK)
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
        (G := f.kernel) (ringChar k) hcard
      have hzpow : powK z = powK 1 := by
        change z ^ ringChar k = (1 : f.kernel) ^ ringChar k
        rw [one_pow, ← hz]
        exact pow_orderOf_eq_one z
      have hzone : z = 1 := hpowKInj hzpow
      have hone : ringChar k = 1 := by
        rw [← hz, hzone, orderOf_one]
      exact (Fact.out : Nat.Prime (ringChar k)).ne_one hone
    exact finiteOrder_coprimeChar_implies_semisimple x n hn hnchar hxpow

end Theory.AlgebraicGroup
