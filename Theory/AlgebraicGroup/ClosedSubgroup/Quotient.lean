module

public import Theory.AlgebraicGroup.PluckerOrbit.Eigenvalue
public import Theory.AlgebraicGroup.Quotient
public import Theory.AlgebraicGroup.Representations.Coinduction.Algebraic

universe u v w

set_option linter.style.haveILetI false
set_option linter.ambiguousOpen false

/-! Algebraic quotient realizations of normal closed subgroups. -/

/-! A connected quotient retained as a closed subgroup of a general linear group. -/

namespace Theory.AlgebraicGroup

section
variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.connectedQuotientGeneralLinear_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal) :
    ∃ (n : ℕ) (T : ClosedSubgroup (glVariety n : Variety k))
      (π : @AlgebraicGroup.Morphism k _ G T.carrierVariety
        (inferInstance : AlgebraicGroup G) T.carrierAlgebraicGroup),
      Function.Surjective
        (@AlgebraicGroup.Morphism.onPoints k _ G T.carrierVariety
          (inferInstance : AlgebraicGroup G) T.carrierAlgebraicGroup π) ∧
        @AlgebraicGroup.Morphism.kernel k _ G T.carrierVariety
          (inferInstance : AlgebraicGroup G) T.carrierAlgebraicGroup π = H.toSubgroup := by
  let n := Module.finrank k
    (Module.End k (Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan) → k))
  let f := H.rightTranslateVanishingPluckerConjugationMorphism
  let T := f.imageClosedSubgroup
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let hmap : ∀ x, f.onPoints x ∈ T.toSubgroup := fun x => ⟨x, rfl⟩
  let π := f.codRestrictClosedSubgroup T hmap
  refine ⟨n, T, π, ?_, ?_⟩
  · exact f.codRestrictImageClosedSubgroup_surjective hmap
  · change (f.codRestrictClosedSubgroup T hmap).kernel = H.toSubgroup
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_kernel_eq]
    exact H.rightTranslateVanishingPluckerConjugationMorphism_kernel_eq_of_connected hG hN

end

/-! The identity-component quotient retained inside a general linear group. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.identityComponentQuotientGeneralLinear_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
    letI : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
    let N := G0.inclusion.closedSubgroupPreimage H
    ∃ (n : ℕ) (T : ClosedSubgroup (glVariety n : Variety k))
      (π : @AlgebraicGroup.Morphism k _ G0.carrierVariety T.carrierVariety
        G0.carrierAlgebraicGroup T.carrierAlgebraicGroup),
      Function.Surjective
        (@AlgebraicGroup.Morphism.onPoints k _ G0.carrierVariety T.carrierVariety
          G0.carrierAlgebraicGroup T.carrierAlgebraicGroup π) ∧
        @AlgebraicGroup.Morphism.kernel k _ G0.carrierVariety T.carrierVariety
          G0.carrierAlgebraicGroup T.carrierAlgebraicGroup π = N.toSubgroup := by
  dsimp only
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  letI : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
  let N := G0.inclusion.closedSubgroupPreimage H
  have hN0 : N.toSubgroup.Normal := by
    change (H.toSubgroup.comap G0.inclusion.onPoints).Normal
    exact hN.comap G0.inclusion.onPoints
  exact N.connectedQuotientGeneralLinear_exists
    (identityComponentClosedSubgroup_carrier_isConnected G) hN0

end

/-! A connected ambient group admits a closed-image projection with prescribed normal kernel. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.connectedQuotientProjection_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (π : AlgebraicGroup.Morphism G Q),
      Function.Surjective π.onPoints ∧ π.kernel = H.toSubgroup := by
  let f := H.rightTranslateVanishingPluckerConjugationMorphism
  let T := f.imageClosedSubgroup
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let hmap : ∀ x, f.onPoints x ∈ T.toSubgroup := fun x => ⟨x, rfl⟩
  let π := f.codRestrictClosedSubgroup T hmap
  refine ⟨T.carrierVariety, inferInstance, π, ?_, ?_⟩
  · exact f.codRestrictImageClosedSubgroup_surjective hmap
  · change (f.codRestrictClosedSubgroup T hmap).kernel = H.toSubgroup
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_kernel_eq]
    exact H.rightTranslateVanishingPluckerConjugationMorphism_kernel_eq_of_connected hG hN

end

/-! The connected-core quotient projection for an arbitrary normal closed subgroup. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.identityComponentQuotientProjection_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
    letI : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
    let N := G0.inclusion.closedSubgroupPreimage H
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (π : AlgebraicGroup.Morphism G0.carrierVariety Q),
      Function.Surjective π.onPoints ∧ π.kernel = N.toSubgroup := by
  dsimp only
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  letI : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
  let N := G0.inclusion.closedSubgroupPreimage H
  have hN0 : N.toSubgroup.Normal := by
    change (H.toSubgroup.comap G0.inclusion.onPoints).Normal
    exact hN.comap G0.inclusion.onPoints
  exact N.connectedQuotientProjection_exists
    (identityComponentClosedSubgroup_carrier_isConnected G) hN0

end

/-! The point-group quotient homomorphism on `H G°`. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The quotient on `G°` extends group-theoretically to `H G°`, with exact
point kernel `H` and the expected restriction to `G°`. -/
lemma ClosedSubgroup.withIdentityComponentQuotientPointHom_exists
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (H : ClosedSubgroup G) (hN : H.toSubgroup.Normal)
    (π : AlgebraicGroup.Morphism
      (AlgebraicGroup.identityComponentClosedSubgroup G).carrierVariety Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel =
      ((AlgebraicGroup.identityComponentClosedSubgroup G).inclusion.closedSubgroupPreimage H).toSubgroup) :
    let K := H.withIdentityComponent
    let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
    ∃ ψ : Variety.Point K.carrierVariety →* Variety.Point Q,
      Function.Surjective ψ ∧
      (∀ x, ψ x = 1 ↔ K.inclusion.onPoints x ∈ H.toSubgroup) ∧
      ∀ x : Variety.Point G0.carrierVariety,
        ψ (K.pointEquiv.symm
          ⟨G0.inclusion.onPoints x, (show G0.toSubgroup ≤ H.toSubgroup ⊔ G0.toSubgroup from le_sup_right)
            (G0.pointEquiv x).property⟩) =
          π.onPoints x := by
  dsimp only
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  let K := H.withIdentityComponent
  let φ : G0.toSubgroup →* Variety.Point Q :=
    π.onPoints.comp (Equiv.mulEquiv G0.pointEquiv).symm.toMonoidHom
  have hφsurj : Function.Surjective φ := by
    exact hπsurj.comp (Equiv.mulEquiv G0.pointEquiv).symm.surjective
  have hφker : H.toSubgroup.subgroupOf G0.toSubgroup = φ.ker := by
    ext x
    change x.val ∈ H.toSubgroup ↔ φ x = 1
    change x.val ∈ H.toSubgroup ↔ π.onPoints (G0.pointEquiv.symm x) = 1
    change x.val ∈ H.toSubgroup ↔ G0.pointEquiv.symm x ∈ π.kernel
    rw [hπker]
    rfl
  let : H.toSubgroup.Normal := hN
  obtain ⟨ψ', hψ'surj, hψ'ker, hψ'restrict⟩ :=
    Subgroup.exists_surjective_supHom_of_ker_eq_subgroupOf
      H.toSubgroup G0.toSubgroup φ hφsurj hφker
  let ψ : Variety.Point K.carrierVariety →* Variety.Point Q :=
    ψ'.comp (Equiv.mulEquiv K.pointEquiv).toMonoidHom
  refine ⟨ψ, hψ'surj.comp (Equiv.mulEquiv K.pointEquiv).surjective, ?_, ?_⟩
  · intro x
    let kx : ↥(H.toSubgroup ⊔ G0.toSubgroup) :=
      ⟨K.inclusion.onPoints x, (K.pointEquiv x).property⟩
    change ψ' kx = 1 ↔ K.inclusion.onPoints x ∈ H.toSubgroup
    rw [← MonoidHom.mem_ker, hψ'ker]
    rfl
  · intro x
    change ψ' (Subgroup.inclusion
      (show G0.toSubgroup ≤ H.toSubgroup ⊔ G0.toSubgroup from le_sup_right)
      (G0.pointEquiv x)) = π.onPoints x
    exact hψ'restrict (G0.pointEquiv x)

end

/-! The algebraic quotient morphism on `H G°`. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The connected quotient projection extends regularly across the finite union
of components `H G°`, with exact kernel the pullback of `H`. -/
lemma ClosedSubgroup.withIdentityComponentQuotientMorphism_exists
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (H : ClosedSubgroup G) (hN : H.toSubgroup.Normal)
    (π : AlgebraicGroup.Morphism
      (AlgebraicGroup.identityComponentClosedSubgroup G).carrierVariety Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel =
      ((AlgebraicGroup.identityComponentClosedSubgroup G).inclusion.closedSubgroupPreimage H).toSubgroup) :
    let K := H.withIdentityComponent
    let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
    ∃ q : AlgebraicGroup.Morphism K.carrierVariety Q,
      Function.Surjective q.onPoints ∧
      q.kernel = (K.inclusion.closedSubgroupPreimage H).toSubgroup ∧
      ∀ x : Variety.Point G0.carrierVariety,
        q.onPoints (K.pointEquiv.symm
          ⟨G0.inclusion.onPoints x,
            (show G0.toSubgroup ≤ H.toSubgroup ⊔ G0.toSubgroup from le_sup_right)
              (G0.pointEquiv x).property⟩) = π.onPoints x := by
  dsimp only
  classical
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  let K := H.withIdentityComponent
  obtain ⟨ψ, hψsurj, hψker, hψrestrict⟩ :=
    H.withIdentityComponentQuotientPointHom_exists hN π hπsurj hπker
  let : G0.toSubgroup.Normal := by
    simpa [G0, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  let F := Variety.Point G ⧸ G0.toSubgroup
  let : Finite F := by
    dsimp [F, G0]
    exact finite_quotient_identityComponentSubgroup G
  letI : Fintype F := Fintype.ofFinite F
  let c : Variety.Point K.carrierVariety → F := fun x =>
    QuotientGroup.mk' G0.toSubgroup (K.inclusion.onPoints x)
  have hc (z : F) : IsClopen {x | c x = z} := by
    have hz := identityComponentQuotientFiber_isClopen G z
    constructor
    · exact hz.isClosed.preimage K.inclusion.toVariety.continuous
    · exact hz.isOpen.preimage K.inclusion.toVariety.continuous
  let hasRep (z : F) : Prop :=
    ∃ h : Variety.Point G, h ∈ H.toSubgroup ∧
      QuotientGroup.mk' G0.toSubgroup h = z
  let rep (z : F) : Variety.Point G :=
    if hz : hasRep z then Classical.choose hz else 1
  have rep_spec (z : F) (hz : hasRep z) :
      rep z ∈ H.toSubgroup ∧ QuotientGroup.mk' G0.toSubgroup (rep z) = z := by
    simp only [rep, dif_pos hz]
    exact Classical.choose_spec hz
  have hasRep_c (x : Variety.Point K.carrierVariety) : hasRep (c x) := by
    have hxK := (K.pointEquiv x).property
    obtain ⟨h, hh, g, hg, hprod⟩ := (H.mem_withIdentityComponent_iff _).mp hxK
    refine ⟨h, hh, ?_⟩
    apply QuotientGroup.eq.mpr
    change h⁻¹ * (K.pointEquiv x).val ∈ G0.toSubgroup
    rw [← hprod]
    simpa [G0, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using hg
  let branchPolynomial (z : F) (j : Q.Coordinates) :
      MvPolynomial K.carrierVariety.Coordinates k :=
    MvPolynomial.bind₁
      (fun i => Classical.choose
        ((AlgebraicGroup.leftMulMorphism G (rep z)⁻¹).regular i))
      (Classical.choose (π.toVariety.regular j))
  have hbranch (z : F) (x : Variety.Point K.carrierVariety)
      (hx : c x = z) (j : Q.Coordinates) :
      (ψ x).val j = evalPolynomial x.val (branchPolynomial z j) := by
    have hrep0 := rep_spec (c x) (hasRep_c x)
    have hrep : rep z ∈ H.toSubgroup ∧
        QuotientGroup.mk' G0.toSubgroup (rep z) = z := by
      simpa [hx] using hrep0
    have hg : (rep z)⁻¹ * K.inclusion.onPoints x ∈ G0.toSubgroup := by
      apply QuotientGroup.eq.mp
      calc
        QuotientGroup.mk' G0.toSubgroup (rep z) = z := hrep.2
        _ = c x := hx.symm
        _ = QuotientGroup.mk' G0.toSubgroup (K.inclusion.onPoints x) := rfl
    let gx : Variety.Point G0.carrierVariety :=
      G0.pointEquiv.symm ⟨(rep z)⁻¹ * K.inclusion.onPoints x, hg⟩
    let hxrep : Variety.Point K.carrierVariety :=
      K.pointEquiv.symm ⟨rep z,
        (show H.toSubgroup ≤ H.toSubgroup ⊔ G0.toSubgroup from le_sup_left) hrep.1⟩
    let hxg : Variety.Point K.carrierVariety :=
      K.pointEquiv.symm ⟨(rep z)⁻¹ * K.inclusion.onPoints x,
        (show G0.toSubgroup ≤ H.toSubgroup ⊔ G0.toSubgroup from le_sup_right) hg⟩
    have hxmul : hxrep * hxg = x := by
      apply K.inclusion_injective
      change rep z * ((rep z)⁻¹ * K.inclusion.onPoints x) = K.inclusion.onPoints x
      group
    have hkill : ψ hxrep = 1 := by
      rw [hψker]
      change rep z ∈ H.toSubgroup
      exact hrep.1
    have hrest : ψ hxg = π.onPoints gx := by
      have h := hψrestrict gx
      change ψ (K.pointEquiv.symm _) = π.onPoints gx at h
      exact h
    calc
      (ψ x).val j = (ψ (hxrep * hxg)).val j := by rw [hxmul]
      _ = (ψ hxrep * ψ hxg).val j := by rw [ψ.map_mul]
      _ = (π.onPoints gx).val j := by rw [hkill, hrest, one_mul]
      _ = evalPolynomial gx.val (Classical.choose (π.toVariety.regular j)) :=
        Classical.choose_spec (π.toVariety.regular j) gx
      _ = evalPolynomial x.val (branchPolynomial z j) := by
        simp only [branchPolynomial]
        rw [evalPolynomial_bind₁]
        congr 1
        funext i
        change (((rep z)⁻¹ * K.inclusion.onPoints x).val i) =
          evalPolynomial (K.inclusion.onPoints x).val
            (Classical.choose
              ((AlgebraicGroup.leftMulMorphism G (rep z)⁻¹).regular i))
        rw [← AlgebraicGroup.leftMulMorphism_apply]
        exact Classical.choose_spec
          ((AlgebraicGroup.leftMulMorphism G (rep z)⁻¹).regular i)
          (K.inclusion.onPoints x)
  obtain ⟨f, hf⟩ := Variety.exists_morphism_of_finite_clopen_coordinatewise
    c hc ψ branchPolynomial hbranch
  let q : AlgebraicGroup.Morphism K.carrierVariety Q :=
    { toVariety := f
      map_one := by
        rw [hf]
        exact ψ.map_one
      map_mul := by
        intro x y
        rw [hf]
        exact ψ.map_mul x y }
  refine ⟨q, ?_, ?_, ?_⟩
  · change Function.Surjective f.toFun
    rw [hf]
    exact hψsurj
  · ext x
    change f.toFun x = 1 ↔ x ∈ (K.inclusion.closedSubgroupPreimage H).toSubgroup
    rw [hf, hψker]
    rfl
  · intro x
    change f.toFun _ = π.onPoints x
    rw [hf]
    exact hψrestrict x

end

/-! A regular linear representation of `H G°` with kernel `H`. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.withIdentityComponentGeneralLinearRepresentation_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    let K := H.withIdentityComponent
    ∃ (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k)),
      ρ.kernel = (H.withIdentityComponent.inclusion.closedSubgroupPreimage H).toSubgroup := by
  dsimp only
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  letI : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
  let N := G0.inclusion.closedSubgroupPreimage H
  obtain ⟨n, T, π, hπsurj, hπker⟩ :=
    H.identityComponentQuotientGeneralLinear_exists hN
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  obtain ⟨q, hqsurj, hqker, hqrestrict⟩ :=
    H.withIdentityComponentQuotientMorphism_exists hN π hπsurj hπker
  let iT : AlgebraicGroup.Morphism T.carrierVariety (glVariety n : Variety k) :=
    @ClosedSubgroup.inclusion k _ (glVariety n : Variety k) (glAlgebraicGroup n) T
  let ρ : AlgebraicGroup.Morphism H.withIdentityComponent.carrierVariety
      (glVariety n : Variety k) := iT.comp q
  refine ⟨n, ρ, ?_⟩
  ext x
  change iT.onPoints (q.onPoints x) = 1 ↔
    x ∈ (H.withIdentityComponent.inclusion.closedSubgroupPreimage H).toSubgroup
  constructor
  · intro hx
    have hqone : q.onPoints x = 1 := by
      apply T.inclusion_injective
      simpa [iT] using hx
    have hxker : x ∈ q.kernel := hqone
    rw [hqker] at hxker
    exact hxker
  · intro hx
    have hxker : x ∈ q.kernel := by
      rw [hqker]
      exact hx
    have hqone : q.onPoints x = 1 := hxker
    rw [hqone, iT.onPoints.map_one]

end

/-! Exact kernel transfer for finite-index induction across an ambient normal subgroup. -/

open scoped MonoidAlgebra
open Representation

section

lemma Representation.ind_subtype_kernel_eq_of_normal
    {k : Type u} {G : Type v} [Field k] [Group G]
    (N S : Subgroup G) (hNS : N ≤ S) [N.Normal] [S.FiniteIndex]
    (A : Rep.{w} k S) [Nontrivial A]
    (hker : A.ρ.ker = N.subgroupOf S) :
    (Rep.ind S.subtype A).ρ.ker = N := by
  classical
  ext x
  constructor
  · intro hx
    have hind : (Rep.ind S.subtype A).ρ x = 1 := MonoidHom.mem_ker.mp hx
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have hm := congrArg (fun L : Module.End k (Rep.ind S.subtype A) =>
      L (Representation.IndV.mk S.subtype A.ρ 1 a)) hind
    change (Rep.ind S.subtype A).ρ x (Representation.IndV.mk S.subtype A.ρ 1 a) =
      Representation.IndV.mk S.subtype A.ρ 1 a at hm
    rw [Representation.ind_mk] at hm
    have hf := congrArg
      (fun z : Rep.ind S.subtype A => (Rep.indToCoind A z).1 x⁻¹) hm
    have hxS : x ∈ S := by
      by_contra hnot
      have hrel : ¬ (QuotientGroup.rightRel S).r x⁻¹ 1 := by
        simpa [QuotientGroup.rightRel_apply] using hnot
      have hleft :
          (Rep.indToCoind A (Representation.IndV.mk S.subtype A.ρ x⁻¹ a)).1 x⁻¹ = a := by
        simp [Rep.indToCoind, Rep.indToCoindAux, LinearMap.codRestrict,
          QuotientGroup.rightRel_apply]
        change (A.ρ (1 : S)) a = a
        simp
      have hright :
          (Rep.indToCoind A (Representation.IndV.mk S.subtype A.ρ 1 a)).1 x⁻¹ = 0 := by
        simp [Rep.indToCoind, Rep.indToCoindAux, hrel]
      have hf' :
          (Rep.indToCoind A (Representation.IndV.mk S.subtype A.ρ x⁻¹ a)).1 x⁻¹ =
            (Rep.indToCoind A (Representation.IndV.mk S.subtype A.ρ 1 a)).1 x⁻¹ := by
        simpa only [one_mul] using hf
      rw [hleft, hright] at hf'
      exact ha (by simpa using hf')
    let s : S := ⟨x, hxS⟩
    have hsind : (Rep.ind S.subtype A).ρ s.1 = 1 := by
      simpa [s] using hind
    have hA : A.ρ s = 1 :=
      Representation.ind_subtype_eq_one_imp S A s hsind
    have hsN : s ∈ N.subgroupOf S := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hA
    exact (Subgroup.mem_subgroupOf.mp hsN)
  · intro hx
    apply MonoidHom.mem_ker.mpr
    apply Representation.IndV.hom_ext
    intro g
    ext a
    change (Rep.ind S.subtype A).ρ x (Representation.IndV.mk S.subtype A.ρ g a) =
      Representation.IndV.mk S.subtype A.ρ g a
    rw [Representation.ind_mk]
    change (Representation.IndV.mk S.subtype A.ρ (g * x⁻¹)) a =
      (Representation.IndV.mk S.subtype A.ρ g) a
    let c : G := g * x⁻¹ * g⁻¹
    have hc : c ∈ N := by
      dsimp [c]
      exact (inferInstance : N.Normal).conj_mem x⁻¹ (N.inv_mem hx) g
    have hcs : c ∈ S := hNS hc
    have hca : A.ρ ⟨c, hcs⟩ a = a := by
      have hcmem : (⟨c, hcs⟩ : S) ∈ A.ρ.ker := by
        rw [hker]
        exact (Subgroup.mem_subgroupOf).mpr hc
      have hcop := MonoidHom.mem_ker.mp hcmem
      simpa using congrArg (fun L : Module.End k A => L a) hcop
    have hcg : c * g = g * x⁻¹ := by
      simp [c, mul_assoc]
    rw [← hcg]
    change (Representation.Coinvariants.mk _ _) = _
    let R := Representation.tprod ((Representation.leftRegular k G).comp S.subtype) A.ρ
    have hmk := Representation.Coinvariants.mk_self_apply (ρ := R) ⟨c, hcs⟩
      (MonoidAlgebra.single g 1 ⊗ₜ[k] a)
    simpa [R, Representation.tprod_apply, hca] using hmk

end

/-! A regular ambient general-linear representation with prescribed normal kernel. -/

section

open Representation

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.generalLinearMorphism_exactKernel_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∃ (m : ℕ) (F : AlgebraicGroup.Morphism G (glVariety m : Variety k)),
      F.kernel = H.toSubgroup := by
  let : H.toSubgroup.Normal := hN
  let : H.withIdentityComponent.toSubgroup.FiniteIndex :=
    H.withIdentityComponent_finiteIndex
  letI : Fintype (Variety.Point G ⧸ H.withIdentityComponent.toSubgroup) :=
    H.withIdentityComponent.toSubgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel
      H.withIdentityComponent.toSubgroup)) := inferInstance
  have hHK : H.toSubgroup ≤ H.withIdentityComponent.toSubgroup := by
    change H.toSubgroup ≤ H.toSubgroup ⊔ AlgebraicGroup.identityComponentSubgroup G
    exact le_sup_left
  by_cases hEq : H.toSubgroup = H.withIdentityComponent.toSubgroup
  · let ρ : AlgebraicGroup.Morphism H.withIdentityComponent.carrierVariety
        (glVariety 1 : Variety k) := {
      toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := by intro x y; exact (one_mul 1).symm }
    let A := Rep.of
      (H.withIdentityComponent.generalLinearMorphismRepresentation 1 ρ)
    have hAker : A.ρ.ker =
        H.toSubgroup.subgroupOf H.withIdentityComponent.toSubgroup := by
      ext x
      rw [MonoidHom.mem_ker,
        H.withIdentityComponent.generalLinearMorphismRepresentation_eq_one_iff]
      constructor
      · intro _
        rw [hEq]
        exact x.property
      · intro _
        rfl
    have hindker :
        (Rep.ind H.withIdentityComponent.toSubgroup.subtype A).ρ.ker = H.toSubgroup :=
      Representation.ind_subtype_kernel_eq_of_normal H.toSubgroup
        H.withIdentityComponent.toSubgroup hHK A hAker
    obtain ⟨F, -, hFker⟩ :=
      H.withIdentityComponent.coindRightQuotient_generalLinearMorphism_kernel_eq 1 ρ
    refine ⟨Module.finrank k
        (Quotient (QuotientGroup.rightRel H.withIdentityComponent.toSubgroup) →
          (Fin 1 → k)), F, ?_⟩
    rw [hFker, hindker]
  · obtain ⟨n, ρ, hρker⟩ :=
      H.withIdentityComponentGeneralLinearRepresentation_exists hN
    let A := Rep.of
      (H.withIdentityComponent.generalLinearMorphismRepresentation n ρ)
    have hAker : A.ρ.ker =
        H.toSubgroup.subgroupOf H.withIdentityComponent.toSubgroup := by
      ext x
      rw [MonoidHom.mem_ker,
        H.withIdentityComponent.generalLinearMorphismRepresentation_eq_one_iff]
      change H.withIdentityComponent.pointEquiv.symm x ∈ ρ.kernel ↔
        x.val ∈ H.toSubgroup
      rw [hρker]
      rfl
    have hn : n ≠ 0 := by
      intro hn
      subst n
      have hAtop : A.ρ.ker = ⊤ := by
        ext x
        simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
        exact Subsingleton.elim _ _
      have hsubtop : H.toSubgroup.subgroupOf
          H.withIdentityComponent.toSubgroup = ⊤ := by
        rw [← hAker, hAtop]
      apply hEq
      apply le_antisymm hHK
      intro x hx
      let y : H.withIdentityComponent.toSubgroup := ⟨x, hx⟩
      have hy : y ∈ H.toSubgroup.subgroupOf
          H.withIdentityComponent.toSubgroup := by
        rw [hsubtop]
        trivial
      exact hy
    let : NeZero n := ⟨hn⟩
    have hindker :
        (Rep.ind H.withIdentityComponent.toSubgroup.subtype A).ρ.ker = H.toSubgroup :=
      Representation.ind_subtype_kernel_eq_of_normal H.toSubgroup
        H.withIdentityComponent.toSubgroup hHK A hAker
    obtain ⟨F, -, hFker⟩ :=
      H.withIdentityComponent.coindRightQuotient_generalLinearMorphism_kernel_eq n ρ
    refine ⟨Module.finrank k
        (Quotient (QuotientGroup.rightRel H.withIdentityComponent.toSubgroup) →
          (Fin n → k)), F, ?_⟩
    rw [hFker, hindker]

end

/-! A surjective algebraic-group projection with prescribed normal kernel. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.closedImageProjection_exactKernel_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∃ (m : ℕ) (Q : ClosedSubgroup (glVariety m : Variety k)),
      letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
      ∃ π : AlgebraicGroup.Morphism G Q.carrierVariety,
        Function.Surjective π.onPoints ∧ π.kernel = H.toSubgroup := by
  obtain ⟨m, F, hFker⟩ := H.generalLinearMorphism_exactKernel_exists hN
  obtain ⟨π, hπsurj, hπker, -⟩ := F.closedImageProjection_exists
  exact ⟨m, F.imageClosedSubgroup, π, hπsurj, hπker.trans hFker⟩

end

/-! The point-group quotient property of the closed-image projection. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.closedImageProjection_pointLift_existsUnique
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∃ (m : ℕ) (Q : ClosedSubgroup (glVariety m : Variety k)),
      letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
      ∃ π : AlgebraicGroup.Morphism G Q.carrierVariety,
        Function.Surjective π.onPoints ∧ π.kernel = H.toSubgroup ∧
          ∀ (I : Variety k) [AlgebraicGroup I]
            (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
              ∃! ψ : Variety.Point Q.carrierVariety →* Variety.Point I,
                ψ.comp π.onPoints = φ.onPoints := by
  obtain ⟨m, Q, hQ⟩ := H.closedImageProjection_exactKernel_exists hN
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  obtain ⟨π, hπsurj, hπker⟩ := hQ
  refine ⟨m, Q, π, hπsurj, hπker, ?_⟩
  intro I _ φ hφ
  exact π.pointLift_existsUnique_of_surjective_kernel H hN hπsurj hπker φ hφ

end
end Theory.AlgebraicGroup
