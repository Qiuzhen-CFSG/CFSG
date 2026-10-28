module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.ModelInput
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.Representation.CentralizerField
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Lifting rank-three generation to the binary G₂ linear normalizer

Conjugation embeds each elementary normalizer subgroup into the automorphism
group of the actual action image. Faithfulness and the genuine conjugation
equivalence then identify it with an elementary subgroup of order eight in
G₂(2). A supplement obtained by derived conjugation of one of its elements
lifts to an involution of the original linear normalizer.

The conjugation kernel is abelian by Schur's lemma and the finite division-ring
theorem. It centralizes the perfect action image, so commutators lift subgroup
containment through this kernel; centrality in the whole normalizer is not
required. The conclusion uses the literal `normalizerActor` on the same space.

The finite coverage and word certificates in `Generation.FiniteSylow` discharge
the Sylow premise. Thus `rankThreeGeneration` supplies the normalizer witness
for every faithful irreducible binary representation, with no extra generation
hypothesis. The conditional model and Sylow lifts remain available separately.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11. The commutator lifting argument also appears in
`Theory.Representation.BinaryOffender.ThreeConjugateNormalizer.CentralCover`.
The actual G₂ conjugation equivalence and perfectness inherit the licensed
ATLAS root conventions through the imports.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2.LieAutomorphismExtensions
open scoped commutatorElement IsMulCommutative

private theorem lift_abelian_kernel {G D : Type*} [Group G] [Group D]
    (f : G →* D) (H J : Subgroup G) [Group.IsPerfect H]
    [IsMulCommutative f.ker]
    (hc : f.ker ≤ centralizer (H : Set G))
    (h : H.map f ≤ J.map f) : H ≤ J := by
  rw [← commutator_eq_self (H := H)]
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha, hfa⟩ := h (mem_map_of_mem f hx)
  obtain ⟨b, hb, hfb⟩ := h (mem_map_of_mem f hy)
  let k := a * x⁻¹
  let l := b * y⁻¹
  have hk : k ∈ f.ker := by simp only [k, MonoidHom.mem_ker, map_mul, map_inv, hfa, mul_inv_cancel]
  have hl : l ∈ f.ker := by simp only [l, MonoidHom.mem_ker, map_mul, map_inv, hfb, mul_inv_cancel]
  have hkx : Commute k x := (mem_centralizer_iff.mp (hc hk) x hx).symm
  have hky : Commute k y := (mem_centralizer_iff.mp (hc hk) y hy).symm
  have hlx : Commute l x := (mem_centralizer_iff.mp (hc hl) x hx).symm
  have hly : Commute l y := (mem_centralizer_iff.mp (hc hl) y hy).symm
  have hkl : Commute k l := congrArg Subtype.val (mul_comm (⟨k, hk⟩ : f.ker) ⟨l, hl⟩)
  have hkly := hkl.mul_right hky
  have hkcomm : Commute k ⁅x,l*y⁆ := by
    rw [commutatorElement_def]
    exact ((hkx.mul_right hkly).mul_right hkx.inv_right).mul_right hkly.inv_right
  have hlcomm : Commute l ⁅x,y⁆ := by
    rw [commutatorElement_def]
    exact ((hlx.mul_right hly).mul_right hlx.inv_right).mul_right hly.inv_right
  have he : ⁅k*x,l*y⁆ = ⁅x,y⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hkly.commutator_eq,
      mul_one, hkcomm.eq, mul_inv_cancel_right,
      commutatorElement_mul_right_eq_mul_conj, hlx.symm.commutator_eq,
      one_mul, hlcomm.eq, mul_inv_cancel_right]
  have hea : k*x = a := by simp [k]
  have heb : l*y = b := by simp [l]
  rw [hea, heb] at he
  rw [← he, commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private def normalizerConjugation {G : Type*} [Group G]
    (σ : Representation (ZMod 2) G V) :
    linearNormalizer σ →* MulAut (actionImage σ) :=
  (actionImage σ).normalizerMonoidHom

private theorem normalizerActor_le_of_conjugationImage_le
    {G : Type*} [Group G] [Group.IsPerfect G]
    (σ : Representation (ZMod 2) G V) [IsIrreducible σ]
    (J : Subgroup (linearNormalizer σ))
    (h : (normalizerActor σ).map (normalizerConjugation σ) ≤
      J.map (normalizerConjugation σ)) : normalizerActor σ ≤ J := by
  let f : linearNormalizer σ →* MulAut (actionImage σ) :=
    normalizerConjugation σ
  have hker (n : linearNormalizer σ) :
      n ∈ f.ker ↔ n.val ∈ CentralizerField.linearCentralizer σ := by
    change n ∈ (actionImage σ).normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  let C := CentralizerField.linearCentralizer σ
  let : IsCyclic (IntertwiningMap σ σ)ˣ := CentralizerField.units_isCyclic σ
  let : IsCyclic C := isCyclic_of_injective (CentralizerField.centralizerUnitsEquiv σ).toMonoidHom
    (CentralizerField.centralizerUnitsEquiv σ).injective
  let j : f.ker →* C :=
    (((linearNormalizer σ).subtype.comp f.ker.subtype).codRestrict C
      (fun n => (hker n).mp n.property))
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => c.val) h
  let : IsCyclic f.ker := isCyclic_of_injective j hj
  have hc : f.ker ≤ centralizer (normalizerActor σ : Set (linearNormalizer σ)) := by
    intro n hn
    apply mem_centralizer_iff.mpr
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp ((hker n).mp hn) a.val ha)
  let : Group.IsPerfect (actionImage σ) := Group.IsPerfect.range σ.asGroupHom
  let : Group.IsPerfect (normalizerActor σ) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (actionImage σ).le_normalizer).symm.toMonoidHom)
    (subgroupOfEquivOfLe (actionImage σ).le_normalizer).symm.surjective
  exact lift_abelian_kernel f (normalizerActor σ) J hc h

private def imageInclusion {G : Type*} [Group G]
    (σ : Representation (ZMod 2) G V) : G →* linearNormalizer σ :=
  (inclusion (actionImage σ).le_normalizer).comp σ.asGroupHom.rangeRestrict

private theorem lift_rank_three
    {G B : Type*} [Group G] [Group B] [Group.IsPerfect G]
    (σ : Representation (ZMod 2) G V) [IsIrreducible σ]
    (q : MulAut (actionImage σ) ≃* B) (j : G →* B)
    (hj : ∀ g, q (normalizerConjugation σ (imageInclusion σ g)) = j g)
    (hmodel : ∀ E : Subgroup B, IsElementaryAbelian 2 E → Nat.card E = 8 →
      ∃ a ∈ E, ∃ g : G, j.range ≤ E ⊔ zpowers (j g * a * (j g)⁻¹)) :
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A → rank A = 3 →
      ∃ t : linearNormalizer σ, t ^ 2 = 1 ∧ normalizerActor σ ≤ A ⊔ zpowers t := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let f : linearNormalizer σ →* B := q.toMonoidHom.comp (normalizerConjugation σ)
  let inc := imageInclusion σ
  have hinc (g : G) : f (inc g) = j g := hj g
  intro A hA hr
  let : IsElementaryAbelian 2 A := hA.2
  let fA := f.comp A.subtype
  have hfA : Function.Injective fA :=
    q.injective.comp (normalizer_elementary_conjugation_injective σ inferInstance A)
  have hEA : fA.range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hE : IsElementaryAbelian 2 fA.range :=
    IsElementaryAbelian.of_surjective fA.rangeRestrict fA.rangeRestrict_surjective
  have hcard : Nat.card fA.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfA).toEquiv]
    have hp : Nat.card A = 2 ^ rank A := hA.card_eq_two_pow_rank
    rw [hp, hr]
    decide
  obtain ⟨a, ha, g, hgen⟩ := hmodel fA.range hE hcard
  obtain ⟨aA, rfl⟩ := ha
  let t := inc g * (aA : linearNormalizer σ) * (inc g)⁻¹
  have ht : t ^ 2 = 1 := by
    have ha2 : (aA : linearNormalizer σ) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian _ aA.property
    change (MulAut.conj (inc g) aA.val) ^ 2 = 1
    simpa only [map_pow, map_one] using congrArg (MulAut.conj (inc g)) ha2
  refine ⟨t, ht, ?_⟩
  apply normalizerActor_le_of_conjugationImage_le σ (A ⊔ zpowers t)
  apply (map_le_map_iff_of_injective (f := q.toMonoidHom) q.injective).mp
  simp only [Subgroup.map_map]
  change (normalizerActor σ).map f ≤ (A ⊔ zpowers t).map f
  have hft : f t = j g * fA aA * (j g)⁻¹ := by
    simp only [t, map_mul, map_inv, hinc]
    rfl
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hft, ← hEA]
  apply le_trans _ hgen
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨x, hx⟩ := hn
  have he : inc x = n := Subtype.ext hx
  rw [← he, hinc]
  exact ⟨x, rfl⟩

/-- The concrete conjugate supplement lifts to the literal linear normalizer. -/
theorem rankThreeGeneration_of_model
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hmodel : ModelRankThreeGeneration) :
    RankThreeGeneration σ := by
  let : Group.IsPerfect Derived := by
    change Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2)))
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let e : Derived ≃* actionImage σ :=
    MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))
  let q : MulAut (actionImage σ) ≃* Atlas.G2.Model (ZMod 2) :=
    (MulAut.congr e.symm).trans binaryAutomorphismEquiv.symm
  apply lift_rank_three σ q Derived.subtype
  · intro g
    apply binaryAutomorphismEquiv.injective
    change binaryAutomorphismEquiv
      (binaryAutomorphismEquiv.symm
        (MulAut.congr e.symm (normalizerConjugation σ (imageInclusion σ g)))) = _
    rw [binaryAutomorphismEquiv.apply_symm_apply]
    have he : normalizerConjugation σ (imageInclusion σ g) = MulAut.conj (e g) := by
      ext x
      rfl
    rw [he, MulAut.congr_conj, e.symm_apply_apply]
    exact (binaryConjugation_inner g).symm
  · intro E hE hc
    obtain ⟨a, ha, g, hg⟩ := hmodel E hE hc
    refine ⟨a, ha, g, ?_⟩
    rw [Subgroup.range_subtype]
    exact hg

/-- The order-64 Sylow calculation supplies the exact linear-normalizer
witness required by the rank-three common-fixed-space consumer. -/
theorem rankThreeGeneration_of_sylow
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hSylow : SylowRankThreeGeneration) :
    RankThreeGeneration σ :=
  rankThreeGeneration_of_model σ hf (modelRankThreeGeneration_of_sylow hSylow)

/-- Every rank-three elementary subgroup of the literal linear normalizer has
an involution supplement generating over the actual action image. This
discharges the generation premise in the common-fixed-space argument of
GM I, Proposition 4.3, for every faithful irreducible binary representation. -/
theorem rankThreeGeneration
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) : RankThreeGeneration σ :=
  rankThreeGeneration_of_sylow σ hf sylowRankThreeGeneration

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
