module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.G2Recognition.OddCharacteristic.Geometry.ModelInputs
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Theory.Representation.EndFieldRep

/-!
# Lifting inner conjugate generation through a binary normalizer

Let R act faithfully and irreducibly over the binary field, with R perfect.
Conjugation by its full linear normalizer descends faithfully through the
central quotient on involutions. Its whole kernel is the scalar centralizer,
which is abelian by Schur's lemma and the finite endomorphism field.

Containment of a perfect subgroup is reflected across an abelian kernel
centralizing that subgroup: lift two elements into the comparison subgroup,
and their commutator is unchanged by the two kernel factors. Applying this
to the specified model quotient lifts generation without increasing the number
of conjugates. All conjugators are lifted from the model through R/Z(R).
No scalar-linearity of the full normalizer or triviality of Z(R) is assumed.

This supplies the cover and scalar-kernel passage in the conjugate-generation
estimate of Guralnick–Malle, Classification of 2F-modules I, (2.6), used for the
odd G₂ branch of Proposition 4.6. The intrinsic generation bound remains an
explicit input; `Geometry` connects this transfer to `LargeFieldConjugateBound`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra commutatorElement
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd.Geometry

private theorem perfect_le_of_centralizing_abelian_kernel
    {G D : Type*} [Group G] [Group D] (f : G →* D) (P L : Subgroup G)
    [Group.IsPerfect P] (hc : f.ker ≤ centralizer (P : Set G))
    (ha : ∀ a ∈ f.ker, ∀ b ∈ f.ker, Commute a b)
    (hPL : P.map f ≤ L.map f) : P ≤ L := by
  rw [← Subgroup.commutator_eq_self (H := P)]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, haL, hax⟩ := hPL (mem_map_of_mem f hx)
  obtain ⟨b, hbL, hby⟩ := hPL (mem_map_of_mem f hy)
  let k := x⁻¹ * a
  let l := y⁻¹ * b
  have hk : k ∈ f.ker := by simp [k, MonoidHom.mem_ker, hax]
  have hl : l ∈ f.ker := by simp [l, MonoidHom.mem_ker, hby]
  have hky : Commute k y := (mem_centralizer_iff.mp (hc hk) y hy).symm
  have hxl : Commute x l := mem_centralizer_iff.mp (hc hl) x hx
  have hkl := ha k hk l hl
  have he : ⁅x * k, y * l⁆ = ⁅x, y⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      (hky.mul_right hkl).commutator_eq,
      commutatorElement_mul_right_eq_mul_conj, hxl.commutator_eq]
    simp [mul_assoc]
  rw [← he]
  have hxa : x * k = a := by simp [k]
  have hyb : y * l = b := by simp [l]
  rw [hxa, hyb, commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL)

variable {R S W : Type*} [Group R] [Group S]
  [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) R W) (hf : Function.Injective σ)

private theorem quotientAction_ker [Group.IsPerfect R]
    (e : R ⧸ center R ≃* S) :
    (PerfectNormalizer.quotientAction σ hf e).ker =
      (actionImage σ).normalizerMonoidHom.ker := by
  ext a
  change PerfectNormalizer.quotientAction σ hf e a = 1 ↔
    (actionImage σ).normalizerMonoidHom a = 1
  constructor
  · intro ha
    apply (MulAut.congr (PerfectNormalizer.imageEquiv σ hf).symm).injective
    apply MulAut.centralQuotientAction_injective e
    change MulAut.centralQuotientAction e
      (MulAut.congr (PerfectNormalizer.imageEquiv σ hf).symm
        ((actionImage σ).normalizerMonoidHom a)) = 1 at ha
    simpa only [map_one] using ha
  · intro ha
    change MulAut.centralQuotientAction e
      (MulAut.congr (PerfectNormalizer.imageEquiv σ hf).symm
        ((actionImage σ).normalizerMonoidHom a)) = 1
    rw [ha, map_one, map_one]

private theorem centralizer_commute [FiniteDimensional (ZMod 2) W]
    (hi : σ.IsIrreducible)
    (a b : (Module.End (ZMod 2) W)ˣ)
    (ha : a ∈ centralizer (actionImage σ : Set _))
    (hb : b ∈ centralizer (actionImage σ : Set _)) : Commute a b := by
  let := hi
  let j (c : centralizer (actionImage σ : Set (Module.End (ZMod 2) W)ˣ)) : IntertwiningMap σ σ := {
    toLinearMap := c.val.val
    isIntertwining' r := by
      have h := mem_centralizer_iff.mp c.property (σ.asGroupHom r) ⟨r, rfl⟩
      exact congrArg Units.val h.symm }
  let E := IntertwiningMap.equivAlgEnd (ρ := σ)
  have h : j ⟨a, ha⟩ * j ⟨b, hb⟩ = j ⟨b, hb⟩ * j ⟨a, ha⟩ := by
    apply E.injective
    exact (map_mul E _ _).trans ((mul_comm _ _).trans (map_mul E _ _).symm)
  apply Units.ext
  exact congrArg (fun f : IntertwiningMap σ σ => f.toLinearMap) h

private def componentHom : R →* linearNormalizer σ :=
  (Subgroup.inclusion (actionImage σ).le_normalizer).comp (actionHom σ)

private theorem componentHom_range :
    (componentHom σ).range = (actionImage σ).subgroupOf (linearNormalizer σ) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr⟩

private theorem quotientAction_componentHom
    (e : R ⧸ center R ≃* S) (r : R) :
    PerfectNormalizer.quotientAction σ hf e (componentHom σ r) =
      MulAut.conj (e (QuotientGroup.mk' (center R) r)) := by
  change MulAut.centralQuotientAction e
    (MulAut.congr (PerfectNormalizer.imageEquiv σ hf).symm
      ((actionImage σ).normalizerMonoidHom (componentHom σ r))) = _
  have h : (actionImage σ).normalizerMonoidHom (componentHom σ r) =
      MulAut.conj (PerfectNormalizer.imageEquiv σ hf r) := by
    ext x
    rfl
  rw [h, MulAut.congr_conj, MulEquiv.symm_apply_apply,
    MulAut.centralQuotientAction_conj]

private theorem quotientAction_ne_one [Group.IsPerfect R]
    (hi : σ.IsIrreducible) (e : R ⧸ center R ≃* S)
    (t : linearNormalizer σ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    PerfectNormalizer.quotientAction σ hf e t ≠ 1 := by
  let : IsElementaryAbelian 2 (zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have hj := PerfectNormalizer.quotientAction_injective_on_elementary σ hf hi e (zpowers t)
  intro h
  have h' : ((PerfectNormalizer.quotientAction σ hf e).comp (zpowers t).subtype)
      ⟨t, mem_zpowers t⟩ =
      ((PerfectNormalizer.quotientAction σ hf e).comp (zpowers t).subtype) 1 := by
    change PerfectNormalizer.quotientAction σ hf e t =
      PerfectNormalizer.quotientAction σ hf e 1
    simpa only [map_one] using h
  exact ht (congrArg Subtype.val (hj h'))

private theorem component_le_of_quotientAction_le [Group.IsPerfect R]
    [FiniteDimensional (ZMod 2) W] (hi : σ.IsIrreducible)
    (e : R ⧸ center R ≃* S) (L : Subgroup (linearNormalizer σ))
    (hL : (MulAut.conj : S →* MulAut S).range ≤
      L.map (PerfectNormalizer.quotientAction σ hf e)) :
    (actionImage σ).subgroupOf (linearNormalizer σ) ≤ L := by
  let P := (actionImage σ).subgroupOf (linearNormalizer σ)
  let q := PerfectNormalizer.quotientAction σ hf e
  let : Group.IsPerfect P := by
    rw [show P = (componentHom σ).range from (componentHom_range σ).symm]
    exact Group.IsPerfect.ofSurjective (componentHom σ).rangeRestrict_surjective
  apply perfect_le_of_centralizing_abelian_kernel q P L
  · intro a ha
    rw [quotientAction_ker, normalizerMonoidHom_ker] at ha
    apply mem_centralizer_iff.mpr
    intro p hp
    apply Subtype.ext
    exact mem_centralizer_iff.mp ha p.val hp
  · intro a ha b hb
    rw [quotientAction_ker, normalizerMonoidHom_ker] at ha hb
    apply Subtype.ext
    exact centralizer_commute σ hi a.val b.val ha hb
  · rintro _ ⟨p, hp, rfl⟩
    apply hL
    obtain ⟨r, hr⟩ : ∃ r, componentHom σ r = p := by
      have hp' : p ∈ (componentHom σ).range := by
        rw [componentHom_range]
        exact hp
      exact hp'
    rw [← hr]
    exact ⟨e (QuotientGroup.mk' (center R) r), quotientAction_componentHom σ hf e r |>.symm⟩

include hf in
/-- Lift intrinsic model generation to the literal full binary normalizer.
The central cover and outer involutions are unrestricted. -/
theorem normalizer_conjugate_generation [Group.IsPerfect R]
    [FiniteDimensional (ZMod 2) W] (hi : σ.IsIrreducible)
    (e : R ⧸ center R ≃* S) (n : ℕ) (hgen : InnerConjugateBound S n)
    (t : linearNormalizer σ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g : Fin n → linearNormalizer σ,
      (actionImage σ).subgroupOf (linearNormalizer σ) ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let q := PerfectNormalizer.quotientAction σ hf e
  obtain ⟨g, hg⟩ := hgen (q t) (quotientAction_ne_one σ hf hi e t ht ht2)
    (by rw [← map_pow, ht2, map_one])
  have hs : Function.Surjective (fun r : R => e (QuotientGroup.mk' (center R) r)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center R))
  choose r hr using fun i => hs (g i)
  let a : Fin n → linearNormalizer σ := fun i => componentHom σ (r i)
  refine ⟨a, component_le_of_quotientAction_le σ hf hi e _ ?_⟩
  have hqa (i) : q (a i) = MulAut.conj (g i) := by
    exact (quotientAction_componentHom σ hf e (r i)).trans
      (congrArg MulAut.conj (hr i))
  have he : (closure (Set.range fun i => a i * t * (a i)⁻¹)).map q =
      closure (Set.range fun i => MulAut.conj (g i) * q t * (MulAut.conj (g i))⁻¹) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, map_mul, map_inv, hqa]
  rw [he]
  exact hg

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd.Geometry
