module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.Axes

/-!
# Two conjugate Sylow groups in the marked orthogonal product

Every order-four subgroup preserving the two definite planes is the product of
two independent coordinate reflections. The two permutation signs give this
identification: the sign kernel has exponent three, while the subgroup has
order four. The original natural module therefore has exactly four common
fixed vectors. Conjugating by the actual rotation acting cubically on both
planes gives a second reflection in each plane, so the two conjugate subgroups
generate the full symmetric-three product.

These facts supply the index and two-conjugate-family premises for the literal
B.2.18 application on the source Thompson image in 15.4.12.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, B.2.18,
printed pp.80--81, and 15.4.12, printed pp.1160--1161.
-/

@[expose] public section
open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
open FamilySource.ModuleStructure.BaumannPair

private theorem card_four_pairSign_bijective (B : Subgroup OrthogonalFourBinary.IsometryGroup)
    (hB : B ≤ base) (hcard : Nat.card B = 4) :
    Function.Bijective (pairSign.comp (inclusion hB)) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro b hb
    have hr : b.val ∈ rotations := (pairSign_eq_one_iff (inclusion hB b)).mp hb
    obtain ⟨r,hr⟩ := hr
    have h3 : b.val ^ 3 = 1 := hr ▸ rotation_cube r
    have h4 : b.val ^ 4 = 1 := by
      have h : b ^ Nat.card B = 1 := pow_card_eq_one'
      rw [hcard] at h
      exact congrArg (fun b : B => b.val) h
    rw [show (4 : ℕ) = 3+1 from rfl, pow_succ, h3, one_mul] at h4
    exact Subtype.ext h4
  · rw [hcard,Nat.card_eq_fintype_card]
    decide

private theorem even_involution_trivial : ∀ p : S3,
    p ^ 2 = 1 → Equiv.Perm.sign p = 1 → p = 1 := by decide +kernel

private theorem odd_reflection : ∀ p : S3, Equiv.Perm.sign p = -1 →
    ∃ i : Fin 3, p = codePermutation (i,1) := by decide +kernel

private def leftReflection (i : Fin 3) : OrthogonalFourBinary.IsometryGroup :=
  productIsometry (codePermutation (i,1),1)
private def rightReflection (i : Fin 3) : OrthogonalFourBinary.IsometryGroup :=
  productIsometry (1,codePermutation (i,1))

private theorem leftReflection_code (i : Fin 3) :
    leftReflection i = codeMap ((i,1),(0,0),false) := by
  rw [leftReflection, ←planeEquiv_code (i,1)]
  have h0 : planeEquiv (planePermutation (0,0)) = 1 := by
    rw [planeEquiv_code]
    simp [codePermutation]
  rw [←h0, productIsometry_codes]
private theorem rightReflection_code (i : Fin 3) :
    rightReflection i = codeMap ((0,0),(i,1),false) := by
  rw [rightReflection, ←planeEquiv_code (i,1)]
  have h0 : planeEquiv (planePermutation (0,0)) = 1 := by
    rw [planeEquiv_code]
    simp [codePermutation]
  rw [←h0, productIsometry_codes]

private theorem four_group_reflections (B : Subgroup OrthogonalFourBinary.IsometryGroup)
    (hB : B ≤ base) (hcard : Nat.card B = 4) :
    ∃ i j : Fin 3, leftReflection i ∈ B ∧ rightReflection j ∈ B ∧
      ∀ g ∈ B, g = 1 ∨ g = leftReflection i ∨ g = rightReflection j ∨
        g = leftReflection i * rightReflection j := by
  let f := pairSign.comp (inclusion hB)
  have hf : Function.Bijective f := card_four_pairSign_bijective B hB hcard
  have hsquare (g : B) : g ^ 2 = 1 := by
    apply hf.1
    rw [map_pow,map_one]
    exact (show ∀ s : ℤˣ × ℤˣ, s^2=1 by decide) (f g)
  obtain ⟨a,ha⟩ := hf.2 (-1,1)
  obtain ⟨b,hb⟩ := hf.2 (1,-1)
  let pa := baseEquiv (inclusion hB a)
  let pb := baseEquiv (inclusion hB b)
  have hapa : Equiv.Perm.sign pa.1 = -1 ∧ Equiv.Perm.sign pa.2 = 1 :=
    ⟨congrArg Prod.fst ha,congrArg Prod.snd ha⟩
  have hpb : Equiv.Perm.sign pb.1 = 1 ∧ Equiv.Perm.sign pb.2 = -1 :=
    ⟨congrArg Prod.fst hb,congrArg Prod.snd hb⟩
  have hpa2 : pa^2=1 := by
    change (baseEquiv.toMonoidHom.comp (inclusion hB)) a ^2=1
    rw [←map_pow,hsquare,map_one]
  have hpb2 : pb^2=1 := by
    change (baseEquiv.toMonoidHom.comp (inclusion hB)) b ^2=1
    rw [←map_pow,hsquare,map_one]
  have hasecond : pa.2 = 1 := even_involution_trivial pa.2 (congrArg Prod.snd hpa2) hapa.2
  have hbfirst : pb.1 = 1 := even_involution_trivial pb.1 (congrArg Prod.fst hpb2) hpb.1
  obtain ⟨i,hi⟩ := odd_reflection pa.1 hapa.1
  obtain ⟨j,hj⟩ := odd_reflection pb.2 hpb.2
  have hea : a.val = leftReflection i := by
    have h := congrArg Subtype.val (baseEquiv.symm_apply_apply (inclusion hB a))
    change productIsometry pa = a.val at h
    rw [show pa = (codePermutation (i,1),1) from Prod.ext hi hasecond] at h
    exact h.symm
  have heb : b.val = rightReflection j := by
    have h := congrArg Subtype.val (baseEquiv.symm_apply_apply (inclusion hB b))
    change productIsometry pb = b.val at h
    rw [show pb = (1,codePermutation (j,1)) from Prod.ext hbfirst hj] at h
    exact h.symm
  refine ⟨i,j,hea ▸ a.property,heb ▸ b.property,?_⟩
  intro g hg
  let g' : B := ⟨g,hg⟩
  have hc : f g' = 1 ∨ f g' = (-1,1) ∨ f g' = (1,-1) ∨ f g' = (-1,-1) :=
    (show ∀ s : ℤˣ × ℤˣ, s=1 ∨s=(-1,1)∨s=(1,-1)∨s=(-1,-1) by decide) (f g')
  rcases hc with h | h | h | h
  · left
    exact congrArg Subtype.val (hf.1 (h.trans f.map_one.symm))
  · right; left
    exact (congrArg Subtype.val (hf.1 (h.trans ha.symm))).trans hea
  · right; right; left
    exact (congrArg Subtype.val (hf.1 (h.trans hb.symm))).trans heb
  · right; right; right
    have he : f g' = f (a*b) := by rw [map_mul,ha,hb,h]; rfl
    have he' := congrArg Subtype.val (hf.1 he)
    change g = a.val*b.val at he'
    rwa [hea,heb] at he'

/-- Every order-four subgroup of the plane-preserving group fixes exactly four
vectors in the original natural space. -/
theorem base_four_fixed_card (B : Subgroup OrthogonalFourBinary.IsometryGroup)
    (hB : B ≤ base) (hcard : Nat.card B = 4) : Nat.card (FixedVectors B) = 4 := by
  obtain ⟨i,j,hi,hj,hcases⟩ := four_group_reflections B hB hcard
  let e : FixedVectors B ≃ {v : Space //
      eval ((i,1),(0,0),false) v = v ∧ eval ((0,0),(j,1),false) v = v} :=
    (Equiv.refl Space).subtypeEquiv (fun v => by
    constructor
    · intro hv
      have ha := hv (leftReflection i) hi
      have hb := hv (rightReflection j) hj
      rw [leftReflection_code] at ha
      rw [rightReflection_code] at hb
      exact ⟨(candidate_eval _ v).symm.trans ha, (candidate_eval _ v).symm.trans hb⟩
    · rintro ⟨hv,hv'⟩ g hg
      have ha : (leftReflection i).val v = v := by
        rw [leftReflection_code]
        exact (candidate_eval _ v).trans hv
      have hb : (rightReflection j).val v = v := by
        rw [rightReflection_code]
        exact (candidate_eval _ v).trans hv'
      rcases hcases g hg with rfl | rfl | rfl | rfl
      · rfl
      · exact ha
      · exact hb
      · change (leftReflection i).val ((rightReflection j).val v)=v
        rw [hb,ha])
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]
  exact (show ∀ i j : Fin 3, Fintype.card {v : Space //
    eval ((i,1),(0,0),false) v=v ∧ eval ((0,0),(j,1),false) v=v}=4 by decide +kernel) i j

private def cubicPermutation : S3 := codePermutation (1,0)
private def cubicDiagonal : OrthogonalFourBinary.IsometryGroup :=
  rotationHom (Multiplicative.ofAdd (1,1))
private theorem cubicDiagonal_eq : cubicDiagonal = productIsometry (cubicPermutation,cubicPermutation) := by
  rw [cubicDiagonal,rotationHom_code]
  exact (productIsometry_codes (1,0) (1,0)).symm.trans (by
    simp only [planeEquiv_code,cubicPermutation])

private theorem reflection_generates {K : Type*} [Group K] (f : S3 →* K)
    (D : Subgroup K) (a : S3) (ha : Equiv.Perm.sign a = -1)
    (h1 : f a ∈ D) (h2 : f (cubicPermutation*a*cubicPermutation⁻¹) ∈ D) :
    ∀ p : S3, f p ∈ D := by
  intro p
  let b := cubicPermutation*a*cubicPermutation⁻¹
  have hcases : p=1∨p=a∨p=b∨p=a*b∨p=b*a∨p=a*b*a :=
    (show ∀ a p : S3, Equiv.Perm.sign a = -1 →
      p=1∨p=a∨p=cubicPermutation*a*cubicPermutation⁻¹∨
      p=a*(cubicPermutation*a*cubicPermutation⁻¹)∨
      p=(cubicPermutation*a*cubicPermutation⁻¹)*a∨
      p=a*(cubicPermutation*a*cubicPermutation⁻¹)*a by decide +kernel) a p ha
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [map_one] using D.one_mem
  · exact h1
  · exact h2
  · rw [map_mul]; exact D.mul_mem h1 h2
  · rw [map_mul]; exact D.mul_mem h2 h1
  · rw [map_mul,map_mul]; exact D.mul_mem (D.mul_mem h1 h2) h1

private def axisEmbedding (b : Bool) : S3 →* OrthogonalFourBinary.IsometryGroup where
  toFun p := productIsometry (if b then (1,p) else (p,1))
  map_one' := by cases b <;> exact productIsometry.map_one
  map_mul' p q := by cases b <;> simp [←map_mul]

/-- Two cubic-conjugate copies of any order-four subgroup generate the full
plane-preserving isometry group. The conjugator is an actual rotation. -/
theorem base_four_two_conjugates (B : Subgroup OrthogonalFourBinary.IsometryGroup)
    (hB : B ≤ base) (hcard : Nat.card B = 4) :
    ∃ r ∈ rotations, B ⊔ B.map (MulAut.conj r).toMonoidHom = base := by
  obtain ⟨i,j,hi,hj,_⟩ := four_group_reflections B hB hcard
  let r := cubicDiagonal
  have hr : r ∈ rotations := ⟨Multiplicative.ofAdd (1,1),rfl⟩
  let D := B ⊔ B.map (MulAut.conj r).toMonoidHom
  refine ⟨r,hr,le_antisymm ?_ ?_⟩
  · apply sup_le hB
    rintro _ ⟨b,hb,rfl⟩
    exact base.mul_mem (base.mul_mem (rotations_le_base hr) (hB hb))
      (base.inv_mem (rotations_le_base hr))
  · have haxis (b : Bool) (k : Fin 3) (hk : axisEmbedding b (codePermutation (k,1)) ∈ B) :
        ∀ p : S3, axisEmbedding b p ∈ D := by
      apply reflection_generates (axisEmbedding b) D (codePermutation (k,1))
      · exact (show ∀ k : Fin 3, Equiv.Perm.sign (codePermutation (k,1)) = -1 by decide +kernel) k
      · exact (le_sup_left : B≤D) hk
      · have hh : (MulAut.conj r) (axisEmbedding b (codePermutation (k,1))) ∈ D :=
          (le_sup_right : B.map (MulAut.conj r).toMonoidHom≤D) ⟨_,hk,rfl⟩
        have he : (MulAut.conj r) (axisEmbedding b (codePermutation (k,1))) =
            axisEmbedding b (cubicPermutation * codePermutation (k,1) * cubicPermutation⁻¹) := by
          change r * axisEmbedding b (codePermutation (k,1)) * r⁻¹ = _
          rw [show r = productIsometry (cubicPermutation,cubicPermutation) from cubicDiagonal_eq]
          cases b <;> simp [axisEmbedding,←map_inv,←map_mul]
        rwa [he] at hh
    have hleft := haxis false i hi
    have hright := haxis true j hj
    intro g hg
    obtain ⟨p,hp⟩ := productBase_surjective (⟨g,hg⟩ : base)
    have he : productIsometry p = g := congrArg Subtype.val hp
    have hh := D.mul_mem (hleft p.1) (hright p.2)
    change productIsometry (p.1,1) * productIsometry (1,p.2) ∈ D at hh
    rw [←map_mul] at hh
    simpa only [Prod.mk_mul_mk,mul_one,one_mul,he] using hh

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
