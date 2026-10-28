module

public import Theory.AtlasPort.LinearGroups.G2.BinaryCore
public import Theory.AtlasPort.LinearGroups.G2.Parabolic
public import Theory.GroupTheory.PResidual.Defs

/-!
# An elementary eight and a moving cubic in the binary second parabolic

The parabolic is the actual root-defined singular-point stabilizer in the
split-octonion model. Its unipotent generators and Weyl involution normalize
the embedded elementary eight. The explicit element `rootE 1 * weylR` has
cube one, belongs to the two-residual, and moves the common central involution
of the two quaternion factors in `BinaryCore`.

The coordinate conjugation formulas prove normalization, and one matrix
entry witnesses the nontrivial action. Identification of the other parabolic
and its two-core is a separate calculation.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
Root conventions come from the licensed ATLAS port imported here.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Atlas.G2.BinaryCore
open Atlas.G2.Explicit

def involution : Coordinates := ⟨1,0,0,0,0⟩
theorem involution_ne_one : involution ≠ 1 := by decide +kernel
theorem involution_sq : involution ^ 2 = 1 := by decide +kernel

theorem involution_mem_elementary : involution ∈ elementaryCoordinates := by decide +kernel

theorem involution_mem_center : involution ∈ Subgroup.center Coordinates := by
  rw [quaternionData.center_eq]
  change involution ∈ leftEmbedding.range ∧ involution ∈ rightEmbedding.range
  decide +kernel

theorem embedding_involution : embedding involution = rootA 1 := by
  simp [embedding, parameters, involution, unipotentProduct]

def z : Model (ZMod 2) := rootA 1

theorem z_mem_elementary : z ∈ elementary := by
  exact ⟨involution, involution_mem_elementary, embedding_involution⟩

theorem z_ne_one : z ≠ 1 := by
  rw [z, ← embedding_involution]
  exact fun h => involution_ne_one (embedding_injective (h.trans embedding.map_one.symm))

def secondParabolic : Subgroup (Model (ZMod 2)) := parabolic

def movingActor : Model (ZMod 2) := rootE 1 * weylR

theorem movingActor_mem : movingActor ∈ secondParabolic :=
  parabolic.mul_mem (rootE_mem_parabolic _) weylR_mem_parabolic

theorem movingActor_cube : movingActor ^ 3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [movingActor, pow_succ, pow_zero, weylR, weylREquiv, weylRLinear,
    weylRApply, rootE, rootEEquiv, rootELinear, rootEApply]
  · have h : ∀ a b : ZMod 2, a+b+(a+b+b)=b := by decide +kernel
    exact h _ _
  · have h : ∀ a b : ZMod 2, a+b+b=a := by decide +kernel
    exact h _ _

theorem movingActor_moves : movingActor * z * movingActor⁻¹ ≠ z := by
  intro h
  have he := congrArg (fun g : Model (ZMod 2) => g.val (Atlas.SplitOctonion.basisVector 7) 2) h
  have hm : (movingActor*z*movingActor⁻¹).val (Atlas.SplitOctonion.basisVector 7) 2 = 1 := by
    decide +kernel
  have hz : z.val (Atlas.SplitOctonion.basisVector 7) 2 = 0 := by decide +kernel
  rw [hm,hz] at he
  exact one_ne_zero he

theorem movingActor_residual :
    (⟨movingActor, movingActor_mem⟩ : secondParabolic) ∈ pResidual 2 secondParabolic := by
  apply Subgroup.mem_sInf.mpr
  rintro N ⟨hN,hP⟩
  let := hN
  let a : secondParabolic := ⟨movingActor,movingActor_mem⟩
  let b := QuotientGroup.mk' N a
  have hb3 : b ^ 3 = 1 := by
    change (QuotientGroup.mk' N a) ^ 3 = 1
    rw [← map_pow]
    have ha : a ^ 3 = 1 := Subtype.ext movingActor_cube
    rw [ha, map_one]
  obtain ⟨k,hk⟩ := hP b
  apply (QuotientGroup.eq_one_iff a).mp
  change b = 1
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 3 (2^k) from
    (by decide : Nat.Coprime 3 2).pow_right k)
    (orderOf_dvd_of_pow_eq_one hb3) (orderOf_dvd_of_pow_eq_one hk)


def unipotentConjugate (t : Fin 6 → ZMod 2) (x : elementaryCoordinates) : Coordinates :=
  ⟨x.val.a+x.val.b*t 4+x.val.c*(t 3+t 4*t 5), x.val.b+x.val.c*t 5,x.val.c,0,0⟩

theorem unipotent_conjugate_parameters (t : Fin 6 → ZMod 2) (x : elementaryCoordinates) :
    unipotentProductParameters (unipotentProductParameters t (parameters x))
      (unipotentInverseParameters t) = parameters (unipotentConjugate t x) := by
  revert t x
  decide +kernel

theorem unipotent_normalizes_elementary : unipotent (K := ZMod 2) ≤ Subgroup.normalizer (elementary : Set (Model (ZMod 2))) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩ := hg
  obtain ⟨x,hx,rfl⟩ := hx
  refine ⟨unipotentConjugate t ⟨x,hx⟩, ⟨rfl,rfl⟩, ?_⟩
  change unipotentProduct (parameters (unipotentConjugate t ⟨x,hx⟩)) =
    unipotentProduct t * unipotentProduct (parameters x) * (unipotentProduct t)⁻¹
  rw [unipotentProduct_inv, unipotentProduct_mul, unipotentProduct_mul,
    unipotent_conjugate_parameters t ⟨x,hx⟩]

def weylConjugate (x : elementaryCoordinates) : Coordinates := ⟨x.val.b,x.val.a,x.val.c,0,0⟩

theorem weyl_conjugate_elementary (x : elementaryCoordinates) :
    (weylR : Model (ZMod 2)) * embedding x * weylR⁻¹ = embedding (weylConjugate x) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro j
  funext i
  simp only [Pi.basisFun_apply]
  revert x j i
  decide +kernel

theorem secondParabolic_normalizes_elementary : secondParabolic ≤ Subgroup.normalizer (elementary : Set (Model (ZMod 2))) := by
  have htorus : splitTorus (K := ZMod 2) ≤ Subgroup.normalizer (elementary : Set (Model (ZMod 2))) := by
    rintro g ⟨p,rfl⟩
    have hp : ∀ p : (ZMod 2)ˣ × (ZMod 2)ˣ, p = 1 := by decide +kernel
    rw [hp p, map_one]
    exact Subgroup.one_mem _
  have hw : (weylR : Model (ZMod 2)) ∈ Subgroup.normalizer (elementary : Set (Model (ZMod 2))) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro g
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨weylConjugate ⟨x,hx⟩, ⟨rfl,rfl⟩, (weyl_conjugate_elementary ⟨x,hx⟩).symm⟩
    · intro hg
      have hww : (weylR : Model (ZMod 2)) * weylR = 1 := by
        simpa [pow_two] using (weylR_sq (K := ZMod 2))
      have hh : ∀ a ∈ elementary, (weylR : Model (ZMod 2))*a*weylR⁻¹ ∈ elementary := by
        rintro _ ⟨x,hx,rfl⟩
        exact ⟨weylConjugate ⟨x,hx⟩, ⟨rfl,rfl⟩, (weyl_conjugate_elementary ⟨x,hx⟩).symm⟩
      have h := hh _ hg
      have heq : (weylR : Model (ZMod 2)) * (weylR * g * weylR⁻¹) * weylR⁻¹ = g := by
        calc
          _ = (weylR * weylR) * g * (weylR * weylR)⁻¹ := by group
          _ = g := by rw [hww]; simp
      rwa [heq] at h
  exact sup_le (sup_le unipotent_normalizes_elementary htorus)
    ((Subgroup.closure_le _).mpr (by simpa using hw))

end Atlas.G2.BinaryCore
