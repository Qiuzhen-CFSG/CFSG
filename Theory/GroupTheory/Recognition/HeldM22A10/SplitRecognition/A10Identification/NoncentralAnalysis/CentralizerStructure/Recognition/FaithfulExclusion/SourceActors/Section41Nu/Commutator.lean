module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Geometry

/-!
# Compatibility of Held's initial actor with the chosen xi

Let A be conjugation by nu and put c = A(xi)*xi⁻¹. The induced actions of
nu and xi commute on S, so self-centralization of S puts c in S. The cube
relation gives A²(c)*A(c)*c = 1; inversion of nu by mu-prime gives
c^mu-prime = A²(c)⁻¹. On the sixteen binary words of S these equations force
c = 1 or c = tau*lambda. Thus xi^nu = xi or xi^nu = tau*lambda*xi.
A nonconjugacy hypothesis excludes the second possibility and gives every
field of `NuRelations`, for the original xi rather than a newly chosen one.

This replaces the additional subgroup argument in the last paragraph of
Held 4.1. It is conditional on the initial actor and the nonconjugacy; neither
ambient construction is inferred from the relations themselves.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.14 and 4.1, pp.231--232.
All finite calculations concern the sixteen local words and use kernel reduction.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private def sWord (b : Bit) (v : BaseCode) : H :=
  Coordinates.pi ^ v.1.val * Coordinates.mu ^ v.2.1.val *
    tau ^ v.2.2.1.val * normalizedLam b ^ v.2.2.2.val

-- Conjugation on the binary basis (pi, mu, tau, normalized lambda).
private def aCode (v : BaseCode) : BaseCode :=
  (v.1 + v.2.2.1, v.2.1 + v.2.2.1, v.1, v.1 + v.2.2.1 + v.2.2.2)
private def xCode (v : BaseCode) : BaseCode :=
  (v.1, v.2.1 + v.2.2.1 + v.2.2.2, v.2.2.1, v.2.2.2)
private def mCode (v : BaseCode) : BaseCode :=
  (v.1 + v.2.2.1, v.2.1 + v.2.2.2, v.2.2.1, v.2.2.2)
private def reCode (b : Bit) (v : BaseCode) : BaseCode :=
  (v.1 + b * v.2.2.2, v.2.1, v.2.2.1, v.2.2.2)

private theorem sWord_reCode : ∀ b v,
    sWord b v = Fusion.elementaryWord 1 (reCode b v) := by decide +kernel
private theorem reCode_twice : ∀ b v, reCode b (reCode b v) = v := by decide +kernel
private theorem aCode_three : ∀ v, aCode (aCode (aCode v)) = v := by decide +kernel
private theorem aCode_xCode : ∀ v, aCode (xCode v) = xCode (aCode v) := by decide +kernel
private theorem sWord_xi : ∀ b d v,
    (normalizedXi d)⁻¹ * sWord b v * normalizedXi d = sWord b (xCode v) := by
  decide +kernel
private theorem sWord_mup : ∀ b v,
    mup * sWord b v * mup = sWord b (mCode v) := by decide +kernel

private theorem sWord_image : ∀ b v,
    (Coordinates.pi * tau * normalizedLam b) ^ v.1.val * Coordinates.mu ^ v.2.1.val *
      (Coordinates.pi * Coordinates.mu * normalizedLam b) ^ v.2.2.1.val * normalizedLam b ^ v.2.2.2.val =
      sWord b (aCode v) := by decide +kernel

private theorem conj_commute {x g : G} (h : Commute g x) : g⁻¹ * x * g = x := by
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

variable {D e}
private theorem NuSeedRelations.conj_sWord {b : Bit} (n : NuSeedRelations D e b)
    (v : BaseCode) :
    (MulAut.conj n.nu⁻¹) (D.a10ModelEmbedding e (sWord b v)) =
      D.a10ModelEmbedding e (sWord b (aCode v)) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj n.nu⁻¹
  have hp : A (f Coordinates.pi) = f (Coordinates.pi * tau * normalizedLam b) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using n.pi_nu
  have ht : A (f tau) = f (Coordinates.pi * Coordinates.mu * normalizedLam b) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using n.tau_nu
  have hm : A (f Coordinates.mu) = f Coordinates.mu := by
    simpa only [A, MulAut.conj_apply, inv_inv] using conj_commute n.mu_commute
  have hl : A (f (normalizedLam b)) = f (normalizedLam b) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using conj_commute n.lam_commute
  change A (f (sWord b v)) = _
  calc
    _ = f ((Coordinates.pi * tau * normalizedLam b) ^ v.1.val * Coordinates.mu ^ v.2.1.val *
        (Coordinates.pi * Coordinates.mu * normalizedLam b) ^ v.2.2.1.val * normalizedLam b ^ v.2.2.2.val) := by
      simp only [sWord, map_mul, map_pow, hp, ht, hm, hl]
    _ = _ := congrArg f (sWord_image b v)

private theorem commute_mul_inv_of_conj_eq {u v s : G}
    (h : u⁻¹ * s * u = v⁻¹ * s * v) : Commute (u * v⁻¹) s := by
  have h' := congrArg (fun z => u * z * v⁻¹) h
  have : s * (u * v⁻¹) = (u * v⁻¹) * s := by
    simpa only [← mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, mul_one,
      mul_inv_cancel_right] using h'
  exact this.symm

private theorem NuSeedRelations.commutator_mem {b d : Bit} [Finite G]
    (n : NuSeedRelations D e b) :
    (MulAut.conj n.nu⁻¹) (D.a10ModelEmbedding e (normalizedXi d)) *
      (D.a10ModelEmbedding e (normalizedXi d))⁻¹ ∈ Fusion.ambientElementary D e 1 := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj n.nu⁻¹
  let x := f (normalizedXi d)
  let c := A x * x⁻¹
  have hA (v : BaseCode) : A (f (sWord b v)) = f (sWord b (aCode v)) :=
    n.conj_sWord v
  have hx (v : BaseCode) : x⁻¹ * f (sWord b v) * x = f (sWord b (xCode v)) := by
    simpa only [x, ← map_inv, ← map_mul] using congrArg f (sWord_xi b d v)
  have hc (v : BaseCode) : Commute c (f (sWord b (aCode v))) := by
    apply commute_mul_inv_of_conj_eq
    calc
      _ = A (x⁻¹ * f (sWord b v) * x) := by rw [map_mul, map_mul, map_inv, hA]
      _ = f (sWord b (aCode (xCode v))) := by rw [hx, hA]
      _ = x⁻¹ * f (sWord b (aCode v)) * x := by rw [hx, aCode_xCode]
  rw [← Fusion.ambientElementary_selfCentralizing D e 1]
  apply mem_centralizer_iff.mpr
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨v, rfl⟩ := (Fusion.mem_elementary 1 w).mp hw
  have he : f (Fusion.elementaryWord 1 v) = f (sWord b (reCode b v)) := by
    rw [sWord_reCode, reCode_twice]
  rw [he]
  have hh := hc (aCode (aCode (reCode b v)))
  rw [aCode_three] at hh
  exact hh.eq.symm

private theorem cube_conj (g : G) (hg : g ^ 3 = 1) (x : G) :
    (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) x)) = x := by
  have he : g * g * g = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hg
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (g * g * g)⁻¹ * x * (g * g * g) := by group
    _ = x := by rw [he]; group

/-- The seed relations realize the earlier normalizer action on the actual
ambient S, independently of xi's marking or ambient fusion. -/
public theorem NuSeedRelations.normalizes_S {b : Bit} (n : NuSeedRelations D e b) :
    n.nu ∈ normalizer (Fusion.ambientElementary D e 1 : Set G) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj n.nu⁻¹
  have hforward : ∀ x ∈ Fusion.ambientElementary D e 1,
      A x ∈ Fusion.ambientElementary D e 1 := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨v, rfl⟩ := (Fusion.mem_elementary 1 w).mp hw
    have he : f (Fusion.elementaryWord 1 v) = f (sWord b (reCode b v)) := by
      rw [sWord_reCode, reCode_twice]
    change A (f (Fusion.elementaryWord 1 v)) ∈ _
    rw [he, n.conj_sWord]
    refine ⟨sWord b (aCode (reCode b v)), ?_, rfl⟩
    change sWord b (aCode (reCode b v)) ∈ Fusion.elementary 1
    rw [Fusion.mem_elementary]
    exact ⟨reCode b (aCode (reCode b v)), (sWord_reCode b _).symm⟩
  apply mem_normalizer_iff''.mpr
  intro x
  suffices h : x ∈ Fusion.ambientElementary D e 1 ↔ A x ∈ Fusion.ambientElementary D e 1 by
    simpa only [A, MulAut.conj_apply, inv_inv] using h
  constructor
  · exact hforward x
  · intro hx
    have h := hforward _ (hforward _ hx)
    simpa only [A, cube_conj n.nu n.cube] using h

/-- The initial actor either fixes xi or conjugates it to tau*lambda*xi.
This holds for either marking of xi, without any ambient fusion assumption. -/
public theorem NuSeedRelations.xi_conjugation {b d : Bit} [Finite G]
    (n : NuSeedRelations D e b) :
    (MulAut.conj n.nu⁻¹) (D.a10ModelEmbedding e (normalizedXi d)) =
        D.a10ModelEmbedding e (normalizedXi d) ∨
      (MulAut.conj n.nu⁻¹) (D.a10ModelEmbedding e (normalizedXi d)) =
        D.a10ModelEmbedding e (coreTau b * normalizedXi d) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj n.nu⁻¹
  let x := f (normalizedXi d)
  let c := A x * x⁻¹
  let m := f mup
  let B := MulAut.conj m
  have hA (v : BaseCode) : A (f (sWord b v)) = f (sWord b (aCode v)) :=
    n.conj_sWord v
  have hcube (y : G) : A (A (A y)) = y := cube_conj n.nu n.cube y
  have hm : m⁻¹ = m := by
    have hh : mup⁻¹ = mup := by decide +kernel
    simpa only [m, ← map_inv] using congrArg f hh
  have hBnu : B n.nu = n.nu⁻¹ := by
    simpa only [B, MulAut.conj_apply, hm, m] using n.mup_inverts
  have hBx : B x = x := by
    have hh : ∀ d, mup * normalizedXi d * mup = normalizedXi d := by decide +kernel
    simpa only [B, x, m, MulAut.conj_apply, hm, ← map_mul] using congrArg f (hh d)
  have hBc : B c = (A (A c))⁻¹ := by
    have hcA : A (A c) = x * (A (A x))⁻¹ := by
      simp only [c, map_mul, map_inv, hcube]
    have hAi : A (A x) = n.nu * x * n.nu⁻¹ := by
      have h : n.nu⁻¹ * A (A x) * n.nu = x := by
        simpa only [A, MulAut.conj_apply, inv_inv] using hcube x
      calc
        _ = n.nu * (n.nu⁻¹ * A (A x) * n.nu) * n.nu⁻¹ := by group
        _ = _ := by rw [h]
    rw [hcA, hAi]
    have hcexp : c = n.nu⁻¹ * x * n.nu * x⁻¹ := by
      simp only [c, A, MulAut.conj_apply, inv_inv]
    rw [hcexp]
    rw [map_mul, map_mul, map_mul, map_inv, hBnu, inv_inv, hBx, map_inv, hBx]
    group
  have hnorm : A (A c) * A c * c = 1 := by
    simp only [c, map_mul, map_inv, hcube]
    group
  obtain ⟨w, hw, hc⟩ := n.commutator_mem (d := d)
  obtain ⟨v, hv⟩ := (Fusion.mem_elementary 1 w).mp hw
  have hv' : f (sWord b (reCode b v)) = c := by
    rw [sWord_reCode, reCode_twice, hv]
    exact hc
  generalize reCode b v = j at hv'
  have hBword : B (f (sWord b j)) = f (sWord b (mCode j)) := by
    simpa only [B, MulAut.conj_apply, hm, m, ← map_mul] using congrArg f (sWord_mup b j)
  have heB : sWord b (mCode j) = (sWord b (aCode (aCode j)))⁻¹ := by
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    rw [map_inv, ← hBword, hv', hBc, ← hv', hA, hA]
  have heN : sWord b (aCode (aCode j)) * sWord b (aCode j) * sWord b j = 1 := by
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    rw [map_one, map_mul, map_mul, ← hA, ← hA, hv']
    exact hnorm
  have hfinite : ∀ b j,
      sWord b (mCode j) = (sWord b (aCode (aCode j)))⁻¹ →
      sWord b (aCode (aCode j)) * sWord b (aCode j) * sWord b j = 1 →
      sWord b j = 1 ∨ sWord b j = coreTau b := by decide +kernel
  rcases hfinite b j heB heN with h | h
  · left
    have hc1 : c = 1 := by rw [← hv', h, map_one]
    exact mul_inv_eq_one.mp hc1
  · right
    have hct : c = f (coreTau b) := by rw [← hv', h]
    change A x = f (coreTau b * normalizedXi d)
    rw [map_mul]
    calc
      _ = c * x := by dsimp [c]; group
      _ = _ := by rw [hct]

/-- Excluding the second conjugation alternative supplies the required actor,
with precisely the original choices of lambda and xi. -/
public noncomputable def NuSeedRelations.toNuRelations {b d : Bit} [Finite G]
    (n : NuSeedRelations D e b)
    (hsep : ¬ IsConj (D.a10ModelEmbedding e (normalizedXi d))
      (D.a10ModelEmbedding e (coreTau b * normalizedXi d))) : NuRelations D e b d := by
  let f := D.a10ModelEmbedding e
  have hx : n.nu⁻¹ * f (normalizedXi d) * n.nu = f (normalizedXi d) := by
    rcases n.xi_conjugation (d := d) with h | h
    · simpa only [MulAut.conj_apply, inv_inv] using h
    · exact (hsep (isConj_iff.mpr ⟨n.nu⁻¹, h⟩)).elim
  refine
    { nu := n.nu
      cube := n.cube
      mu_commute := n.mu_commute
      xi_commute := ?_
      pi_nu := n.corePi_conjugation
      tau_nu := n.coreTau_conjugation }
  · show n.nu * f (normalizedXi d) = f (normalizedXi d) * n.nu
    calc
      _ = n.nu * (n.nu⁻¹ * f (normalizedXi d) * n.nu) := by rw [hx]
      _ = _ := by group

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
