module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Geometry

/-!
# Normalizing inversion in the initial Held actor

An order-three element with the prescribed action on S can be conjugated by
1 or tau so that mu-prime inverts it. The discrepancy between its conjugate
by mu-prime and its inverse centralizes S, hence lies in S. Its norm and
mu-prime action restrict it to 1 or tau*lambda. In the second case conjugation
by tau removes the discrepancy. All calculations on S use its sixteen actual
binary words; no quotient lifting or additional normalizer premise is assumed.

This proves the inversion adjustment in the first paragraph of Held 4.1.
Constructing an element with the marked action remains an earlier obligation.
Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, printed p.232. Conjugation is g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The marked action before imposing inversion by mu-prime. -/
public structure NuActionRelations (b : Bit) where
  nu : G
  cube : nu ^ 3 = 1
  mu_commute : Commute nu (D.a10ModelEmbedding e Coordinates.mu)
  lam_commute : Commute nu (D.a10ModelEmbedding e (normalizedLam b))
  pi_nu : nu⁻¹ * D.a10ModelEmbedding e Coordinates.pi * nu =
    D.a10ModelEmbedding e (Coordinates.pi * Coordinates.tau * normalizedLam b)
  tau_nu : nu⁻¹ * D.a10ModelEmbedding e Coordinates.tau * nu =
    D.a10ModelEmbedding e (Coordinates.pi * Coordinates.mu * normalizedLam b)

private def sWord (b : Bit) (v : BaseCode) : H :=
  Coordinates.pi ^ v.1.val * Coordinates.mu ^ v.2.1.val *
    tau ^ v.2.2.1.val * normalizedLam b ^ v.2.2.2.val

-- Conjugation on the binary basis (pi, mu, tau, normalized lambda).
private def aCode (v : BaseCode) : BaseCode :=
  (v.1 + v.2.2.1, v.2.1 + v.2.2.1, v.1, v.1 + v.2.2.1 + v.2.2.2)
private def mCode (v : BaseCode) : BaseCode :=
  (v.1 + v.2.2.1, v.2.1 + v.2.2.2, v.2.2.1, v.2.2.2)
private def reCode (b : Bit) (v : BaseCode) : BaseCode :=
  (v.1 + b * v.2.2.2, v.2.1, v.2.2.1, v.2.2.2)

private theorem sWord_reCode : ∀ b v,
    sWord b v = Fusion.elementaryWord 1 (reCode b v) := by decide +kernel
private theorem reCode_twice : ∀ b v, reCode b (reCode b v) = v := by decide +kernel
private theorem aCode_three : ∀ v, aCode (aCode (aCode v)) = v := by decide +kernel
private theorem sWord_mup : ∀ b v,
    mup * sWord b v * mup = sWord b (mCode v) := by decide +kernel

private theorem sWord_image : ∀ b v,
    (Coordinates.pi * tau * normalizedLam b) ^ v.1.val * Coordinates.mu ^ v.2.1.val *
      (Coordinates.pi * Coordinates.mu * normalizedLam b) ^ v.2.2.1.val * normalizedLam b ^ v.2.2.2.val =
      sWord b (aCode v) := by decide +kernel

private theorem conj_commute {x g : G} (h : Commute g x) : g⁻¹ * x * g = x := by
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

variable {D e}
private theorem NuActionRelations.conj_sWord {b : Bit} (n : NuActionRelations D e b)
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

private theorem cube_conj (g : G) (hg : g ^ 3 = 1) (x : G) :
    (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) x)) = x := by
  have he : g * g * g = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hg
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (g * g * g)⁻¹ * x * (g * g * g) := by group
    _ = x := by rw [he]; group

private theorem aCode_mCode : ∀ v,
    mCode (aCode (mCode v)) = aCode (aCode v) := by decide +kernel

private theorem conj_twice_of_cube (g : G) (hg : g ^ 3 = 1) (x : G) :
    (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) x) = g * x * g⁻¹ := by
  have h : g⁻¹ * (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) x) * g = x := by
    simpa only [MulAut.conj_apply, inv_inv] using cube_conj g hg x
  calc
    _ = g * (g⁻¹ * (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) x) * g) * g⁻¹ := by group
    _ = _ := by rw [h]

private theorem NuActionRelations.defect_mem {b : Bit} [Finite G]
    (n : NuActionRelations D e b) :
    D.a10ModelEmbedding e mup * n.nu * D.a10ModelEmbedding e mup * n.nu ∈
      Fusion.ambientElementary D e 1 := by
  let f := D.a10ModelEmbedding e
  let m := f mup
  let A := MulAut.conj n.nu⁻¹
  have hm : m⁻¹ = m := by
    have h : mup⁻¹ = mup := by decide +kernel
    simpa only [m, ← map_inv] using congrArg f h
  have hM (v : BaseCode) : m * f (sWord b v) * m = f (sWord b (mCode v)) := by
    simpa only [m, ← map_mul] using congrArg f (sWord_mup b v)
  have hA (v : BaseCode) : n.nu⁻¹ * f (sWord b v) * n.nu =
      f (sWord b (aCode v)) := by
    simpa only [MulAut.conj_apply, inv_inv] using n.conj_sWord v
  have hc (v : BaseCode) : Commute (m * n.nu * m * n.nu) (f (sWord b v)) := by
    have h : Commute ((m * n.nu * m) * (n.nu⁻¹)⁻¹) (f (sWord b v)) := by
      apply commute_mul_inv_of_conj_eq
      calc
        _ = m * (n.nu⁻¹ * (m * f (sWord b v) * m) * n.nu) * m := by
          simp only [mul_inv_rev, hm]
          group
        _ = f (sWord b (mCode (aCode (mCode v)))) := by rw [hM, hA, hM]
        _ = A (A (f (sWord b v))) := by rw [aCode_mCode, n.conj_sWord, n.conj_sWord]
        _ = _ := by rw [conj_twice_of_cube n.nu n.cube]; simp only [inv_inv]
    simpa only [inv_inv] using h
  rw [← Fusion.ambientElementary_selfCentralizing D e 1]
  apply mem_centralizer_iff.mpr
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨v, rfl⟩ := (Fusion.mem_elementary 1 w).mp hw
  have he : f (Fusion.elementaryWord 1 v) = f (sWord b (reCode b v)) := by
    rw [sWord_reCode, reCode_twice]
  rw [he]
  exact (hc _).eq.symm

private theorem NuActionRelations.defect_cases {b : Bit} [Finite G]
    (n : NuActionRelations D e b) :
    D.a10ModelEmbedding e mup * n.nu * D.a10ModelEmbedding e mup * n.nu = 1 ∨
    D.a10ModelEmbedding e mup * n.nu * D.a10ModelEmbedding e mup * n.nu =
      D.a10ModelEmbedding e (coreTau b) := by
  let f := D.a10ModelEmbedding e
  let m := f mup
  let A := MulAut.conj n.nu⁻¹
  let B := MulAut.conj m
  let c := m * n.nu * m * n.nu
  have hm : m⁻¹ = m := by
    have h : mup⁻¹ = mup := by decide +kernel
    simpa only [m, ← map_inv] using congrArg f h
  have hm2 : m * m = 1 := by calc
    _ = m⁻¹ * m := congrArg (fun x => x * m) hm.symm
    _ = 1 := inv_mul_cancel m
  have hA (v : BaseCode) : A (f (sWord b v)) = f (sWord b (aCode v)) :=
    n.conj_sWord v
  have hBc : B c = A (A c) := by
    rw [conj_twice_of_cube n.nu n.cube]
    simp only [B, MulAut.conj_apply, hm, c]
    calc
      _ = n.nu * m * n.nu * m := by
        calc
          _ = (m * m) * n.nu * m * n.nu * m := by group
          _ = _ := by rw [hm2, one_mul]
      _ = _ := by group
  have hnorm : c * A c * A (A c) = 1 := by
    have hBcube : (m * n.nu * m) ^ 3 = 1 := by
      simpa only [map_pow, B, MulAut.conj_apply, hm, map_one] using congrArg B n.cube
    calc
      _ = (m * n.nu * m) ^ 3 * n.nu ^ 3 := by
        simp only [A, MulAut.conj_apply, inv_inv, c, pow_succ, pow_zero, one_mul]
        group
      _ = 1 := by rw [hBcube, n.cube, one_mul]
  obtain ⟨w, hw, hc⟩ := n.defect_mem
  obtain ⟨v, hv⟩ := (Fusion.mem_elementary 1 w).mp hw
  have hv' : f (sWord b (reCode b v)) = c := by
    rw [sWord_reCode, reCode_twice, hv]
    exact hc
  generalize reCode b v = j at hv'
  have hBword : B (f (sWord b j)) = f (sWord b (mCode j)) := by
    simpa only [B, MulAut.conj_apply, hm, m, ← map_mul] using congrArg f (sWord_mup b j)
  have heB : sWord b (mCode j) = sWord b (aCode (aCode j)) := by
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    rw [← hBword, hv', hBc, ← hv', hA, hA]
  have heN : sWord b j * sWord b (aCode j) * sWord b (aCode (aCode j)) = 1 := by
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    simpa only [map_one, map_mul, ← hA, hv'] using hnorm
  have hfinite : ∀ b j,
      sWord b (mCode j) = sWord b (aCode (aCode j)) →
      sWord b j * sWord b (aCode j) * sWord b (aCode (aCode j)) = 1 →
      sWord b j = 1 ∨ sWord b j = coreTau b := by decide +kernel
  rcases hfinite b j heB heN with h | h
  · left
    change c = 1
    rw [← hv', h, map_one]
  · right
    change c = f (coreTau b)
    rw [← hv', h]
private noncomputable def NuActionRelations.conjugateTau {b : Bit} (n : NuActionRelations D e b) :
    NuActionRelations D e b := by
  let f := D.a10ModelEmbedding e
  let T := MulAut.conj (f tau)
  have hti : (f tau)⁻¹ = f tau := by
    have h : tau⁻¹ = tau := by decide +kernel
    simpa only [← map_inv] using congrArg f h
  have hlocal : ∀ b,
      tau * Coordinates.pi * tau = Coordinates.pi ∧
      tau * Coordinates.mu * tau = Coordinates.mu ∧
      tau * tau * tau = tau ∧
      tau * normalizedLam b * tau = normalizedLam b := by decide +kernel
  have hp : T (f Coordinates.pi) = f Coordinates.pi := by
    simpa only [T, MulAut.conj_apply, hti, ← map_mul] using congrArg f (hlocal b).1
  have hm : T (f Coordinates.mu) = f Coordinates.mu := by
    simpa only [T, MulAut.conj_apply, hti, ← map_mul] using congrArg f (hlocal b).2.1
  have ht : T (f tau) = f tau := by
    simpa only [T, MulAut.conj_apply, hti, ← map_mul] using congrArg f (hlocal b).2.2.1
  have hl : T (f (normalizedLam b)) = f (normalizedLam b) := by
    simpa only [T, MulAut.conj_apply, hti, ← map_mul] using congrArg f (hlocal b).2.2.2
  refine ⟨T n.nu, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, n.cube, map_one]
  · have h := n.mu_commute.map T.toMonoidHom
    change Commute (T n.nu) (T (f Coordinates.mu)) at h
    rwa [hm] at h
  · have h := n.lam_commute.map T.toMonoidHom
    change Commute (T n.nu) (T (f (normalizedLam b))) at h
    rwa [hl] at h
  · have h := congrArg T n.pi_nu
    change T (n.nu⁻¹ * f Coordinates.pi * n.nu) =
      T (f (Coordinates.pi * tau * normalizedLam b)) at h
    simpa only [map_mul, map_inv, hp, ht, hl] using h
  · have h := congrArg T n.tau_nu
    change T (n.nu⁻¹ * f tau * n.nu) =
      T (f (Coordinates.pi * Coordinates.mu * normalizedLam b)) at h
    simpa only [map_mul, map_inv, hp, hm, ht, hl] using h

private theorem NuActionRelations.conjugateTau_inverted {b : Bit}
    (n : NuActionRelations D e b)
    (hc : D.a10ModelEmbedding e mup * n.nu * D.a10ModelEmbedding e mup * n.nu =
      D.a10ModelEmbedding e (coreTau b)) :
    D.a10ModelEmbedding e mup * n.conjugateTau.nu * D.a10ModelEmbedding e mup =
      n.conjugateTau.nu⁻¹ := by
  let f := D.a10ModelEmbedding e
  let m := f mup
  let t := f tau
  have hm2 : m * m = 1 := by
    have h : mup * mup = 1 := by decide +kernel
    simpa only [m, ← map_mul, map_one] using congrArg f h
  have hti : t⁻¹ = t := by
    have h : tau⁻¹ = tau := by decide +kernel
    simpa only [t, ← map_inv] using congrArg f h
  have hmn : m * n.nu * m = f (coreTau b) * n.nu⁻¹ := by
    exact eq_mul_inv_of_mul_eq hc
  have hmt : m * t * m = f (Coordinates.pi * tau) := by
    have h : mup * tau * mup = Coordinates.pi * tau := by decide +kernel
    simpa only [m, t, ← map_mul] using congrArg f h
  have hApt : n.nu⁻¹ * f (Coordinates.pi * tau) * n.nu =
      f (tau * Coordinates.mu) := by
    calc
      _ = (n.nu⁻¹ * f Coordinates.pi * n.nu) * (n.nu⁻¹ * f tau * n.nu) := by
        rw [map_mul]
        group
      _ = f ((Coordinates.pi * tau * normalizedLam b) *
          (Coordinates.pi * Coordinates.mu * normalizedLam b)) := by
        rw [n.pi_nu, n.tau_nu, ← map_mul]
      _ = _ := by
        have h : ∀ b, (Coordinates.pi * tau * normalizedLam b) *
          (Coordinates.pi * Coordinates.mu * normalizedLam b) = tau * Coordinates.mu := by
          decide +kernel
        exact congrArg f (h b)
  have hlocal : ∀ b, (Coordinates.pi * tau) * coreTau b * (tau * Coordinates.mu) =
      tau * (Coordinates.pi * Coordinates.mu * normalizedLam b) := by decide +kernel
  change m * ((MulAut.conj t) n.nu) * m = ((MulAut.conj t) n.nu)⁻¹
  simp only [MulAut.conj_apply, hti]
  calc
    _ = (m * t * m) * (m * n.nu * m) * (m * t * m) := by
      symm
      calc
        _ = m * t * (m * m) * n.nu * (m * m) * t * m := by group
        _ = _ := by rw [hm2]; group
    _ = f (Coordinates.pi * tau) * (f (coreTau b) * n.nu⁻¹) * f (Coordinates.pi * tau) := by
      rw [hmt, hmn]
    _ = (f (Coordinates.pi * tau) * f (coreTau b) *
        (n.nu⁻¹ * f (Coordinates.pi * tau) * n.nu)) * n.nu⁻¹ := by group
    _ = f (tau * (Coordinates.pi * Coordinates.mu * normalizedLam b)) * n.nu⁻¹ := by
      rw [hApt, ← map_mul, ← map_mul, hlocal b]
    _ = t * (n.nu⁻¹ * t * n.nu) * n.nu⁻¹ := by rw [map_mul, ← n.tau_nu]
    _ = (t * n.nu * t)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hti]; group

/-- An ambient three-element with the marked S-action can be conjugated by
one or tau so that mu-prime inverts it. No further normalizer geometry,
ambient fusion or simplicity premise is required for this lifting step. -/
public theorem NuActionRelations.nonempty_seed {b : Bit} [Finite G]
    (n : NuActionRelations D e b) : Nonempty (NuSeedRelations D e b) := by
  have finish (n' : NuActionRelations D e b)
      (hi : D.a10ModelEmbedding e mup * n'.nu * D.a10ModelEmbedding e mup = n'.nu⁻¹) :
      Nonempty (NuSeedRelations D e b) :=
    ⟨⟨n'.nu, n'.cube, n'.mu_commute, n'.lam_commute, n'.pi_nu, n'.tau_nu, hi⟩⟩
  rcases n.defect_cases with h | h
  · exact finish n (mul_eq_one_iff_eq_inv.mp h)
  · exact finish n.conjugateTau (n.conjugateTau_inverted h)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
