module

public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransportAlgebra
public import Stellmacher.Recognition.Parrott.ElementaryJoin

/-!
# The upper bound for Parrott's involution orbit

The involutions in wF belong to E, since the square-one elements of E∨F
are in E or F and w is outside F. Fusion puts the ones conjugate to y
in the H-class of t. The core of N centralizes t and has order 1024,
so this H-class has at most ten elements. It already contains t and zt
in F; consequently its intersection with wF has at most eight elements.

The image set below retains the actual second Sylow candidate
T₂ = ⟨s₀,K⟩. Its lower bound is a separate census of involution
transporters, rather than a consequence of ambient conjugacy.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.681, “Generators and relations for N”.
-/

open Subgroup MulAction
open scoped IsMulCommutative

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Images in wF obtained by involutions outside K in the actual ⟨s₀,K⟩.
The coset condition is retained in the image set so that a lower census
alone suffices for saturation. -/
@[expose] public def ParrottCentralizerGeneratorData.secondSylowInvolutionImages
    (f : ParrottCentralizerGeneratorData n) (s₀ : G) : Set G :=
  {g | f.w⁻¹ * g ∈ e.F ∧ ∃ s : G,
    s ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype ⊔ zpowers s₀ ∧
    s ∉ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype ∧
    s ^ 2 = 1 ∧ s⁻¹ * f.y * s = g}

private theorem local_class_card [Finite G] (H : Subgroup G) (x : G) :
    (Set.range (fun a : H => (a : G) * x * (a : G)⁻¹)).ncard *
      Nat.card (H ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card H := by
  let act : MulDistribMulAction H G := MulDistribMulAction.compHom G
    ((MulAut.conj : G →* MulAut G).comp H.subtype)
  let : MulAction H G := act.toMulAction
  have heq : (stabilizer H x).map H.subtype = H ⊓ centralizer ({x} : Set G) := by
    ext a
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp ha)⟩
    · rintro ⟨haH, ha⟩
      exact ⟨⟨a, haH⟩, mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp ha), rfl⟩
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod, ← card_map_of_injective (K := stabilizer H x)
    H.subtype_injective, heq] at hc
  exact hc

/-- There are at most eight elements of wF in the ambient class of y.
This upper bound uses the actual derived fusion and the order of the core. -/
public theorem ParrottCentralizerGeneratorData.w_coset_y_class_ncard_le_eight
    [Finite G] (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) :
    {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g}.ncard ≤ 8 := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let N := normalizer (e.F : Set G)
  let K := pCore 2 N
  let X := K.map N.subtype
  let O : Set G := Set.range (fun a : H => (a : G) * n.t * (a : G)⁻¹)
  have hC : 1024 ≤ Nat.card (H ⊓ centralizer ({n.t} : Set G) : Subgroup G) := by
    have hXC : X ≤ H ⊓ centralizer ({n.t} : Set G) := by
      change (pCore 2 (normalizer (e.F : Set G))).map
        (normalizer (e.F : Set G)).subtype ≤ _
      rw [n.core_eq_sylow_centralizer]
      exact inf_le_inf_right _ e.sylow_le_centralizer
    have hc := card_le_of_le hXC
    rwa [card_map_of_injective N.subtype_injective, n.core_card] at hc
  have hO : O.ncard ≤ 10 := by
    have hc := (local_class_card H n.t).trans (h.card_and_solvable z).1
    change O.ncard * _ = 10240 at hc
    nlinarith
  have htO : n.t ∈ O := ⟨1, by simp⟩
  have hztO : z * n.t ∈ O := by
    obtain ⟨a, _, ha⟩ := parrott_derived_central_twist_conjugator z h n.t
      n.t_mem_inf.1 n.t_not_mem_zpowers
    exact ⟨a, ha⟩
  have hpair : ({n.t, z * n.t} : Set G) ⊆ O ∩ (e.F : Set G) := by
    intro g hg
    rcases (show g = n.t ∨ g = z * n.t by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg) with rfl | rfl
    · exact ⟨htO, n.t_mem_inf.2⟩
    · exact ⟨hztO, e.F.mul_mem e.z_mem_inf.2 n.t_mem_inf.2⟩
  have htne : n.t ≠ z * n.t := by
    intro heq
    have hz1 : z = 1 := mul_right_cancel (heq.symm.trans (one_mul n.t).symm)
    have hh := h.involution
    simp [hz1] at hh
  have hinter : 2 ≤ (O ∩ (e.F : Set G)).ncard := by
    have hh := Set.ncard_le_ncard hpair
    rwa [Set.ncard_pair htne] at hh
  have hsmall : (O \ (e.F : Set G)).ncard ≤ 8 := by
    have hh := Set.ncard_inter_add_ncard_sdiff_eq_ncard O (e.F : Set G)
    omega
  have haF : f.a ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have hwE : f.w ∈ E := by
    change f.w ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  have hwF : f.w ∉ e.F := by
    intro hw
    let _ := e.elementary
    have hcomm : Commute f.a f.w :=
      congrArg e.F.subtype (mul_comm (⟨f.a, haF⟩ : e.F) ⟨f.w, hw⟩)
    have hz1 : z = 1 := f.eq02_aw.symm.trans
      ((Tits.parrottCommutator_eq_one_iff _ _).mpr hcomm)
    have hh := h.involution
    simp [hz1] at hh
  have hsub : {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} ⊆ O \ (e.F : Set G) := by
    rintro g ⟨hgF, hconj⟩
    have hgnotF : g ∉ e.F := by
      intro hg
      have hwInv : f.w⁻¹ ∈ e.F := by
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using e.F.mul_mem hgF (e.F.inv_mem hg)
      exact hwF ((e.F.inv_mem_iff).mp hwInv)
    have hgA : g ∈ E ⊔ e.F := by
      have hh := (E ⊔ e.F).mul_mem (mem_sup_left hwE) (mem_sup_right hgF)
      simpa only [mul_inv_cancel_left] using hh
    have hg2 : g ^ 2 = 1 := by
      obtain ⟨q, rfl⟩ := isConj_iff.mp hconj
      rw [conj_pow, f.y_sq]
      simp
    have hgE : g ∈ E := (e.elementary_join_involution h g hgA hg2).resolve_right hgnotF
    have hgz : g ∉ zpowers z := fun hh => hgnotF ((zpowers_le.mpr e.z_mem_inf.2) hh)
    refine ⟨?_, hgnotF⟩
    rcases n.derived_fusion g hgE hgz with ht | hv
    · exact ht
    · obtain ⟨a, ha⟩ := hv
      have hvg : IsConj n.v g := isConj_iff.mpr ⟨(a : G), ha⟩
      exact (n.not_isConj ((f.y_isConj_z.symm.trans hconj).trans hvg.symm)).elim
  exact (Set.ncard_le_ncard hsub).trans hsmall

end Stellmacher.Recognition
