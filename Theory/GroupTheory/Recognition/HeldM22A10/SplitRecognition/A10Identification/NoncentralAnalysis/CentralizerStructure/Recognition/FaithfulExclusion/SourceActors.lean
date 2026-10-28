module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.Actors
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Lift
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations

/-!
# Passing Held's earlier actors to the canonical core

Assuming the ambient actors constructed in Sections 2.13 and 4.1, this module
proves all the core memberships and the eight-word centralizer description
required by `Actors`. It does not yet assert the existence of the earlier actors.

The quotient C/A has order eight, so elements of exponent three in C lie in A.
The action of nu then puts tau*lambda and pi*mu in A; the action of
beta = tau'*alpha*tau' puts mu'*xi in A. Normality is only used inside C.
The injective derived map embeds C_A(pi*mu) in C_M(p), of order eight.
The eight distinct local words therefore exhaust the centralizer.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13 and 4.1--4.2, pp.231--235.
The remaining existence constructions belong to the `SourceActors` descendants;
the unconditional `Nonempty (Actors c)` assembly remains an open obligation.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion

universe u
variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}
  (c : QuotientCore D e)

public theorem ambientCore_le : ambientCore c ≤ C D e := map_subtype_le _

public theorem mem_ambientCore_iff (x : C D e) :
    (x : G) ∈ ambientCore c ↔ x ∈ c.derivedLift := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy
  · exact mem_map_of_mem (C D e).subtype

/-- Odd-order actors of exponent three lie in A because [C:A] = 8. -/
public theorem cube_mem_ambientCore [Finite G] (hbij : Function.Bijective c.derivedMap)
    {x : G} (hx : x ∈ C D e) (h3 : x ^ 3 = 1) : x ∈ ambientCore c := by
  let y : C D e := ⟨x, hx⟩
  let z := QuotientGroup.mk' c.derivedLift y
  have hz3 : z ^ 3 = 1 := by
    change QuotientGroup.mk' c.derivedLift y ^ 3 = 1
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext h3, map_one]
  have hz8 : orderOf z ∣ 8 := by
    simpa only [show Nat.card (C D e ⧸ c.derivedLift) = 8 from c.derivedLift_index hbij]
      using orderOf_dvd_natCard z
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by
    simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz3) hz8))
  exact (mem_ambientCore_iff c y).mpr ((QuotientGroup.eq_one_iff y).mp hz1)

public theorem ambientCore_conj_mem {x g : G} (hx : x ∈ ambientCore c)
    (hg : g ∈ C D e) : g⁻¹ * x * g ∈ ambientCore c := by
  let x' : C D e := ⟨x, ambientCore_le c hx⟩
  let g' : C D e := ⟨g, hg⟩
  have hh := c.derivedLift_normal.conj_mem x' ((mem_ambientCore_iff c x').mp hx) g'⁻¹
  have := (mem_ambientCore_iff c (g'⁻¹ * x' * g')).mpr (by simpa only [inv_inv] using hh)
  exact this

public theorem factor_mem_ambientCore {x g t : G} (hx : x ∈ C D e)
    (hg : g ∈ ambientCore c) (heq : g⁻¹ * x * g = x * t) :
    t ∈ ambientCore c := by
  have h := (ambientCore c).mul_mem
    (ambientCore_conj_mem c ((ambientCore c).inv_mem hg) hx) hg
  have ht : x⁻¹ * g⁻¹ * x * g = t := by
    calc
      _ = x⁻¹ * (g⁻¹ * x * g) := by group
      _ = t := by rw [heq, inv_mul_cancel_left]
  rwa [ht] at h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem local_word_injective : ∀ b d, Function.Injective (coreWord b d) := by
  intro b d a a'
  rcases a with ⟨i,j,k⟩
  rcases a' with ⟨l,m,n⟩
  fin_cases b <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;> fin_cases m <;> fin_cases n <;> decide +kernel

private theorem local_word_commute : ∀ b d i,
    coreWord b d i * corePi = corePi * coreWord b d i := by
  intro b d ⟨i,j,k⟩
  fin_cases b <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> decide +kernel

/-- The intrinsic centralizer bound makes the eight local words exhaustive. -/
public theorem centralizer_words_of_mem [Finite G] (hbij : Function.Bijective c.derivedMap)
    (b d : Bit)
    (hpi : D.a10ModelEmbedding e corePi ∈ ambientCore c)
    (htau : D.a10ModelEmbedding e (coreTau b) ∈ ambientCore c)
    (hswap : D.a10ModelEmbedding e (coreSwap d) ∈ ambientCore c) :
    ∀ y ∈ ambientCore c, Commute y (D.a10ModelEmbedding e corePi) →
      ∃ i : WordCode, y = D.a10ModelEmbedding e (coreWord b d i) := by
  let f := D.a10ModelEmbedding e
  let K : Subgroup G := ambientCore c ⊓ centralizer ({f corePi} : Set G)
  let x : C D e := ⟨f corePi, ambientCore_le c hpi⟩
  have hqx : q D e x = p D e := by
    have hx : x = pi D e * mu D e := by
      apply Subtype.ext
      simp only [x, f, corePi, map_mul, Coordinates.pi,
        D.a10ModelEmbedding_central e, Coordinates.mu, pi, mu,
        LocalData.a10NoncentralInvolution, coe_mul]
    rw [hx, map_mul]
    have hm : q D e (mu D e) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)
    rw [hm, mul_one]
    rfl
  let toCore (y : K) : c.derivedLift :=
    ⟨⟨y.1, ambientCore_le c y.property.1⟩,
      (mem_ambientCore_iff c _).mp y.property.1⟩
  let z : c.subgroup := ⟨p D e, c.p_mem⟩
  let F (y : K) : centralizer ({z} : Set c.subgroup) :=
    ⟨c.derivedMap (toCore y), mem_centralizer_singleton_iff.mpr (by
      apply Subtype.ext
      change q D e (toCore y).1 * p D e = p D e * q D e (toCore y).1
      rw [← hqx, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property.2))⟩
  have hF : Function.Injective F := by
    intro y y' h
    have hh := hbij.1 (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun a : c.derivedLift => (a.1 : G)) hh)
  have hcardK : Nat.card K ≤ 8 := by
    have hc : Nat.card (centralizer ({z} : Set c.subgroup)) = 8 := by
      rw [show centralizer ({z} : Set c.subgroup) = (c.sylow : Subgroup c.subgroup)
        from c.centralizer_eq]
      exact (Nat.card_congr c.sylowEquiv.toEquiv).trans (by
        rw [DihedralGroup.nat_card])
    exact (Nat.card_le_card_of_injective F hF).trans_eq hc
  let W (i : WordCode) : K := ⟨f (coreWord b d i), by
    constructor
    · simp only [coreWord, map_mul, map_pow]
      exact (ambientCore c).mul_mem
        ((ambientCore c).mul_mem ((ambientCore c).pow_mem hpi _)
          ((ambientCore c).pow_mem htau _)) ((ambientCore c).pow_mem hswap _)
    · exact mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg f (local_word_commute b d i))⟩
  have hW : Function.Injective W := by
    intro i j h
    have hw : f (coreWord b d i) = f (coreWord b d j) :=
      congrArg (fun x : K => (x : G)) h
    exact local_word_injective b d (D.a10ModelEmbedding_injective e hw)
  have hsurj := (hW.bijective_of_nat_card_le (by
    simpa [WordCode, Bit] using hcardK)).2
  intro y hy hcomm
  obtain ⟨i, hi⟩ := hsurj ⟨y, hy, mem_centralizer_singleton_iff.mpr hcomm.eq⟩
  exact ⟨i, (congrArg Subtype.val hi).symm⟩


/-- Complete core geometry from the two earlier, separately constructed actors. -/
public noncomputable def actorsOfRelations [Finite G] (hbij : Function.Bijective c.derivedMap)
    {b d : Bit} (a : AlphaRelations D e d) (n : NuRelations D e b d) : Actors c := by
  let f := D.a10ModelEmbedding e
  let t := f Coordinates.taup
  let beta := t * a.alpha * t
  have ht : t * t = 1 := by
    rw [← map_mul]
    have hh : Coordinates.taup * Coordinates.taup = 1 := by decide +kernel
    rw [hh, map_one]
  have hti : t⁻¹ = t := (eq_inv_iff_mul_eq_one.mpr ht).symm
  have htm : t * f Coordinates.mu * t = f corePi := by
    have hl : Coordinates.taup * Coordinates.mu * Coordinates.taup = corePi := by
      decide +kernel
    simpa only [t, map_mul] using congrArg f hl
  have htp : t * f corePi * t = f Coordinates.mu := by
    have hl : Coordinates.taup * corePi * Coordinates.taup = Coordinates.mu := by
      decide +kernel
    simpa only [t, map_mul] using congrArg f hl
  have hb3 : beta ^ 3 = 1 := by
    change (t * a.alpha * t) ^ 3 = 1
    calc
      _ = (t * a.alpha * t⁻¹) ^ 3 := by rw [hti]
      _ = 1 := by rw [conj_pow, a.cube, mul_one, mul_inv_cancel]
  have hbmu : beta ∈ C D e := by
    apply mem_centralizer_singleton_iff.mpr
    change beta * f Coordinates.mu = f Coordinates.mu * beta
    have hcomm := a.corePi_commute.eq
    rw [← htm] at hcomm
    have hh := congrArg (fun z => t * z * t) hcomm
    have htt (z : G) : t * (t * z) = z := by rw [← mul_assoc, ht, one_mul]
    simpa only [beta, mul_assoc, ht, mul_one, one_mul, htt] using hh
  have hbmem := cube_mem_ambientCore c hbij hbmu hb3
  have hnmu : n.nu ∈ C D e := mem_centralizer_singleton_iff.mpr n.mu_commute.eq
  have hnmem := cube_mem_ambientCore c hbij hnmu n.cube
  have hpc : f corePi ∈ C D e := by
    apply mem_centralizer_singleton_iff.mpr
    change f corePi * f Coordinates.mu = f Coordinates.mu * f corePi
    have hl : corePi * Coordinates.mu = Coordinates.mu * corePi := by decide +kernel
    simpa only [map_mul] using congrArg f hl
  have htaumem : f (coreTau b) ∈ ambientCore c :=
    factor_mem_ambientCore c hpc hnmem (by simpa only [map_mul] using n.pi_nu)
  have hpimem : f corePi ∈ ambientCore c := by
    rw [← n.tau_nu]
    exact (ambientCore c).mul_mem
      ((ambientCore c).mul_mem ((ambientCore c).inv_mem hnmem) htaumem) hnmem
  have hpb : beta⁻¹ * f corePi * beta = f (corePi * coreSwap d) := by
    calc
      _ = t * (a.alpha⁻¹ * (t * f corePi * t) * a.alpha) * t := by
        dsimp [beta]
        simp only [mul_inv_rev, hti]
        group
      _ = t * (a.alpha⁻¹ * f Coordinates.mu * a.alpha) * t := by rw [htp]
      _ = t * f (Coordinates.mu * normalizedXi d) * t := by rw [a.mu_alpha]
      _ = f (corePi * coreSwap d) := by
        have hl : ∀ d, Coordinates.taup * (Coordinates.mu * normalizedXi d) *
          Coordinates.taup = corePi * coreSwap d := by decide +kernel
        simpa only [t, map_mul] using congrArg f (hl d)
  have hswapmem : f (coreSwap d) ∈ ambientCore c :=
    factor_mem_ambientCore c hpc hbmem (by simpa only [map_mul] using hpb)
  exact
    { lamChoice := b
      xiChoice := d
      nu := n.nu
      alpha := a.alpha
      pi_mem := hpimem
      tau_mem := htaumem
      swap_mem := hswapmem
      nu_mem := hnmem
      beta_mem := hbmem
      centralizer_words := centralizer_words_of_mem c hbij b d hpimem htaumem hswapmem
      nu_xi := n.xi_commute
      pi_nu := n.pi_nu
      xi_alpha := a.xi_alpha
      pi_alpha := a.pi_alpha }

end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
