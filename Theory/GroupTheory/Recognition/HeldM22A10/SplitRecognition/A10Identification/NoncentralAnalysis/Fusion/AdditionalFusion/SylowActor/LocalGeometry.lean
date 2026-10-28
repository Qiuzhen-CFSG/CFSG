module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry

/-!
# The common Sylow intersection and its center

The local centralizer of mu has order 64 and lies in the displayed Sylow
subgroup. Its ambient image is the actual intersection of the centralizers
of pi and mu. Its center consists of 1, pi, mu and pi*mu, and the ambient
centralizer of this four-group is exactly the original intersection.

The center calculation tests six explicit centralizing generators against
the 384 coordinate normal forms. Normalizing the intersection preserves
its center. These are the local inputs to the Sylow construction in
D. Held, Illinois J. Math. 13 (1969), 224--240, Lemma 2.6, p.228,
DOI 10.1215/ijm/1256053756.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
local instance : DecidableEq H := inferInstance

private def commonGenerator : Fin 6 → H := ![pi, mu, mup, tau, lam, xi]

private theorem commonGenerator_mem (i : Fin 6) :
    commonGenerator i ∈ centralizer ({mu} : Set H) := by
  apply mem_centralizer_singleton_iff.mpr
  have h : ∀ i, commonGenerator i * mu = mu * commonGenerator i := by decide +kernel
  exact h i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem common_center_test : ∀ a : Code,
    (∀ i, commonGenerator i * word a = word a * commonGenerator i) →
      word a = 1 ∨ word a = pi ∨ word a = mu ∨ word a = pi * mu := by
  decide +kernel

private theorem common_center (x : H)
    (hx : x ∈ centralizer ((centralizer ({mu} : Set H)) : Set H)) :
    x = 1 ∨ x = pi ∨ x = mu ∨ x = pi * mu := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  exact common_center_test a (fun i => mem_centralizer_iff.mp hx _ (commonGenerator_mem i))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem common_le_modelD : centralizer ({mu} : Set H) ≤ modelD := by
  intro x hx
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  rw [word_mem_modelD]
  have h : ∀ a : Code, word a * mu = mu * word a → a.2.2.2.1 = 0 := by
    decide +kernel
  exact h a (mem_centralizer_singleton_iff.mp hx)

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

@[expose] public def muIntersection : Subgroup G :=
  D.centralizer ⊓ centralizer ({D.a10NoncentralInvolution e} : Set G)

@[expose] public def muPlane : Subgroup G :=
  muIntersection D e ⊓ centralizer (muIntersection D e : Set G)

public theorem muIntersection_le_sylow : muIntersection D e ≤ ambientSylow D e := by
  rw [muIntersection, ← ambient_centralizer_mu_map]
  exact map_mono common_le_modelD

omit [Finite G] in
public theorem muIntersection_card : Nat.card (muIntersection D e) = 64 :=
  ambient_intersection_card D e

public theorem muPlane_mem (x : G) : x ∈ muPlane D e ↔
    x = 1 ∨ x = D.z ∨ x = D.a10NoncentralInvolution e ∨
      x = D.z * D.a10NoncentralInvolution e := by
  let f := D.a10ModelEmbedding e
  have hp : f pi = D.z := D.a10ModelEmbedding_central e
  have hm : f mu = D.a10NoncentralInvolution e := rfl
  have hzQ : D.z ∈ muIntersection D e := by
    rw [muIntersection, ← ambient_centralizer_mu_map, ← hp]
    apply mem_map_of_mem
    exact mem_centralizer_singleton_iff.mpr (by decide +kernel)
  have hmQ : D.a10NoncentralInvolution e ∈ muIntersection D e := by
    rw [muIntersection, ← ambient_centralizer_mu_map, ← hm]
    exact mem_map_of_mem _ (mem_centralizer_singleton_iff.mpr rfl)
  have hzV : D.z ∈ muPlane D e := by
    refine ⟨hzQ, ?_⟩
    intro y hy
    exact mem_centralizer_singleton_iff.mp hy.1
  have hmV : D.a10NoncentralInvolution e ∈ muPlane D e := by
    refine ⟨hmQ, ?_⟩
    intro y hy
    exact mem_centralizer_singleton_iff.mp hy.2
  constructor
  · rintro ⟨hxQ, hxC⟩
    have hxrange : x ∈ f.range := by
      rw [D.a10ModelEmbedding_range e]
      exact hxQ.1
    obtain ⟨y, rfl⟩ := hxrange
    have hy : y ∈ centralizer ((centralizer ({mu} : Set H)) : Set H) := by
      intro t ht
      apply D.a10ModelEmbedding_injective e
      have htQ : f t ∈ muIntersection D e := by
        rw [muIntersection, ← ambient_centralizer_mu_map]
        exact mem_map_of_mem _ ht
      simpa only [map_mul] using mem_centralizer_iff.mp hxC _ htQ
    rcases common_center y hy with rfl | rfl | rfl | rfl
    · exact Or.inl f.map_one
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hm))
    · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, hp, hm])))
  · rintro (rfl | rfl | rfl | rfl)
    · exact (muPlane D e).one_mem
    · exact hzV
    · exact hmV
    · exact (muPlane D e).mul_mem hzV hmV

private def fourRep : Fin 4 → H := ![1, pi, mu, pi * mu]

public theorem muPlane_card : Nat.card (muPlane D e) = 4 := by
  let w (i : Fin 4) : muPlane D e := ⟨D.a10ModelEmbedding e (fourRep i), by
    rw [muPlane_mem]
    fin_cases i
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl (D.a10ModelEmbedding_central e))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by
        change D.a10ModelEmbedding e (pi * mu) = _
        rw [map_mul, D.a10ModelEmbedding_central e]; rfl)))⟩
  have hi : Function.Injective fourRep := by decide +kernel
  have hw : Function.Bijective w := by
    constructor
    · intro a b hab
      exact hi (D.a10ModelEmbedding_injective e (congrArg (fun x : muPlane D e => (x : G)) hab))
    · intro x
      rcases (muPlane_mem D e x).mp x.property with h | h | h | h
      · exact ⟨0, Subtype.ext (by simpa [w, fourRep] using h.symm)⟩
      · exact ⟨1, Subtype.ext (by simpa [w, fourRep, D.a10ModelEmbedding_central e] using h.symm)⟩
      · exact ⟨2, Subtype.ext h.symm⟩
      · refine ⟨3, Subtype.ext ?_⟩
        change D.a10ModelEmbedding e (pi * mu) = (x : G)
        rw [map_mul, D.a10ModelEmbedding_central e]
        exact h.symm
  rw [← Nat.card_congr (Equiv.ofBijective w hw), Nat.card_fin]

public theorem muPlane_centralizer : centralizer (muPlane D e : Set G) = muIntersection D e := by
  apply le_antisymm
  · intro x hx
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · exact (mem_centralizer_iff.mp hx _ ((muPlane_mem D e _).mpr (Or.inr (Or.inl rfl)))).symm
    · exact (mem_centralizer_iff.mp hx _ ((muPlane_mem D e _).mpr (Or.inr (Or.inr (Or.inl rfl))))).symm
  · intro x hx y hy
    exact (mem_centralizer_iff.mp hy.2 x hx).symm

private theorem normalizes_center_intersection {A : Type*} [Group A] (Q : Subgroup A) :
    normalizer (Q : Set A) ≤ normalizer ((Q ⊓ centralizer (Q : Set A) : Subgroup A) : Set A) := by
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  have step (g : A) (hg : g ∈ normalizer (Q : Set A)) (x : A)
      (hx : x ∈ Q ⊓ centralizer (Q : Set A)) :
      g * x * g⁻¹ ∈ Q ⊓ centralizer (Q : Set A) := by
    refine ⟨(mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    intro y hy
    have hy' := (mem_normalizer_iff.mp ((normalizer (Q : Set A)).inv_mem hg) y).mp hy
    have hc := mem_centralizer_iff.mp hx.2 _ hy'
    have hh := congrArg (fun a : A => g * a * g⁻¹) hc
    simpa only [inv_inv] using (show y * (g * x * g⁻¹) = (g * x * g⁻¹) * y from by
      calc
        _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by simpa only [inv_inv] using hh
        _ = _ := by group)
  constructor
  · exact step g hg x
  · intro hx
    have hh := step g⁻¹ ((normalizer (Q : Set A)).inv_mem hg) _ hx
    simpa [mul_assoc] using hh


omit [Finite G] in
public theorem muPlane_normalizer :
    normalizer (muIntersection D e : Set G) ≤ normalizer (muPlane D e : Set G) :=
  normalizes_center_intersection _

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
