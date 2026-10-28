module
public import CFSG.Quasithin.Chapter10.SourceNonnormalFixedResidual
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
public import Theory.GroupTheory.SylowNormalizerOrbit

/-!
# Odd-prime actor normalizers retain the original component orbit

An odd-prime subgroup B in C_M(L₀/O₂(L₀)) that permutes with T has
L^{N_T(B)} = L^T. The section centralizer is normal in M and normalizes
L by C-component lifting. Inside BT, the prime subgroup B is Sylow;
the Frattini argument gives a supplement whose omitted factor fixes L.
The same proof works for a subgroup T₊ ≤ T retaining the original orbit.

This proves the precise prime-primary consequence of Aschbacher–Smith,
4.4.4–6, combined manuscript of 1 March 2004, printed pp.619–620,
needed for the literal Chapter 10 Cartan kernel. It does not require
commutativity of B or the full abelian-Hall factorization of 4.4.4.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

include D in
/-- The prime actor normalizer inside an orbit-retaining subgroup retains
that same original component orbit. -/
theorem source_oddPrimeActor_normalizer_orbit_of_subgroup
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B S : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hST : S ≤ (T : Subgroup G))
    (hperm : (B : Set G)*(S : Set G) = (S : Set G)*(B : Set G))
    (horbit : componentOrbit L S = localOrbit T L) :
    componentOrbit L (S ⊓ normalizer (B : Set G)) = localOrbit T L := by
  let X := localOrbit T L
  let M := D.maximalLocal
  let C := sectionCentralizer X
  have hCM : C ≤ M := ((le_sectionCentralizer_iff C X).mp le_rfl).1
  have hMC : M ≤ normalizer (C : Set G) := by
    have hh := sectionCentralizerIn_normalized (M := M) (X := X) le_rfl
    rwa [sectionCentralizerIn, inf_eq_right.mpr hCM] at hh
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hCL : C ≤ normalizer (L : Set G) :=
    ((le_sectionCentralizer_iff C L).mp
      (source_orbit_sectionCentralizer_le_component D)).1
  have hnot : ¬ p ∣ Nat.card S := by
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le hST).exists_card_eq
    rw [hn]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hp.coprime_two_right.pow_right n)
  have he := conjugateSpanBy_inf_normalizer_eq_of_permutable L B S C hB hnot
    hperm.symm hBC ((hST.trans hTM).trans hMC) hCL
  rw [conjugateSpanBy_eq_iSup_conj,conjugateSpanBy_eq_iSup_conj] at he
  exact he.trans horbit

include D in
/-- The literal N_T(B) retains the full original component orbit. -/
theorem source_oddPrimeActor_normalizer_orbit
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G)*(T : Set G) = (T : Set G)*(B : Set G)) :
    componentOrbit L ((T : Subgroup G) ⊓ normalizer (B : Set G)) = localOrbit T L :=
  source_oddPrimeActor_normalizer_orbit_of_subgroup D hp B T hB hBC le_rfl hperm rfl
end CFSG.Quasithin.Chapter10
