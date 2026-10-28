module

public import Theory.Representation.SL2.EightRootPlacement
public import Theory.GroupAction.CoprimeInvariantSubgroupConjugacy

/-!
# Root placement while retaining a coprime normalizer

The prescribed root and the corresponding root in the specified section are
both invariant under the given coprime prime actor. A fixed transporter
therefore chooses the regular-kernel conjugator in its centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Representation.SL2.BinarySmall

/-- Place the actual root in a kernel-conjugate of the specified section
using a conjugator centralizing its prescribed coprime normalizer. -/
theorem root_le_centralizing_conjugate_section_of_eight_irreducible_kernel
    {E V : Type*} [Group E] [Finite E] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (q : E →* SL(2,GaloisField 2 3))
    (ρ : Representation (ZMod 2) SL(2,GaloisField 2 3) V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V=8) (ek : q.ker ≃* Multiplicative V)
    (hρ : ∀ (g : E) (v : q.ker),
      (ek (MulAut.conjNormal g v)).toAdd=ρ (q g) (ek v).toAdd)
    (s : SL(2,GaloisField 2 3) →* E) (hs : ∀ g,q (s g)=g)
    (R : Subgroup E) (hR : IsPGroup 2 R) (hc : Nat.card R=8)
    (hk : Disjoint R q.ker) (C : Subgroup E) (hCs : C≤s.range)
    (hCR : C≤normalizer (R:Set E))
    {p : ℕ} [Fact p.Prime] (hC : IsPGroup p C) (hp : ¬p∣Nat.card q.ker) :
    ∃ v∈q.ker⊓centralizer (C:Set E),
      R≤s.range.map (MulAut.conj v).toMonoidHom := by
  let U := R.map q
  let A := U.map s
  have hAs : A≤s.range := U.map_le_range s
  have hsq (c : E) (hc : c∈s.range) : s (q c)=c := by
    obtain ⟨g,rfl⟩ := hc
    rw [hs]
  have hCA : C≤normalizer (A:Set E) := by
    intro c hc
    rw [←hsq c (hCs hc)]
    apply U.le_normalizer_map s
    apply mem_map_of_mem s
    exact R.le_normalizer_map q (mem_map_of_mem q (hCR hc))
  obtain ⟨v,hv⟩ := root_le_conjugate_section_of_eight_irreducible_kernel
    q ρ hd ek hρ s hs R hR hc hk
  have hAv : A.map (MulAut.conj (v:E)).toMonoidHom=R := by
    apply le_antisymm
    · rintro x ⟨a,⟨u,hu,rfl⟩,rfl⟩
      obtain ⟨r,hr,he⟩ := hu
      obtain ⟨y,⟨g,rfl⟩,hy⟩ := hv hr
      have hqv : q (v:E)=1 := v.property
      have hg : g=q r := by
        have hh := congrArg q hy
        change q ((v:E)*s g*(v:E)⁻¹)=q r at hh
        simpa only [map_mul,map_inv,hqv,one_mul,mul_one,inv_one,hs] using hh
      change (v:E)*s u*(v:E)⁻¹∈R
      rw [←he,←hg]
      change (v:E)*s g*(v:E)⁻¹=r at hy
      rwa [hy]
    · intro r hr
      obtain ⟨y,⟨g,rfl⟩,hy⟩ := hv hr
      have hqv : q (v:E)=1 := v.property
      have hg : g=q r := by
        have hh := congrArg q hy
        change q ((v:E)*s g*(v:E)⁻¹)=q r at hh
        simpa only [map_mul,map_inv,hqv,one_mul,mul_one,inv_one,hs] using hh
      exact ⟨s g,⟨g,hg.symm ▸ mem_map_of_mem q hr,rfl⟩,hy⟩
  obtain ⟨w,hw,hew⟩ := Theory.GroupAction.exists_centralizing_conjugator_of_invariant_subgroups
    q.ker C A R le_normalizer_of_normal hCA hCR hC hp ⟨v,v.property,hAv⟩
  refine ⟨w,hw,?_⟩
  rw [←hew]
  exact map_mono hAs

end Representation.SL2.BinarySmall
