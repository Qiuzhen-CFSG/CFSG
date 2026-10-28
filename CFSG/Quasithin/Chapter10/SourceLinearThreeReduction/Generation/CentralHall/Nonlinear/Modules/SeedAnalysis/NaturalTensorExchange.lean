module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorCartan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.CartanExchange

/-!
# A common Cartan exchanger in the original tensor alternative

Choose the tensor's factor exchanger in N_T(C) for the same common Cartan
containing the original cyclic Hall subgroup B. Hall uniqueness also puts
this exchanger in N_T(B). The index-two component orbit identifies its
conjugate of L with the previous one, so the actual tensor and determinant
markings can be reconstructed using this same chosen exchanger.

The remaining 9.2.7 comparison must determine the action on B both in the
tensor Cartan and in the original H model, then exclude n > 2. Neither the
action formula nor that exclusion is assumed here.
Source: Aschbacher--Smith 9.2.7 and 10.2.3, pp.731--732,745,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 HallGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
include D c

/-- The literal Hall alternative retains one exchanger in both Cartan and
Hall normalizers, and uses it in the original component quotient markings. -/
theorem original_hall_conclusion_or_natural_tensor_exchanger :
    (IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          D.moduleSubgroup = D.seed ∧
          H ⊓ D.maximalLocal ≤ normalizer (D.seed : Set G) ∧
          B.map H.subtype ≤ localOrbit T L ∧ IsCyclic B ∧
          Nat.card B = 2^n-1 ∧ Monoid.exponent B = 2^n-1 ∧
          n-1 ≤ ChapterE.generationParameter H ∧ ChapterE.generationParameter H ≤ n ∧
          ∃ C : Subgroup G, B.map H.subtype ≤ C ∧ C ≤ sourceOrbitBorel T L ∧
            IsHallSubgroup OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
            Nonempty (C ≃* ((GaloisField 2 n)ˣ × (GaloisField 2 n)ˣ)) ∧
            t ∈ normalizer (C : Set G) ∧ t ∈ normalizer (B.map H.subtype : Set G) := by
  rcases original_hall_conclusion_or_natural_tensor_cartan D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,_ha,_hdet,heq,hseed,hBR,hcyc,hcard,hexp,hlo,hhi,C,hBC,hC,hHall,⟨f⟩⟩
  · exact Or.inl hh
  · let : IsMulCommutative C := ⟨⟨fun x y => f.injective (by simp [mul_comm])⟩⟩
    obtain ⟨s,hs,hsn,hsC⟩ := original_cartan_exchanger D e c.nonnormal C hC hHall
    have hst : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
      (source_nonnormal_maximal_pair D c.nonnormal ht htn s
        (le_normalizer_componentOrbit L T hs)).resolve_left
          (fun h => hsn (mem_normalizer_iff_map_conj_eq.mpr h))
    have hsepS : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj s).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) := by rwa [hst]
    refine Or.inr ⟨s,hs,hsn,n,hn,e,hsepS,
      original_even_seed_natural_tensor D c n hn e hs hsn hsepS,
      original_even_seed_ambient_semilinear D c n hn e hs hsn hsepS,
      heq,hseed,hBR,hcyc,hcard,hexp,hlo,hhi,C,hBC,hC,hHall,⟨f⟩,hsC,?_⟩
    exact original_hall_normalized_by_cartan_normalizer D c C hBC ⟨hs,hsC⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
