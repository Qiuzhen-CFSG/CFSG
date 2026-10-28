module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusReduction
public import Theory.AlgebraicGroup.Bor1.GeometricCertificates

/-!
# Borel–normalizer generation from fixed-torus Borel geometry

If two conjugate Borels contain the same maximal torus, conjugacy of maximal
tori inside the first Borel adjusts their conjugator into the torus normalizer.
Consequently generation by all Borels containing that torus implies generation
by one Borel and the torus normalizer. Both closures are abstract subgroup
closures, so no passage from Zariski density to abstract generation is used.

The adjustment is the argument of Borel, *Linear Algebraic Groups*, 11.19(b).
The assembly combines it with 13.7 to obtain the generation clause of 14.15 T1
and GLS3, Definition 1.11.1(a), Theorem 1.11.3. Sources:
`refs/KGroup/Bor1/Chapter4.tex` and `refs/KGroup/GLS3/Chapter1.tex`;
the omitted 13.7 passage is on printed pp. 167–168 of Borel's second edition.

These results are conditional reductions: ambient Borel conjugacy and the
geometric generation theorem 13.7 remain explicit premises of the assembly.
Neither the numbered root-structure placeholders nor a Tits-system assumption
is used. The unconditional reductive generation theorem remains to be assembled
after the geometric premises have been proved.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Adjust an ambient Borel conjugator to normalize the common maximal torus.
Only the proved conjugacy theorem for maximal tori in a connected solvable
group is needed for the adjustment. -/
public theorem normalizer_conjugate_of_borel_conjugate
    {B C T : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B) (hTC : T ≤ C)
    (hconj : ∃ g : Variety.Point G, C = B.conjugate g) :
    ∃ n : Variety.Point G, n ∈ T.normalizer.toSubgroup ∧ C = B.conjugate n := by
  obtain ⟨g, hCg⟩ := hconj
  have hTgB : T.conjugate g⁻¹ ≤ B := by
    have h := conjugate_le hTC g⁻¹
    rwa [hCg, ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
      ClosedSubgroup.conjugate_one] at h
  obtain ⟨b, hb, hTb⟩ := BorelSelfNormalizer.maximalTori_conjugate_inside_borel
    hB hT (conjugate_isMaximalTorus hT g⁻¹) hTB hTgB
  have hTn : T.conjugate (g * b) = T := by
    rw [← ClosedSubgroup.conjugate_conjugate, ← hTb,
      ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
      ClosedSubgroup.conjugate_one]
  have hn : g * b ∈ T.normalizer.toSubgroup := by
    change g * b ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hback : ∀ x : Variety.Point G,
        (g * b)⁻¹ * x * (g * b) ∈ T.toSubgroup ↔ x ∈ T.toSubgroup := by
      intro x
      rw [← T.mem_conjugate_iff, hTn]
      rfl
    have h := hback ((g * b) * t * (g * b)⁻¹)
    have hc : (g * b)⁻¹ * ((g * b) * t * (g * b)⁻¹) * (g * b) = t := by
      group
    rwa [hc] at h
  refine ⟨g * b, hn, ?_⟩
  rw [← ClosedSubgroup.conjugate_conjugate,
    ClosedSubgroup.conjugate_eq_self_of_mem_normalizer b (Subgroup.le_normalizer hb)]
  exact hCg

/-- Conditional assembly of abstract generation by `B` and `N(T)` from
Borel conjugacy and generation by all Borels containing `T` (Borel 13.7).
The two geometric premises must be discharged by the source-theorem caller. -/
public theorem borel_normalizer_generation_of_torus_borel_generation_and_conjugacy
    {B T : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hconj : ∀ C : BorelContainingIndex T,
      ∃ g : Variety.Point G, C.1 = B.conjugate g)
    (hgen : Subgroup.closure
      (⋃ C : BorelContainingIndex T, (C.1 : Set (Variety.Point G))) = ⊤) :
    Subgroup.closure ((B.toSubgroup : Set (Variety.Point G)) ∪
      (T.normalizer.toSubgroup : Set (Variety.Point G))) = ⊤ := by
  let H := Subgroup.closure ((B.toSubgroup : Set (Variety.Point G)) ∪
    (T.normalizer.toSubgroup : Set (Variety.Point G)))
  have hBH : B.toSubgroup ≤ H := fun _ hx =>
    Subgroup.subset_closure (Or.inl hx)
  have hNH : T.normalizer.toSubgroup ≤ H := fun _ hx =>
    Subgroup.subset_closure (Or.inr hx)
  change H = ⊤
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le H).mpr
  intro x hx
  obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n, hn, hCn⟩ := normalizer_conjugate_of_borel_conjugate
    hB hT hTB C.2.2 (hconj C)
  have hxB : n⁻¹ * x * n ∈ B.toSubgroup :=
    (B.mem_conjugate_iff n x).mp (hCn ▸ hxC)
  have hxH := H.mul_mem (H.mul_mem (hNH hn) (hBH hxB)) (H.inv_mem (hNH hn))
  have hc : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
  rwa [hc] at hxH

end Theory.AlgebraicGroup.BorelIntersectionGeometry
