module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.AlmostSimpleAction
public import Theory.GroupTheory.ConjugateSpanNilpotent

/-!
# Residual displacement from the source commutator comparison

The normal-section action works modulo any subgroup normalized by the local
stabilizer. Apply it to W modulo [W,Q_c] Z_c. This denominator is normalized
because W, Q_c and Z_c are. A local actor E outside Q_c whose displacement
of W lies in [W,Q_c][Z_c,E] therefore forces the same displacement bound
for the whole local two-residual. Neither the denominator's containment in
W nor commutativity of W is needed.

Source: Meierfrankenfeld–Stellmacher (1993), the displayed comparison and
following residual displacement in the proof of (5.9), printed p.921.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

/-- The original residual fixes a relatively normal local section whenever
an actor outside the actual quotient kernel fixes that section. -/
theorem local_section_residual_commutator
    {c : Vertex R} {J : Type*} [Group J]
    (q : stabilizer R c →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R c).subgroupOf (stabilizer R c))
    (hp : IsPGroup 2 (Q R c))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R c)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R c)).map q : Set J) = ⊥)
    (W D E : Subgroup (FreeAmalgam R)) (hW : W ≤ stabilizer R c)
    (hWN : stabilizer R c ≤ normalizer (W : Set _))
    (hDN : stabilizer R c ≤ normalizer (D : Set _))
    (hE : E ≤ stabilizer R c) (hEQ : ¬ E ≤ Q R c)
    (hc : ⁅W,E⁆ ≤ D) : ⁅W,Ltilde R c⁆ ≤ D := by
  let G := stabilizer R c
  let W₀ := W.subgroupOf G
  let D₀ := D.subgroupOf G
  let E₀ := E.subgroupOf G
  let := finite_stabilizer R c
  let := hS
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hWN
  let : D₀.Normal := normal_subgroupOf_of_le_normalizer hDN
  have hker : IsPGroup 2 q.ker := by
    rw [hk]
    exact hp.comap_subtype
  have hescape : ¬ E₀ ≤ q.ker := by
    intro h
    apply hEQ
    intro t ht
    have hh := h (show (⟨t,hE ht⟩ : G) ∈ E₀ from ht)
    rw [hk] at hh
    exact hh
  have hc₀ : ⁅W₀,E₀⁆ ≤ D₀ := by
    apply commutator_le.mpr
    intro w hw t ht
    exact hc (commutator_mem_commutator hw ht)
  have hh := map_mono (f := G.subtype)
    (commutator_pResidual_le_of_monolithic_kernel_escape 2 q hq hker hC
      W₀ D₀ E₀ hescape hc₀)
  rw [map_commutator, map_subgroupOf_eq_of_le hW] at hh
  exact hh.trans (map_comap_le _ _)

/-- The literal displayed comparison gives the residual displacement needed
by the span-collapse argument. -/
theorem residual_displacement_of_comparison
    {c : Vertex R} {J : Type*} [Group J]
    (q : stabilizer R c →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R c).subgroupOf (stabilizer R c))
    (hp : IsPGroup 2 (Q R c))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R c)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R c)).map q : Set J) = ⊥)
    (W E : Subgroup (FreeAmalgam R)) (hW : W ≤ stabilizer R c)
    (hWN : stabilizer R c ≤ normalizer (W : Set _))
    (hE : E ≤ stabilizer R c) (hEQ : ¬ E ≤ Q R c)
    (hc : ⁅W,E⁆ ≤ ⁅W,Q R c⁆ ⊔ ⁅Z R c,E⁆) :
    ⁅W,Ltilde R c⁆ ≤ ⁅W,Q R c⁆ ⊔ Z R c := by
  let D := ⁅W,Q R c⁆ ⊔ Z R c
  have hDN : stabilizer R c ≤ normalizer (D : Set _) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hWN hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R c hg)]
  have hZE : ⁅Z R c,E⁆ ≤ Z R c :=
    le_normalizer_iff_commutator_le_left.mp (hE.trans (Z_normalized R c))
  exact local_section_residual_commutator q hq hk hp hS hC W D E hW hWN hDN hE hEQ
    (hc.trans (sup_le_sup_left hZE _))

/-- Apply the comparison to the literal two-stage source span. Its local
normality is derived from the generating pair; the first span's containment
in Q is the separate distance-four geometry conclusion. -/
theorem source_span_residual_displacement_of_comparison
    {c mu : Vertex R} (hc : color R c = false) (hmu : color R mu = false)
    (hd : (cosetGraph R).dist c mu ≤ 2)
    {J : Type*} [Group J]
    (q : stabilizer R c →* J) (hq : Function.Surjective q)
    (hk : q.ker = (Q R c).subgroupOf (stabilizer R c))
    (hp : IsPGroup 2 (Q R c))
    (hS : IsSimpleGroup ((pResidual 2 (stabilizer R c)).map q))
    (hC : centralizer ((pResidual 2 (stabilizer R c)).map q : Set J) = ⊥)
    (H₂ E : Subgroup (FreeAmalgam R))
    (hVQ : conjugateSpanBy (Z R c) (stabilizer R mu) ≤ Q R c)
    (hgen : (stabilizer R c ⊓ centralizer (H₂ : Set _)) ⊔ E = stabilizer R c)
    (hEQ : ¬ E ≤ Q R c)
    (hcompare :
      let W := conjugateSpanBy (conjugateSpanBy (Z R c) (stabilizer R mu))
        (stabilizer R c ⊓ centralizer (H₂ : Set _))
      ⁅W,E⁆ ≤ ⁅W,Q R c⁆ ⊔ ⁅Z R c,E⁆) :
    let W := conjugateSpanBy (conjugateSpanBy (Z R c) (stabilizer R mu))
      (stabilizer R c ⊓ centralizer (H₂ : Set _))
    ⁅W,Ltilde R c⁆ ≤ ⁅W,Q R c⁆ ⊔ Z R c := by
  let V₀ := conjugateSpanBy (Z R c) (stabilizer R mu)
  let C₀ := stabilizer R c ⊓ centralizer (H₂ : Set (FreeAmalgam R))
  let W := conjugateSpanBy V₀ C₀
  have hQV : Q R c ≤ normalizer (V₀ : Set _) :=
    (Q_le_stabilizer_of_dist_le_two c mu hc hmu hd).trans
      (le_normalizer_conjugateSpanBy (Z R c) (stabilizer R mu))
  have hWN := conjugateSpanBy_normalized_of_commutator_comparison
    V₀ C₀ (Q R c) (Z R c) E (stabilizer R c) hQV
    (Q_normalized R c) (Z_normalized R c)
    (le_conjugateSpanBy (Z R c) (stabilizer R mu)) hgen hcompare
  have hWQ : W ≤ Q R c :=
    conjugateSpanBy_le hVQ (inf_le_left.trans (Q_normalized R c))
  have hE : E ≤ stabilizer R c := hgen ▸ le_sup_right
  exact residual_displacement_of_comparison q hq hk hp hS hC W E
    (hWQ.trans (fun _ hx => hx.1)) hWN hE hEQ hcompare

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
