module
public import Stellmacher.SectionEight.EightFourEdgeFixedNormal
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Equivariant fixed subgroups on ordered edges

In the nontrivial-closure branch of Stellmacher (8.4), the initial barred
fixed subgroup determines a family on ordered vertex pairs. At the initial
edge the family is the original fixed subgroup. Every member lies in the
center module of its first vertex and the stabilizer of its second vertex,
and the family commutes with graph transport by the inverse conjugation
required by this graph's right-action convention.

Define each member as the join of all conjugate fixed subgroups whose actors
carry the initial ordered edge to that pair. The previously proved normality
inside the initial edge stabilizer makes every summand at the initial edge
equal to the original subgroup. Reindexing actors by right multiplication
gives equivariance. The graph covariance of centers and stabilizers proves
the containments. The family is trivial off the initial ordered-edge orbit;
no choice of transporting actor or later normality conclusion is needed.

This constructs the subgroups Z_(d,l) defined immediately before source (7)
of Stellmacher (8.4), Journal of Algebra190 (1997), printed p39,
`refs/files/stellmacher-n-group.pdf`. Their normal closures in the second
vertex stabilizer are the corresponding starred vertex modules.

The local API preserves all actual graph, quotient and configuration data.
Canonical statements remain exact wrappers, using fieldwise local data
conversion where required.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- The barred fixed subgroup extends equivariantly along its ordered-edge orbit. -/
public theorem eight_four_edge_fixed_transport_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    ∃ F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H,
      F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S ∧
      (∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹) ∧
      (∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l) ∧
      (∀ d l, F d l = ⨆ (g : H)
        (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
          ctx.Γ.act g ctx.criticalPath.firstStep = l),
        (w.oneJFixedPoints S).conjBy g⁻¹) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Z := w.oneJFixedPoints S
  let F : Γ.Vertex → Γ.Vertex → Subgroup H := fun d l =>
    ⨆ (g : H) (_ : Γ.act g cp.a = d ∧ Γ.act g cp.firstStep = l), Z.conjBy g⁻¹
  have hnormal : NormalIn Z (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) :=
    eight_four_edge_fixed_normal_local ctx hcenter w hbranch
  have hbase : F cp.a cp.firstStep = Z := by
    apply le_antisymm
    · apply iSup_le
      intro g
      apply iSup_le
      intro hg
      have hge : g ∈ GAt Γ cp.a ⊓ GAt Γ cp.firstStep := by
        constructor
        · have hd : (GAt Γ cp.a : Set H) = {x | Γ.act x cp.a = cp.a} :=
            Γ.stabilizer_def cp.a
          exact (Set.ext_iff.mp hd g).mpr hg.1
        · have hd : (GAt Γ cp.firstStep : Set H) =
              {x | Γ.act x cp.firstStep = cp.firstStep} := Γ.stabilizer_def cp.firstStep
          exact (Set.ext_iff.mp hd g).mpr hg.2
      have hgn := (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp
        hnormal.2 ((GAt Γ cp.a ⊓ GAt Γ cp.firstStep).inv_mem hge)
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgn).le
    · have hindex : Γ.act (1 : H) cp.a = cp.a ∧
          Γ.act (1 : H) cp.firstStep = cp.firstStep := ⟨Γ.act_one _, Γ.act_one _⟩
      have hle : Z.conjBy (1 : H)⁻¹ ≤ F cp.a cp.firstStep := le_iSup_of_le (1 : H)
        (le_iSup_of_le hindex (le_refl (Z.conjBy (1 : H)⁻¹)))
      simpa only [inv_one, Subgroup.conjBy_one] using hle
  refine ⟨F, hbase, ?_, ?_, ?_⟩
  · intro g d l
    change (⨆ (k : H) (_ : Γ.act k cp.a = Γ.act g d ∧
      Γ.act k cp.firstStep = Γ.act g l), Z.conjBy k⁻¹) =
        (⨆ (k : H) (_ : Γ.act k cp.a = d ∧
          Γ.act k cp.firstStep = l), Z.conjBy k⁻¹).conjBy g⁻¹
    simp only [Subgroup.conjBy, Subgroup.map_iSup]
    apply le_antisymm
    · apply iSup_le
      intro k
      apply iSup_le
      intro hk
      have hkg : Γ.act (k * g⁻¹) cp.a = d ∧
          Γ.act (k * g⁻¹) cp.firstStep = l := by
        constructor <;> rw [Γ.act_mul]
        · rw [hk.1, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
        · rw [hk.2, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
      apply le_iSup_of_le (k * g⁻¹)
      apply le_iSup_of_le hkg
      change Z.conjBy k⁻¹ ≤ (Z.conjBy (k * g⁻¹)⁻¹).conjBy g⁻¹
      rw [Subgroup.conjBy_conjBy]
      simp
    · apply iSup_le
      intro k
      apply iSup_le
      intro hk
      have hkg : Γ.act (k * g) cp.a = Γ.act g d ∧
          Γ.act (k * g) cp.firstStep = Γ.act g l := by
        constructor <;> rw [Γ.act_mul]
        · rw [hk.1]
        · rw [hk.2]
      apply le_iSup_of_le (k * g)
      apply le_iSup_of_le hkg
      change (Z.conjBy k⁻¹).conjBy g⁻¹ ≤ Z.conjBy (k * g)⁻¹
      rw [Subgroup.conjBy_conjBy, mul_inv_rev]
  · intro d l
    apply iSup_le
    intro g
    apply iSup_le
    intro hg
    have hZa : Z ≤ z Γ cp.a := Subgroup.map_subtype_le _
    have hZb : Z ≤ stabilizer Γ cp.firstStep := hnormal.1.trans inf_le_right
    refine le_inf ?_ ?_
    · rw [← hg.1]
      change Z.conjBy g⁻¹ ≤ z Γ (Γ.act g cp.a)
      rw [z_act Γ g cp.a]
      exact Subgroup.map_mono hZa
    · rw [← hg.2]
      change Z.conjBy g⁻¹ ≤ stabilizer Γ (Γ.act g cp.firstStep)
      rw [stabilizer_act Γ g cp.firstStep]
      exact Subgroup.map_mono hZb
  · intro d l
    rfl

/-- Canonical specializations preserving the supplied graph, witness and family. -/
public theorem eight_four_edge_fixed_transport
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    ∃ F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H,
      F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S ∧
      (∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹) ∧
      (∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l) ∧
      (∀ d l, F d l = ⨆ (g : H)
        (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
          ctx.Γ.act g ctx.criticalPath.firstStep = l),
        (w.oneJFixedPoints S).conjBy g⁻¹) := by
  exact eight_four_edge_fixed_transport_local ctx.toLocalContext hcenter w hbranch

end Stellmacher.SectionEight
