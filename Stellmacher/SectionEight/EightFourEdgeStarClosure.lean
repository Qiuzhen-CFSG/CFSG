module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.EightFourEdgeFixedTransport

/-!
# The starred closure of an equivariant edge family

Retain the exact family F furnished by the edge-fixed transport theorem,
including its base subgroup, covariance, containment, and transporter
formula. The join C(l) of F(d,l) over first vertices is normal in G_l and
commutes with graph transport. At the initial first-step vertex it is exactly
the original normal closure of the barred fixed subgroup in that stabilizer.
The proof uses only the pure local Section Eight graph context. The
canonical theorem remains an exact wrapper; the edge family and action
are unchanged.

Reindexing the first vertex by the inverse graph actor proves covariance of
the join. A stabilizer actor fixes its vertex, so covariance makes it normalize
the join. At the initial first-step vertex every term in the transporter
formula comes from an actor in that stabilizer and therefore lies in the
original normal closure. Conversely, the join is normal there and contains
the base fixed subgroup, so it contains its normal closure. Both constructions
use the same subgroup and the same subtype homomorphism.

This identifies the Vstar_l defined immediately before source (7) in
Stellmacher (8.4), Journal of Algebra190 (1997), printed p39,
`refs/files/stellmacher-n-group.pdf`, with the earlier initial closure.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- The edge-family join is the original closure at the base and transports normally. -/
public theorem eight_four_edge_star_closure_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹) :
    let C := fun l => ⨆ d, F d l
    C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ∧
    (∀ g l, C (ctx.Γ.act g l) = (C l).conjBy g⁻¹) ∧
    (∀ d l, F d l ≤ C l) ∧
    (∀ l, NormalIn (C l) (GAt ctx.Γ l)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let C := fun l => ⨆ d, F d l
  let Z := w.oneJFixedPoints S
  let P := GAt Γ cp.firstStep
  let N0 := Subgroup.normalClosure (Z.subgroupOf P : Set P)
  let N := N0.map P.subtype
  have hFC (d l) : F d l ≤ C l := le_iSup (fun d => F d l) d
  have hCP (l) : C l ≤ GAt Γ l := iSup_le fun d => (hsub d l).trans inf_le_right
  have hCc (g : H) (l : Γ.Vertex) : C (Γ.act g l) = (C l).conjBy g⁻¹ := by
    apply le_antisymm
    · apply iSup_le
      intro d
      have hd := hcov g (Γ.act g⁻¹ d) l
      rw [← Γ.act_mul, inv_mul_cancel, Γ.act_one] at hd
      rw [hd]
      exact Subgroup.map_mono (hFC (Γ.act g⁻¹ d) l)
    · change (⨆ d, F d l).map (MulAut.conj g⁻¹).toMonoidHom ≤ C (Γ.act g l)
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro d
      change (F d l).conjBy g⁻¹ ≤ _
      rw [← hcov]
      exact hFC _ _
  have hCn (l) : NormalIn (C l) (GAt Γ l) := by
    refine ⟨hCP l, (Subgroup.normal_subgroupOf_iff_le_normalizer (hCP l)).mpr ?_⟩
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hg' := (GAt Γ l).inv_mem hg
    have hd : (GAt Γ l : Set H) = {x | Γ.act x l = l} := Γ.stabilizer_def l
    have hfix := (Set.ext_iff.mp hd g⁻¹).mp hg'
    have hh := hCc g⁻¹ l
    rw [hfix, inv_inv] at hh
    exact hh.symm
  have hZP : Z ≤ P := by
    change w.oneJFixedPoints S ≤ _
    rw [← hbase]
    exact (hsub cp.a cp.firstStep).trans inf_le_right
  have hZN : Z ≤ N := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hZP]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hNP : N ≤ P := Subgroup.map_subtype_le _
  have hNn : (N.subgroupOf P).Normal := by
    change ((N0.map P.subtype).comap P.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  have hCN : C cp.firstStep ≤ N := by
    apply iSup_le
    intro d
    rw [hformula]
    apply iSup_le
    intro g
    apply iSup_le
    intro hg
    have hd : (P : Set H) = {x | Γ.act x cp.firstStep = cp.firstStep} :=
      Γ.stabilizer_def cp.firstStep
    have hgp : g ∈ P := (Set.ext_iff.mp hd g).mpr hg.2
    have hgn := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNn (P.inv_mem hgp)
    have heq : N.conjBy g⁻¹ = N := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgn
    exact (Subgroup.map_mono hZN).trans_eq heq
  have hNC : N ≤ C cp.firstStep := by
    have hZC : Z ≤ C cp.firstStep := by
      change w.oneJFixedPoints S ≤ _
      rw [← hbase]
      exact hFC cp.a cp.firstStep
    let _ := (hCn cp.firstStep).2
    have hn : N0 ≤ (C cp.firstStep).subgroupOf P :=
      Subgroup.normalClosure_le_normal (fun z hz => hZC hz)
    rintro _ ⟨z,hz,rfl⟩
    exact hn hz
  exact ⟨le_antisymm hCN hNC, hCc, hFC, hCn⟩

/-- Canonical-context wrapper retaining the original graph and edge family. -/
public theorem eight_four_edge_star_closure
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹) :
    let C := fun l => ⨆ d, F d l
    C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ∧
    (∀ g l, C (ctx.Γ.act g l) = (C l).conjBy g⁻¹) ∧
    (∀ d l, F d l ≤ C l) ∧
    (∀ l, NormalIn (C l) (GAt ctx.Γ l)) := by
  exact eight_four_edge_star_closure_local ctx.toLocalContext w F hbase hcov hsub hformula

end Stellmacher.SectionEight
