module
public import Theory.GroupAction.BinaryA4Pair
public import Theory.GroupTheory.SymmetricFourResidualGenerators

/-!
# Recognizing A₆ from two actual symmetric-four actors

Two symmetric-four subgroups act on an elementary abelian group of order
sixteen and have the same Sylow two-subgroup in the actual automorphism
group. A fixed-free cubic in the first actor and a one-dimensional fixed
space for the second actor's two-residual force the join of their embedded
two-residuals to be A₆.

Choose a nonidentity central involution of the common Sylow subgroup. The
symmetric-four core calculation puts it in both two-cores. Any nonidentity
cubic generates the corresponding residual together with this involution,
so the finite marked A₄-pair recognition applies. All inclusions, maps and
generated subgroups remain the original action subgroups.

This is the reusable action consumer for Aschbacher–Smith,
*The Classification of Quasithin Groups*, 14.3.19(4). The source constructs
the two actors, common Sylow image, fixed-free cubic and residual fixed line.
-/

namespace BinaryA4Pair
open Subgroup SymmetricFourResidualGenerators
local notation "S4" => Equiv.Perm (Fin 4)

private theorem fixes_closure_pair {W : Type*} [Group W]
    (r c : MulAut W) (w : W) :
    (∀ g ∈ closure ({r,c} : Set (MulAut W)), g w=w) ↔ r w=w ∧ c w=w := by
  constructor
  · intro h
    exact ⟨h r (subset_closure (by simp)),h c (subset_closure (by simp))⟩
  · rintro ⟨hr,hc⟩
    have he : closure ({r,c} : Set (MulAut W)) ≤ MulAction.stabilizer (MulAut W) w := by
      rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hr
      · exact hc
    exact fun g hg => he hg

/-- Two actual symmetric-four action subgroups with the shared core marking
have A₆ as the join of their embedded two-residuals. -/
public theorem canonical_model_of_symmetricFour_core_markers
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W=16) (X Y : Subgroup (MulAut W))
    (eX : X ≃* S4) (eY : Y ≃* S4) (r t c : MulAut W)
    (hrX : r∈(pCore 2 X).map X.subtype) (hrY : r∈(pCore 2 Y).map Y.subtype)
    (hrne : r≠1) (htX : t∈X) (ht3 : t^3=1) (htne : t≠1)
    (htfixed : ∀ w, t w=w → w=1) (hcY : c∈Y) (hc3 : c^3=1) (hcne : c≠1)
    (hfixed : Nat.card {w : W // ∀ g∈(pResidual 2 Y).map Y.subtype, g w=w}=2) :
    HasCanonicalModel ((pResidual 2 X).map X.subtype ⊔ (pResidual 2 Y).map Y.subtype) := by
  obtain ⟨hr2,_,hcomm,hnorm,hXgen⟩ := embedded_residual_generators X eX r t
    hrX htX hrne ht3 htne
  obtain ⟨_,hrc,_,_,hYgen⟩ := embedded_residual_generators Y eY r c
    hrY hcY hrne hc3 hcne
  have hfixed' : Nat.card {w : W // r w=w ∧ c w=w}=2 := by
    rw [← hYgen] at hfixed
    exact (Nat.card_congr (Equiv.subtypeEquivRight (fun w =>
      (fixes_closure_pair r c w).symm))).trans hfixed
  exact canonical_model_of_join hcard _ _ r t c hXgen.symm hYgen.symm hrne hr2 ht3
    htfixed hcomm hnorm hc3 hrc hfixed'

public theorem recognition_of_symmetricFour_core_markers
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W=16) (X Y : Subgroup (MulAut W))
    (eX : X ≃* S4) (eY : Y ≃* S4) (r t c : MulAut W)
    (hrX : r∈(pCore 2 X).map X.subtype) (hrY : r∈(pCore 2 Y).map Y.subtype)
    (hrne : r≠1) (htX : t∈X) (ht3 : t^3=1) (htne : t≠1)
    (htfixed : ∀ w, t w=w → w=1) (hcY : c∈Y) (hc3 : c^3=1) (hcne : c≠1)
    (hfixed : Nat.card {w : W // ∀ g∈(pResidual 2 Y).map Y.subtype, g w=w}=2) :
    Nonempty (((pResidual 2 X).map X.subtype ⊔ (pResidual 2 Y).map Y.subtype :
      Subgroup (MulAut W)) ≃* alternatingGroup (Fin 6)) :=
  (canonical_model_of_symmetricFour_core_markers hcard X Y eX eY r t c hrX hrY hrne
    htX ht3 htne htfixed hcY hc3 hcne hfixed).recognition

/-- A common Sylow two-subgroup supplies the shared involution automatically;
the second cubic is chosen inside the actual second symmetric-four actor. -/
public theorem canonical_model_of_symmetricFour_actors
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W=16) (X Y : Subgroup (MulAut W))
    (eX : X ≃* S4) (eY : Y ≃* S4) (SX : Sylow 2 X) (SY : Sylow 2 Y)
    (hS : (SX : Subgroup X).map X.subtype = (SY : Subgroup Y).map Y.subtype)
    (t : MulAut W) (htX : t∈X) (ht3 : t^3=1)
    (htfixed : ∀ w, t w=w → w=1)
    (hfixed : Nat.card {w : W // ∀ g∈(pResidual 2 Y).map Y.subtype, g w=w}=2) :
    HasCanonicalModel ((pResidual 2 X).map X.subtype ⊔ (pResidual 2 Y).map Y.subtype) := by
  let : Finite X := Finite.of_injective eX eX.injective
  obtain ⟨r,hrS,hrne,_,hrcent,hrcore,_⟩ := exists_central_sylow_involution eX SX
  have hrne' : (r : MulAut W)≠1 := by intro h; exact hrne (Subtype.ext h)
  have hrX : (r : MulAut W)∈(pCore 2 X).map X.subtype := mem_map_of_mem _ hrcore
  have hrS' : (r : MulAut W)∈(SY : Subgroup Y).map Y.subtype := by
    rw [← hS]
    exact mem_map_of_mem _ hrS
  have hrcent' : ∀ s : MulAut W, s∈(SY : Subgroup Y).map Y.subtype → Commute (r : MulAut W) s := by
    intro s hs
    rw [← hS] at hs
    obtain ⟨s,hs,rfl⟩ := hs
    exact (hrcent s hs).map X.subtype
  have hrY := embedded_central_sylow_mem_core Y eY SY r.val hrS' hrcent'
  obtain ⟨c,hc3,hcne⟩ := exists_cubic eY
  have hcne' : (c : MulAut W)≠1 := by intro h; exact hcne (Subtype.ext h)
  have htne : t≠1 := by
    intro ht
    have hsub : Subsingleton W := ⟨fun x y =>
      (htfixed x (by rw [ht]; rfl)).trans (htfixed y (by rw [ht]; rfl)).symm⟩
    have hsize : Nat.card W=1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub,⟨1⟩⟩
    omega
  exact canonical_model_of_symmetricFour_core_markers hcard X Y eX eY r.val t c.val
    hrX hrY hrne' htX ht3 htne htfixed c.property
    (congrArg Subtype.val hc3) hcne' hfixed

public theorem recognition_of_symmetricFour_actors
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W=16) (X Y : Subgroup (MulAut W))
    (eX : X ≃* S4) (eY : Y ≃* S4) (SX : Sylow 2 X) (SY : Sylow 2 Y)
    (hS : (SX : Subgroup X).map X.subtype = (SY : Subgroup Y).map Y.subtype)
    (t : MulAut W) (htX : t∈X) (ht3 : t^3=1)
    (htfixed : ∀ w, t w=w → w=1)
    (hfixed : Nat.card {w : W // ∀ g∈(pResidual 2 Y).map Y.subtype, g w=w}=2) :
    Nonempty (((pResidual 2 X).map X.subtype ⊔ (pResidual 2 Y).map Y.subtype :
      Subgroup (MulAut W)) ≃* alternatingGroup (Fin 6)) :=
  (canonical_model_of_symmetricFour_actors hcard X Y eX eY SX SY hS t htX ht3
    htfixed hfixed).recognition

end BinaryA4Pair
