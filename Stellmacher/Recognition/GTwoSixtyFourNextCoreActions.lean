module

public import Stellmacher.Recognition.GTwoSixtyFourIndexTwo
public import Theory.GroupTheory.PCoreNormalizedOvergroup
public import FeitThompson.BGsection6.Defs

/-!
# The second vertex action on the order-64 transfer subgroup

Let X be the embedded second core, E its vertex's 2-residual, and U the
canonical index-two subgroup of the supplied Sylow S. The actual second
vertex normalizes X ∩ U: its residual has commutators with X in the
quaternion subgroup X ∩ E ≤ U, while S normalizes both X and U. The
residual and S generate the vertex. Centralizers of X preserve this
intersection as well.

The common Sylow also identifies O₂(N_G(X)) with X. Under the ambient
N₂ and trivial odd-core assumptions, characteristic two gives C_G(X) ≤ X.
The final conditional theorem reduces ambient action control to showing
that N_G(X) lies in the product of the second vertex and C_G(X).
That containment remains a separate hypothesis: the vertex has not been
identified with the full ambient normalizer.

Source: the actual local pair in Stellmacher (8.6)(a) and the local-type
definition following it, `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

private theorem mapped_normalizer_le
    {G K : Type*} [Group G] [Group K]
    (f : K →* G) (P Q : Subgroup K) (hQP : Q ≤ P)
    (hQ : (Q.subgroupOf P).Normal) :
    P.map f ≤ Subgroup.normalizer (Q.map f : Set G) :=
  (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQ)).trans
    (Subgroup.le_normalizer_map f)

/-- The part of the canonical transfer subgroup contained in the second core. -/
@[expose] public def gTwoCard64NextTransferIntersection
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    Subgroup G :=
  letI := data.groupK
  letI := data.finiteK
  (QAt data.Γ data.criticalPath.firstStep).map data.embedding ⊓
    (gTwoCard64TransferSubgroup data).map (data.sylowIntersection : Subgroup G).subtype

/-- The actual second vertex normalizes the transfer intersection. -/
public theorem gTwo_card64_next_vertex_normalizes_transfer_intersection
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    (GAt data.Γ data.criticalPath.firstStep).map data.embedding ≤
      Subgroup.normalizer (gTwoCard64NextTransferIntersection data : Set G) := by
  let := data.groupK
  let := data.finiteK
  let S := data.sylowIntersection
  let P0 := GAt data.Γ data.criticalPath.firstStep
  let X0 := QAt data.Γ data.criticalPath.firstStep
  let E0 := EAt data.Γ data.criticalPath.firstStep
  let P := P0.map data.embedding
  let X := X0.map data.embedding
  let E := E0.map data.embedding
  let R := (X0 ⊓ E0).map data.embedding
  let U := (gTwoCard64TransferSubgroup data).map (S : Subgroup G).subtype
  let D := gTwoCard64NextTransferIntersection data
  have hX0 : X0 = twoCoreIn P0 := data.Γ.twoCoreAt_def _
  have hE0 : E0 = twoResidualIn P0 := data.Γ.twoResidualAt_def _
  have hX0P : X0 ≤ P0 := by rw [hX0]; exact twoCoreIn_le _
  have hE0P : E0 ≤ P0 := by rw [hE0]; exact twoResidualIn_le _
  have hPX : P ≤ Subgroup.normalizer (X : Set G) :=
    mapped_normalizer_le data.embedding P0 X0 hX0P (by
      rw [hX0]; exact twoCoreIn_normal _)
  have hPE : P ≤ Subgroup.normalizer (E : Set G) :=
    mapped_normalizer_le data.embedding P0 E0 hE0P (by
      rw [hE0]; exact twoResidualIn_normal _)
  have hXP : X ≤ P := Subgroup.map_mono hX0P
  have hEP : E ≤ P := Subgroup.map_mono hE0P
  have hSP : (S : Subgroup G) ≤ P := by
    rw [← data.intersection_eq]; exact inf_le_right
  have hUeq : U =
      (twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding ⊔ R :=
    Subgroup.map_subgroupOf_eq_of_le (gTwo_card64_transfer_le_sylow data)
  have hUS : U ≤ (S : Subgroup G) := Subgroup.map_subtype_le _
  have hSU : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mp
    have heq : U.subgroupOf (S : Subgroup G) = gTwoCard64TransferSubgroup data := by
      exact Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective _
    rw [heq]
    exact (gTwo_card64_transfer_structure data hcard).1
  have hSD : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf (hSP.trans hPX) hSU).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRX : R ≤ X := Subgroup.map_mono inf_le_left
  have hRU : R ≤ U := by rw [hUeq]; exact le_sup_right
  have hEX : ⁅E, X⁆ ≤ R := by
    have hR : R = X ⊓ E := Subgroup.map_inf _ _ data.embedding data.embedding_injective
    rw [hR]
    exact le_inf
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hEP.trans hPX))
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hXP.trans hPE))
  have hED : E ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl inf_le_left).trans
        (hEX.trans (le_inf hRX hRU)))
  have hgen : E ⊔ (S : Subgroup G) = P := by
    have hres : E = twoResidualIn P := by
      dsimp [E]
      rw [hE0]
      exact map_twoResidualAmbient_of_subgroup_image
        P0 data.embedding P rfl
    rw [hres]
    exact twoResidualIn_sup_sylow ⟨hSP, S.subtype hSP,
      Subgroup.map_subgroupOf_eq_of_le hSP⟩
  change P ≤ _
  rw [← hgen]
  exact sup_le hED hSD

/-- The second vertex together with the centralizer of its core preserves
the transfer intersection. This is the precise ambient containment needed
for the remaining normalizer case. -/
public theorem gTwo_card64_next_vertex_centralizer_normalizes_transfer_intersection
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    (GAt data.Γ data.criticalPath.firstStep).map data.embedding ⊔
      Subgroup.centralizer
        ((QAt data.Γ data.criticalPath.firstStep).map data.embedding : Set G) ≤
      Subgroup.normalizer (gTwoCard64NextTransferIntersection data : Set G) := by
  let := data.groupK
  let := data.finiteK
  refine sup_le (gTwo_card64_next_vertex_normalizes_transfer_intersection data hcard) ?_
  exact (Subgroup.centralizer_le (show
    (gTwoCard64NextTransferIntersection data : Set G) ⊆
      ((QAt data.Γ data.criticalPath.firstStep).map data.embedding : Set G) from
    fun _ h => h.1)).trans (Subgroup.centralizer_le_normalizer _)

private theorem core_map_injective
    {G K : Type*} [Group G] [Group K] (f : K →* G)
    (hf : Function.Injective f) (P : Subgroup K) :
    (twoCoreIn P).map f = twoCoreIn (P.map f) := by
  let e := P.equivMapOfInjective f hf
  have h := pCore_map_iso 2 e
  change ((pCore 2 P).map P.subtype).map f =
    (pCore 2 (P.map f)).map (P.map f).subtype
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- The full normalizer has exactly the supplied second core as its two-core.
This uses the common ambient Sylow, without identifying the normalizer with
the supplied vertex. -/
public theorem gTwo_next_normalizer_core
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    let X := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    twoCoreIn (Subgroup.normalizer (X : Set G)) = X := by
  let := data.groupK
  let := data.finiteK
  let P0 := GAt data.Γ data.criticalPath.firstStep
  let X0 := QAt data.Γ data.criticalPath.firstStep
  let P := P0.map data.embedding
  let X := X0.map data.embedding
  have hXP : X0 = twoCoreIn P0 := data.Γ.twoCoreAt_def _
  have hcore : twoCoreIn P = X := by
    rw [← core_map_injective data.embedding data.embedding_injective, ← hXP]
  have hPN : P ≤ Subgroup.normalizer (X : Set G) :=
    mapped_normalizer_le data.embedding P0 X0
      (by rw [hXP]; exact twoCoreIn_le _)
      (by rw [hXP]; exact twoCoreIn_normal _)
  have hSP : (data.sylowIntersection : Subgroup G) ≤ P := by
    rw [← data.intersection_eq]; exact inf_le_right
  change twoCoreIn (Subgroup.normalizer (X : Set G)) = X
  calc
    twoCoreIn (Subgroup.normalizer (X : Set G)) = twoCoreIn P :=
      Subgroup.mapped_pCore_eq_of_normalized_local_pCore
        data.sylowIntersection P _ hSP hPN (by
          change Subgroup.normalizer (X : Set G) ≤
            Subgroup.normalizer (twoCoreIn P : Set G)
          rw [hcore])
    _ = X := hcore

/-- Characteristic two of the actual ambient normalizer makes the second core
self-centralizing in the whole ambient group. -/
public theorem gTwo_card64_next_core_centralizer_le
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let X := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Subgroup.centralizer (X : Set G) ≤ X := by
  let := data.groupK
  let := data.finiteK
  let X0 := QAt data.Γ data.criticalPath.firstStep
  let X := X0.map data.embedding
  let N := Subgroup.normalizer (X : Set G)
  have hXcard : Nat.card X = 32 := by
    rw [Subgroup.card_map_of_injective data.embedding_injective]
    exact (gTwo_card64_vertex_structure data hcard).2.2.1
  have hXne : X ≠ ⊥ := by
    intro heq
    rw [heq, Subgroup.card_bot] at hXcard
    omega
  have hXtwo : IsPGroup 2 X := IsPGroup.of_card (n := 5) (by simpa using hXcard)
  have hlocal : IsTwoLocal N := ⟨X, hXne, hXtwo, rfl⟩
  have hchar := centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot (hN N hlocal)
    (hcore N hlocal)
  have hcoreN : (pCore 2 N).map N.subtype = X := gTwo_next_normalizer_core data
  change Subgroup.centralizer (X : Set G) ≤ X
  intro c hc
  have hcN : c ∈ N := Subgroup.centralizer_le_normalizer _ hc
  have hcCore : (⟨c, hcN⟩ : N) ∈ pCore 2 N := by
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hqX : (q : G) ∈ X := by
      rw [← hcoreN]
      exact Subgroup.mem_map_of_mem N.subtype hq
    exact Subgroup.mem_centralizer_iff.mp hc (q : G) hqX
  rw [← hcoreN]
  exact Subgroup.mem_map_of_mem N.subtype hcCore

/-- A precise reduction of the ambient action problem to a normalizer
containment. No involution hypothesis is needed for this implication. -/
public theorem gTwo_card64_next_core_preserves_transfer_of_normalizer_le
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let X := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Subgroup.normalizer (X : Set G) ≤
      (GAt data.Γ data.criticalPath.firstStep).map data.embedding ⊔
        Subgroup.centralizer (X : Set G) →
    ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x y : data.sylowIntersection,
      (x : G) ∈ X → g⁻¹ * (x : G) * g = (y : G) →
        (x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data) := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  intro hbound g hg x y hx hxy
  let X := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
  let D := gTwoCard64NextTransferIntersection data
  let U := gTwoCard64TransferSubgroup data
  have hgD : g ∈ Subgroup.normalizer (D : Set G) :=
    gTwo_card64_next_vertex_centralizer_normalizes_transfer_intersection data hcard
      (hbound hg)
  have hy : (y : G) ∈ X := by
    rw [← hxy]
    exact (Subgroup.mem_normalizer_iff''.mp hg (x : G)).mp hx
  have hmem (z : data.sylowIntersection) (hz : (z : G) ∈ X) :
      (z : G) ∈ D ↔ z ∈ U := by
    change ((z : G) ∈ X ∧ (z : G) ∈ U.map
      (data.sylowIntersection : Subgroup G).subtype) ↔ z ∈ U
    rw [and_iff_right hz]
    exact Subgroup.mem_map_iff_mem (data.sylowIntersection : Subgroup G).subtype_injective
  rw [← hmem x hx, ← hmem y hy]
  simpa only [hxy] using Subgroup.mem_normalizer_iff''.mp hgD (x : G)

end Stellmacher.Recognition
