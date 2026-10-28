module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# The local closure on the original chosen flag

The seed for G.2.2 is V₃, and its perfect acting subgroup is the literal
solvable residual L₁. This avoids identifying O²(N_L(V₁)) with
N_L(V₁)^∞: an odd torus in the parabolic quotient would invalidate that
identification. Since L₁ already normalizes V₁ and is perfect, the local
subgroup in this G.2 setup is exactly L₁. This supplies G.2.2 only;
later recognition results involving the original L require their own setup.

The remaining inputs are the preceding flag invariance and irreducibility
of V₃/V₁. Characteristic two and both Sylow conditions are constructed
from the original chosen source hypotheses. No conclusion about the closure
is assumed. Source: Aschbacher--Smith 11.5.5(1--2), printed p.780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The local H₁-closure, with the source seed V₃. -/
def localClosure (H₁ : Subgroup G) : Subgroup G := conjugateSpanBy E.V₃ H₁

/-- The G.2 setup specialized to the perfect local actor L₁. -/
def closureSetup (H₁ : Subgroup G) : ChapterG.Section02.Setup G where
  V := E.V₃
  V₁ := E.V₁
  L := E.L₁
  T := T
  H := H₁

theorem L₁_perfect : Group.IsPerfect E.L₁ :=
  LocalGeometry.localResidual_perfect E.V₁

theorem L₁_le_G₁ : E.L₁ ≤ E.G₁ := (residualIn_le _).trans inf_le_right

/-- Perfectness of the source residual implies two-perfectness. -/
theorem L₁_twoResidual : pResidual 2 E.L₁ = ⊤ := by
  let := E.L₁_perfect
  apply (pResidual_eq_top_iff 2 E.L₁).mpr
  intro N hN hq
  let := hN
  let : Group.IsNilpotent (E.L₁ ⧸ N) := hq.isNilpotent
  let : Group.IsSolvable (E.L₁ ⧸ N) := inferInstance
  have hh := solvableResidual_le_of_solvable_quotient N
  rwa [solvableResidual_eq_top, top_le_iff] at hh

/-- The two-residual in this G.2 setup really is the original solvable residual. -/
theorem closureSetup_local_eq (H₁ : Subgroup G) : (E.closureSetup H₁).L₁ = E.L₁ := by
  change (pResidual 2 (E.L₁ ⊓ E.G₁ : Subgroup G)).map (E.L₁ ⊓ E.G₁).subtype = _
  rw [inf_eq_left.mpr E.L₁_le_G₁, E.L₁_twoResidual,
    ← MonoidHom.range_eq_map, range_subtype]

/-- Every local overgroup of T in the point normalizer has characteristic two. -/
theorem local_characteristic_two (hp : E.point ≠ ⊥)
    (H₁ : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H₁) (hH : H₁ ≤ E.G₁) :
    generalizedFitting H₁ = pCore 2 H₁ := by
  have hpoint := D.centralQuotientPreimage_ne_bot E.point hp
  have hVH : E.V₁ ≤ H₁ := E.V₁_le.trans (D.le_sylow.trans hTH)
  have hcore : E.V₁ ≤ H₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (@IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary E.point))
      hVH hH
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  apply Chapter1.mem_He_iff.mp
  apply Chapter1.lemma_1_1_4_6 T (E.input.source.simpleQTKE.evenCharacteristic T)
  exact ⟨fun hz => hpoint (bot_unique (hz ▸ hcore)), hTH⟩

/-- All G.2.1 hypotheses from the actual preceding flag geometry.
The invariant interval is exactly irreducibility of V₃/V₁ under L₁T. -/
theorem closureSetup_hypothesis (hp : E.point ≠ ⊥)
    (h13 : E.V₁ ≤ E.V₃) (hne : E.V₁ ≠ E.V₃)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁) :
    (E.closureSetup H₁).Hypothesis := by
  have hres := E.closureSetup_local_eq H₁
  refine {
    elementary := D.centralQuotientPreimage_elementary E.threeSpace
    point_ne_bot := D.centralQuotientPreimage_ne_bot E.point hp
    point_le := h13
    residual := E.L₁_twoResidual
    V_le_T := (D.centralQuotientPreimage_le E.threeSpace).trans D.le_sylow
    T_normalizes_point := hT1
    T_normalizes_V := le_sup_right.trans hlocal
    T_normalizes_L := LocalGeometry.sylow_normalizes_localResidual D E.V₁ hT1
    sylow_LT := ⟨T.subtype le_sup_right, ?_⟩
    H_le := hH
    local_le := ?_
    sylow_H := ⟨T.subtype (le_sup_right.trans hLH), ?_⟩
    characteristic_two := E.local_characteristic_two hp H₁ (le_sup_right.trans hLH) hH
    local_normalizes_V := ?_
    quotient_nonzero := hne
    irreducible := ?_ }
  · exact map_subgroupOf_eq_of_le le_sup_right
  · change (E.closureSetup H₁).L₁ ⊔ (T : Subgroup G) ≤ H₁
    rw [hres]
    exact hLH
  · exact map_subgroupOf_eq_of_le (le_sup_right.trans hLH)
  · change (E.closureSetup H₁).L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G)
    rw [hres]
    exact hlocal
  · intro A hA hB hn
    change (E.closureSetup H₁).L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) at hn
    rw [hres] at hn
    exact hirr A hA hB hn

private def toLocalTilde (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) : H₁ →* E.tilde H₁ where
  toFun x := ⟨QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨x, hH x.property⟩,
    ⟨⟨x, hH x.property⟩, x.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁))
    (⟨x, hH x.property⟩ : E.G₁) ⟨y, hH y.property⟩)

private theorem toLocalTilde_surjective (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) :
    Function.Surjective (E.toLocalTilde H₁ hH) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem toLocalTilde_map (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁)
    (A : Subgroup G) (ha : A ≤ H₁) :
    (A.subgroupOf H₁).map (E.toLocalTilde H₁ hH) = (E.tilde A).subgroupOf (E.tilde H₁) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hH x.property⟩, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, ha hx⟩, hx, Subtype.ext hxy⟩

/-- The image of O₂(H₁) is the actual two-core of the image of H₁ in G₁/V₁. -/
theorem tilde_core_eq (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) :
    E.tilde (H₁.pCoreIn 2) = (E.tilde H₁).pCoreIn 2 := by
  let f := E.toLocalTilde H₁ hH
  have hk : f.ker = E.V₁.subgroupOf H₁ := by
    ext x
    change E.toLocalTilde H₁ hH x = 1 ↔ x.val ∈ E.V₁
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (⟨x, hH x.property⟩ : E.G₁)
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (@IsElementaryAbelian.isPGroup 2 _ _
      (D.centralQuotientPreimage_elementary E.point)).comap_subtype
  have hpre := f.comap_pCore_of_ker_isPGroup (E.toLocalTilde_surjective H₁ hH) hkp
  have hm : (pCore 2 H₁).map f = pCore 2 (E.tilde H₁) := by
    rw [← hpre, map_comap_eq_self_of_surjective (E.toLocalTilde_surjective H₁ hH)]
  have hQ : (H₁.pCoreIn 2).subgroupOf H₁ = pCore 2 H₁ :=
    comap_map_eq_self_of_injective H₁.subtype_injective _
  rw [← hQ, E.toLocalTilde_map H₁ hH _ (pCoreIn_le 2 H₁)] at hm
  unfold pCoreIn
  rw [← hm]
  exact (map_subgroupOf_eq_of_le (map_mono (comap_mono (pCoreIn_le 2 H₁)))).symm

/-- The core and Frattini assertions of 11.5.5, also retaining the central
omega containment and relative normality used in 11.5.7. -/
theorem localClosure_core_and_frattini (hp : E.point ≠ ⊥)
    (h13 : E.V₁ ≤ E.V₃) (hne : E.V₁ ≠ E.V₃)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁) :
    E.localClosure H₁ ≤ H₁.pCoreIn 2 ∧
      E.tilde (E.localClosure H₁) ≤ omegaOneAmbient
        ((center (E.tilde (H₁.pCoreIn 2))).map (E.tilde (H₁.pCoreIn 2)).subtype) ∧
      (frattini (E.localClosure H₁)).map (E.localClosure H₁).subtype ≤ E.V₁ ∧
      (E.localClosure H₁ ≤ (T : Subgroup G) ∧
        ((E.localClosure H₁).subgroupOf (T : Subgroup G)).Normal) ∧
      ⁅E.localClosure H₁, H₁.pCoreIn 2⁆ ≤ E.V₁ := by
  have h := E.closureSetup_hypothesis hp h13 hne hT1 hlocal hirr H₁ hH hLH
  exact ⟨h.U_le_core, h.tilde_U_central.2, h.frattini_U_le_point,
    h.U_normal_in_T, h.commutator_U_core_le_point⟩

/-- The source's central quotient formulation uses O₂(H̃₁), not an
unidentified image of a different core. -/
theorem localClosure_central_quotient (hp : E.point ≠ ⊥)
    (h13 : E.V₁ ≤ E.V₃) (hne : E.V₁ ≠ E.V₃)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (H₁ : Subgroup G) (hH : H₁ ≤ E.G₁) (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁) :
    E.tilde (E.localClosure H₁) ≤
      (center ((E.tilde H₁).pCoreIn 2)).map ((E.tilde H₁).pCoreIn 2).subtype := by
  have h := (E.localClosure_core_and_frattini hp h13 hne hT1 hlocal hirr H₁ hH hLH).2.1
  rw [E.tilde_core_eq H₁ hH] at h
  exact h.trans (omegaOneAmbient_le _)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
