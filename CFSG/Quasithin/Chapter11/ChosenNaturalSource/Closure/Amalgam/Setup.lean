module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.ChapterF.Section07.Geometry
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The literal amalgam for the abelian chosen-natural closure

The vertex groups are LT and KT inside their generated subgroup. The overlap
is L₁T, using the preceding point-centralizer bound and K≤C_G(V₁). Uniqueness of the
maximal two-local over LT and escape of K from M kill the generated two-core.
The remaining F.7 inputs are transferred through the actual subgroup maps.

The closure used here is ⟨V^(KT)⟩. It is different from Geometry.U, which is
⟨V₃^G₁⟩. Abelianness of Geometry.W makes this new closure elementary abelian
and normal in KT, so the F.7 critical distance exceeds one.

LocalInputs contains explicit earlier inputs, not the conclusion K=L₁.
This module does not discharge those earlier inputs or the two parity cases.
Source: Aschbacher--Smith, 11.5.8, printed p.784, and F.7.1,6--11, pp.311--314.
Conjugation in Lean is x ↦ g*x*g⁻¹; source right-coset labels use g⁻¹.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterF.Section07
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

def LT (_E : Closure.Geometry D) : Subgroup G := L ⊔ (T : Subgroup G)
def KT : Subgroup G := E.K ⊔ (T : Subgroup G)
abbrev generated : Subgroup G := LT E ⊔ KT E
def localClosure : Subgroup G := conjugateSpanBy V (KT E)
abbrev family := ChapterF.Section07.Geometry.family (LT E) (KT E)

/-- Only earlier local inputs needed to construct the graph. The marked
quadratic geometry and exceptional K alternatives are additional inputs to
the parity arguments, not assertions of this record. -/
structure LocalInputs : Prop where
  point_invariant : (T : Subgroup G) ≤ E.G₁
  point_centralizer : LT E ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ (T : Subgroup G)
  K_centralizes : E.K ≤ centralizer (E.V₁ : Set G)
  unique : ∀ N : Subgroup G, IsMaximalTwoLocal N → LT E ≤ N → N = E.M
  characteristicTwo : generalizedFitting (LT E) = pCore 2 (LT E)
  reduced : IsPReduced 2 (V.subgroupOf (LT E))
  centralizer_eq : (T : Subgroup G).subgroupOf (LT E) ⊓
      centralizer (V.subgroupOf (LT E) : Set (LT E)) =
        (centralizer (V.subgroupOf (LT E) : Set (LT E))).pCoreIn 2

theorem V_le_LT : V ≤ LT E := D.le_sylow.trans le_sup_right
theorem V_le_KT : V ≤ KT E := D.le_sylow.trans le_sup_right

theorem KT_le_G₁ (h : LocalInputs E) : KT E ≤ E.G₁ :=
  sup_le E.K_le_G₁ h.point_invariant

open scoped Pointwise in
/-- The actual intersection, without replacing the solvable residual by O².
The full point normalizer is larger because it includes the odd Cartan. -/
theorem overlap (h : LocalInputs E) : LT E ⊓ KT E = E.L₁ ⊔ (T : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    have hxKT : x ∈ (E.K : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left E.K (T : Subgroup G)
        (h.point_invariant.trans E.G₁_normalizes_K)]
      exact hx.2
    obtain ⟨k, hk, t, ht, rfl⟩ := hxKT
    have hkLT : k ∈ LT E := by
      simpa only [mul_inv_cancel_right] using
        (LT E).mul_mem hx.1 ((LT E).inv_mem (mem_sup_right ht))
    exact (E.L₁ ⊔ (T : Subgroup G)).mul_mem
      (h.point_centralizer ⟨hkLT, h.K_centralizes hk⟩) (mem_sup_right ht)
  · exact le_inf (sup_le (E.L₁_le.trans le_sup_left) le_sup_right)
      (sup_le ((le_conjugateSpanBy E.L₁ E.G₁).trans le_sup_left) le_sup_right)

/-- Escape from the unique maximal two-local kills O₂ of the generated group. -/
theorem generated_core (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    pCore 2 (generated E) = ⊥ := by
  have hn : generated E ≤ normalizer ((generated E).pCoreIn 2 : Set G) :=
    (generated E).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hz : (generated E).pCoreIn 2 = ⊥ := by
    by_contra hne
    have hc := normalizer_le_of_unique_maximalTwoLocal h.unique
      (isPGroup_pCoreIn 2 (generated E)) hne (le_sup_left.trans hn)
    exact hout ((le_sup_left : E.K ≤ KT E).trans
      ((le_sup_right : KT E ≤ generated E).trans (hn.trans hc)))
  exact ((pCore 2 (generated E)).map_eq_bot_iff_of_injective
    (generated E).subtype_injective).mp hz

/-- The first vertex subgroup has the literal LT carrier. -/
def firstEquiv : LT E ≃* family E false :=
  (subgroupOfEquivOfLe (show LT E ≤ generated E from le_sup_left)).symm

theorem map_seed :
    (V.subgroupOf (LT E)).map (firstEquiv E).toMonoidHom =
      (V.subgroupOf (generated E)).subgroupOf (family E false) := by
  ext x
  rw [mem_map_equiv]
  rfl

/-- Every F.7.6 hypothesis on the actual generated ambient group. Escape is
still an explicit input, to be supplied from the strict component branch. -/
def sourceSetup (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    Track.SourceSetup (family E) := by
  let P₀ := T.subtype
    (show (T : Subgroup G) ≤ generated E from
      (le_sup_right : (T : Subgroup G) ≤ KT E).trans le_sup_right)
  have hPi (i : Bool) : (P₀ : Subgroup (generated E)) ≤ family E i := by
    cases i <;> exact fun x hx => mem_sup_right hx
  let S (i : Bool) := P₀.subtype (hPi i)
  let e := firstEquiv E
  have hV := h.reduced.map_equiv e
  rw [map_seed] at hV
  refine {
    finite := fun _ => inferInstance
    generates := ChapterF.Section07.Geometry.family_generates (LT E) (KT E)
    characteristicTwo := ?_
    core_free := ?_
    sylow := S
    same_sylow := ?_
    V := (V.subgroupOf (generated E)).subgroupOf (family E false)
    reduced := hV
    centralizer_eq := ?_ }
  · rw [← map_generalizedFitting_equiv e, h.characteristicTwo, pCore_map_iso]
  · let f : (family E false ⊔ family E true : Subgroup (generated E)) ≃*
        generated E := (MulEquiv.subgroupCongr
          (ChapterF.Section07.Geometry.family_generates (LT E) (KT E))).trans
            Subgroup.topEquiv
    apply (map_eq_bot_iff_of_injective _ (f := f.toMonoidHom) f.injective).mp
    rw [pCore_map_iso]
    exact generated_core E h hout
  · exact (map_subgroupOf_eq_of_le (hPi false)).trans
      (map_subgroupOf_eq_of_le (hPi true)).symm
  · rw [AmalgamLocalCores.reduced_centralizer_core _ hV]
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [Subgroup.map_inf _ _ _ e.symm.injective, pCore_map_iso]
    have hS : (S false : Subgroup (family E false)).map e.symm.toMonoidHom =
        (T : Subgroup G).subgroupOf (LT E) := by
      ext x
      rw [mem_map_equiv]
      rfl
    rw [hS, map_centralizer_equiv]
    have hVV : e.symm '' ((V.subgroupOf (generated E)).subgroupOf
        (family E false) : Set (family E false)) =
        (V.subgroupOf (LT E) : Set (LT E)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
    rw [hVV, ← AmalgamLocalCores.reduced_centralizer_core _ h.reduced]
    exact h.centralizer_eq

theorem sourceSeed_eq (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    (sourceSetup E h hout).seed = V.subgroupOf (generated E) := by
  exact map_subgroupOf_eq_of_le (comap_mono (V_le_LT E))

theorem sourceSeed_map (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    (sourceSetup E h hout).seed.map (generated E).subtype = V := by
  rw [sourceSeed_eq, map_subgroupOf_eq_of_le ((V_le_LT E).trans le_sup_left)]

theorem sourceV_ne_bot (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    (sourceSetup E h hout).V ≠ ⊥ := by
  intro hz
  have hs : (sourceSetup E h hout).seed = ⊥ := by
    rw [Track.SourceSetup.seed, hz, Subgroup.map_bot]
  apply D.ne_bot
  rw [← sourceSeed_map E h hout, hs, Subgroup.map_bot]

/-- 11.5.7 supplies elementary abelianness of the whole normalizer closure. -/
theorem W_elementary (hab : IsMulCommutative E.W) : IsElementaryAbelian 2 E.W := by
  let := D.elementary
  let _ : IsMulCommutative (conjugateSpanBy V E.G₁) := hab
  exact conjugateSpanBy_elementary_of_commutative V E.G₁

theorem localClosure_elementary (h : LocalInputs E) (hab : IsMulCommutative E.W) :
    IsElementaryAbelian 2 (localClosure E) := by
  let _ : IsMulCommutative E.W := hab
  let _ : IsElementaryAbelian 2 E.W := W_elementary E hab
  exact IsElementaryAbelian.of_le (show localClosure E ≤ E.W from
    conjugateSpanBy_mono le_rfl (KT_le_G₁ E h))

theorem localClosure_le_core (h : LocalInputs E) (hab : IsMulCommutative E.W) :
    localClosure E ≤ (KT E).pCoreIn 2 := by
  let := localClosure_elementary E h hab
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    (conjugateSpanBy_le_self (V_le_KT E)) (le_normalizer_conjugateSpanBy _ _)

/-- The F.7 module at the second base vertex is precisely ⟨V^(KT)⟩. -/
theorem secondModule_map (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    (CriticalPairs.vertexModule (family E) (sourceSetup E h hout).seed
      (Subgroup.CosetGeometry.RankTwo.base (family E) true)).map
        (generated E).subtype = localClosure E := by
  rw [CriticalPairs.second_base_module_eq_conjugate_join _ _
      (sourceSetup E h hout).seed_normalized,
    ← conjugateSpanBy_eq_iSup_conj, map_conjugateSpanBy, sourceSeed_map]
  rw [show (family E true).map (generated E).subtype = KT E from
    map_subgroupOf_eq_of_le le_sup_right]
  rfl

/-- The actual critical distance in 11.5.8, before the parity split. -/
def distance (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) : ℕ :=
  (sourceSetup E h hout).track (sourceV_ne_bot E h hout)

theorem one_lt_distance (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (hab : IsMulCommutative E.W) : 1 < distance E h hout := by
  apply CriticalPairs.Completion.one_lt_track_of_true_core (family E)
    (sourceSetup E h hout) (sourceV_ne_bot E h hout)
  apply (map_le_map_iff_of_injective (generated E).subtype_injective).mp
  rw [sourceSeed_map, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _
    (generated E).subtype_injective,
    show (family E true).map (generated E).subtype = KT E from
      map_subgroupOf_eq_of_le le_sup_right]
  exact (le_conjugateSpanBy _ _).trans (localClosure_le_core E h hab)

/-- The final elementary contradiction after an even pair has been aligned
with the original field line. The alignment itself is a separate obligation. -/
theorem aligned_conjugates_commute (hab : IsMulCommutative E.W)
    (g : G) (hg : g ∈ E.G₁) : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hV : V ≤ E.W := le_conjugateSpanBy _ _
  have hVg : V.map (MulAut.conj g).toMonoidHom ≤ E.W := by
    rintro x ⟨v, hv, rfl⟩
    exact subset_closure ⟨g, hg, v, hv, rfl⟩
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hV.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans
      (centralizer_le hVg)))

/-- Correct the conjugator on the right by an element of L. The premise
identifies an actual field line of Vᵍ with V₁; mere binary containment
V₁≤Vᵍ would not supply this premise. -/
theorem commutes_of_line_alignment (hab : IsMulCommutative E.W) (g : G)
    (halign : ∃ l ∈ L,
      (E.V₁.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom = E.V₁) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨l, hl, he⟩ := halign
  have hm (A : Subgroup G) : A.map (MulAut.conj (g * l)).toMonoidHom =
      (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mul_inv_rev, mul_assoc]
  have hn : g * l ∈ E.G₁ := mem_normalizer_iff_map_conj_eq.mpr ((hm E.V₁).trans he)
  have hv : V.map (MulAut.conj (g * l)).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom := by
    have hlV : V.map (MulAut.conj l).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (D.normalizes hl)
    rw [hm V, hlV]
  simpa only [hv] using aligned_conjugates_commute E hab (g * l) hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
