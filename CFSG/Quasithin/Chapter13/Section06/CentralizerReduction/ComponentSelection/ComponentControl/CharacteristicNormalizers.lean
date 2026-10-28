module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Characteristic
public import Theory.GroupTheory.CComponent.SolvableSupplement

/-!
# The radical supplement in the characteristic-normalizer argument

Let S = C_T(v) and D be the ambient image of a nontrivial characteristic
subgroup of S. If R N_K(D) = K, where R is the solvable radical of K, take
the residual of N_K(D) S. The solvable-kernel component correspondence proves
that this residual is a C-component, and its image K₁ lies in N_K(D).
It is S-invariant, belongs to the genuine local family, and R K₁ = K.
The normal subgroup D supplies the nontrivial two-core required by that family.

The movement of z under this replacement is a separate obligation. The final
deduction here proves strictness when R centralizes z, and records precisely
the residual obstruction otherwise. It does not assert the full 13.6.16(2).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 13.6.16(2),
printed p.930. The generic supplement facts use A.3.3(3–4), pp.42–43.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The join in the source conclusion is the product R N_K(C). Normality
is inside K; no normality of the radical in G is asserted. -/
theorem radical_normalizer_join_coe (K S : Subgroup G) (C : Subgroup S) :
    (((solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map S.subtype : Set G)) : Subgroup G) : Set G) =
    ((solvableRadical K).map K.subtype : Set G) *
      (K ⊓ normalizer (C.map S.subtype : Set G) : Set G) := by
  apply coe_mul_of_right_le_normalizer_left
  exact inf_le_left.trans (K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (solvableRadical K)))

/-- The actual local replacement: the residual of N_K(C)S, mapped to G. -/
def characteristicNormalizerReplacement (K S : Subgroup G) (C : Subgroup S) : Subgroup G :=
  let M := (K ⊓ normalizer (C.map S.subtype : Set G)) ⊔ S
  (solvableResidual M).map M.subtype

private theorem normalizer_replacement_le (K S : Subgroup G) (C : Subgroup S)
    [C.Characteristic] (hK : K ∈ Chapter1.L G S)
    (hS : S ≤ normalizer (K : Set G)) :
    characteristicNormalizerReplacement K S C ≤ K ⊓ normalizer (C.map S.subtype : Set G) := by
  let D := C.map S.subtype
  let M := (K ⊓ normalizer (D : Set G)) ⊔ S
  have hSD : S ≤ normalizer (D : Set G) :=
    S.le_normalizer.trans (normalizer_le_normalizer_characteristic_image S C)
  have hMH : M ≤ K ⊔ S := sup_le_sup inf_le_left le_rfl
  let := Chapter1.mem_L_isPerfect hK
  let : Group.IsNilpotent S := (Chapter1.isSylowIn_iff.mp hK.2.1).1.isNilpotent
  have hres := map_residual_sup_eq_of_perfect_of_solvable K S hS
  exact le_inf ((map_solvableResidual_mono hMH).trans hres.le)
    ((map_subtype_le (solvableResidual M)).trans (sup_le inf_le_right hSD))

/-- Failure of strictness constructs the supplement, its invariance and its
genuine local-family membership. No moving condition is inferred from coverage. -/
theorem characteristicNormalizerReplacement_spec
    (S K : Subgroup G) (hK : K ∈ Chapter1.L G S)
    (hS : S ≤ normalizer (K : Set G))
    (C : Subgroup S) [C.Characteristic] (hC : C ≠ ⊥)
    (hgen : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map S.subtype : Set G)) = K) :
    characteristicNormalizerReplacement K S C ≤ K ⊓ normalizer (C.map S.subtype : Set G) ∧
    S ≤ normalizer (characteristicNormalizerReplacement K S C : Set G) ∧
    characteristicNormalizerReplacement K S C ∈ Chapter1.L G S ∧
    (solvableRadical K).map K.subtype ⊔ characteristicNormalizerReplacement K S C = K := by
  let R := (solvableRadical K).map K.subtype
  let D := C.map S.subtype
  let N := K ⊓ normalizer (D : Set G)
  let H := K ⊔ S
  let M := N ⊔ S
  let K₁ := characteristicNormalizerReplacement K S C
  have hK₁N : K₁ ≤ N := normalizer_replacement_le K S C hK hS
  have hSD : S ≤ normalizer (D : Set G) :=
    S.le_normalizer.trans (normalizer_le_normalizer_characteristic_image S C)
  have hMK₁ : M ≤ normalizer (K₁ : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (solvableResidual M))
  have hSK₁ : S ≤ normalizer (K₁ : Set G) := le_sup_right.trans hMK₁
  have hMH : M ≤ H := sup_le_sup inf_le_left le_rfl
  have hRM : R ⊔ M = H := by
    change R ⊔ (N ⊔ S) = K ⊔ S
    rw [← sup_assoc, hgen]
  have hRH : R ≤ H := (map_subtype_le _).trans le_sup_left
  have hHR : H ≤ normalizer (R : Set G) :=
    (sup_le K.le_normalizer hS).trans
      (normalizer_le_normalizer_characteristic_image K (solvableRadical K))
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (f := K.subtype.subgroupMap (solvableRadical K))
    (K.subtype.subgroupMap_surjective _)
  let := Chapter1.mem_L_isPerfect hK
  let : Group.IsNilpotent S := (Chapter1.isSylowIn_iff.mp hK.2.1).1.isNilpotent
  have hres : (solvableResidual H).map H.subtype = K :=
    map_residual_sup_eq_of_perfect_of_solvable K S hS
  have hres' : solvableResidual H = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hres, map_subgroupOf_eq_of_le le_sup_left]
  have hHcomp : (solvableResidual H).IsCComponent := hres'.symm ▸ hK.1
  have hMcomp : (solvableResidual M).IsCComponent :=
    residual_isCComponent_of_solvable_supplement_in H R M hRH hMH hHR hRM hHcomp
  have hK₁M : K₁ ≤ M := map_subtype_le _
  have hK₁comp : (K₁.subgroupOf M).IsCComponent := by
    have he : K₁.subgroupOf M = solvableResidual M :=
      comap_map_eq_self_of_injective M.subtype_injective _
    exact he.symm ▸ hMcomp
  have hJM : K₁ ⊔ S ≤ M := sup_le hK₁M le_sup_right
  have hJH : K₁ ⊔ S ≤ H := hJM.trans hMH
  have hDcore : D ≤ (K₁ ⊔ S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((Chapter1.isSylowIn_iff.mp hK.2.1).1.to_le (map_subtype_le C))
      ((map_subtype_le C).trans le_sup_right)
      (sup_le (hK₁N.trans inf_le_right) hSD)
  have hlocal : K₁ ∈ Chapter1.L G S := by
    refine ⟨hK₁comp.subgroupOf_of_le le_sup_left hJM,
      hK.2.1.restrict le_sup_right hJH, ?_⟩
    intro he
    exact hC ((map_eq_bot_iff_of_injective C S.subtype_injective).mp
      (bot_unique (he ▸ hDcore)))
  refine ⟨hK₁N, hSK₁, hlocal, le_antisymm
    (sup_le (map_subtype_le _) (hK₁N.trans inf_le_left)) ?_⟩
  exact hres.symm.le.trans
    (map_solvableResidual_le_sup_residual_of_sup_eq H R M hRH hMH hHR hRM)

/-- The replacement is inside the literal centralizer G_v; the local-family
and invariance clauses use C_T(v), with its original ambient inclusion. -/
theorem characteristicNormalizerReplacement_local
    (T : Sylow 2 G) (v : G) (K : Subgroup G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic] (hC : C ≠ ⊥)
    (hgen : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) = K) :
    characteristicNormalizerReplacement K (Tv (T : Subgroup G) v) C ∈
      Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v) ∧
    Tv (T : Subgroup G) v ≤
      normalizer (characteristicNormalizerReplacement K (Tv (T : Subgroup G) v) C : Set G) := by
  obtain ⟨hle, hn, hlocal, _⟩ := characteristicNormalizerReplacement_spec _ K hK.2 hS C hC hgen
  exact ⟨⟨(hle.trans inf_le_left).trans hK.1, hlocal⟩, hn⟩

/-- Adjoining S before taking the residual does not change the replacement:
it is exactly N_K(C)^∞, with the intrinsic residual mapped into G. -/
theorem characteristicNormalizerReplacement_eq_normalizer_residual
    (S K : Subgroup G) (hK : K ∈ Chapter1.L G S)
    (hS : S ≤ normalizer (K : Set G)) (C : Subgroup S) [C.Characteristic] :
    characteristicNormalizerReplacement K S C =
      (solvableResidual (K ⊓ normalizer (C.map S.subtype : Set G) : Subgroup G)).map
        (K ⊓ normalizer (C.map S.subtype : Set G)).subtype := by
  let N := K ⊓ normalizer (C.map S.subtype : Set G)
  let M := N ⊔ S
  let : Group.IsPerfect (characteristicNormalizerReplacement K S C) :=
    Group.IsPerfect.map M.subtype
  exact le_antisymm
    (le_map_solvableResidual_of_isPerfect _ N (normalizer_replacement_le K S C hK hS))
    (map_solvableResidual_mono (show N ≤ M from le_sup_left))

/-- The actual logical obstruction: if the replacement fixes z while K
moves it, the solvable radical must move z. -/
theorem radical_moves_of_replacement_centralizes
    (S K : Subgroup G) (hK : K ∈ Chapter1.L G S)
    (hS : S ≤ normalizer (K : Set G)) (z : G)
    (hmoving : ¬ K ≤ centralizer ({z} : Set G))
    (C : Subgroup S) [C.Characteristic] (hC : C ≠ ⊥)
    (hgen : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map S.subtype : Set G)) = K)
    (hfixed : characteristicNormalizerReplacement K S C ≤ centralizer ({z} : Set G)) :
    ¬ (solvableRadical K).map K.subtype ≤ centralizer ({z} : Set G) := by
  intro hrad
  have he := (characteristicNormalizerReplacement_spec S K hK hS C hC hgen).2.2.2
  exact hmoving (he ▸ sup_le hrad hfixed)

omit [Finite G] in
/-- The radical-action obligation is discharged when the intrinsic radical
is a two-group: its ambient image is normal in K S and hence lies in S ≤ T. -/
theorem radical_centralizes_seed_of_isTwoGroup
    (T : Sylow 2 G) (z v : G)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hR : IsPGroup 2 (solvableRadical K)) :
    (solvableRadical K).map K.subtype ≤ centralizer ({z} : Set G) := by
  let H := K ⊔ Tv (T : Subgroup G) v
  let R := (solvableRadical K).map K.subtype
  have hRH : R ≤ H := (map_subtype_le _).trans le_sup_left
  have hHR : H ≤ normalizer (R : Set G) :=
    (sup_le K.le_normalizer hS).trans
      (normalizer_le_normalizer_characteristic_image K (solvableRadical K))
  have hRc : R ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes (hR.map _) hRH hHR
  obtain ⟨P, hP⟩ := hK.2.2.1
  have hRS : R ≤ Tv (T : Subgroup G) v :=
    hRc.trans ((pCoreIn_le_sylow H P).trans_eq hP)
  intro r hr
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 r (hRS hr).1)

/-- Strict characteristic-normalizer control when the radical fixes the
seed. This is a sufficient conditional result, not the full source theorem:
the source setup must still supply the radical-action step or another proof
that the constructed replacement moves z. -/
theorem radical_normalizer_lt_of_radical_centralizes
    (T : Sylow 2 G) (z v : G)
    (_hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (_hvT : v ∈ T) (_hv : v ≠ 1)
    (_hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hcore : ∀ K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({z} : Set G) → (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hmoving : ¬ K ≤ centralizer ({z} : Set G))
    (hrad : (solvableRadical K).map K.subtype ≤ centralizer ({z} : Set G))
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic] (hC : C ≠ ⊥) :
    (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) < K := by
  apply lt_of_le_of_ne (sup_le (map_subtype_le _) inf_le_left)
  intro he
  let K₁ := characteristicNormalizerReplacement K (Tv (T : Subgroup G) v) C
  obtain ⟨hle, _, _, _⟩ := characteristicNormalizerReplacement_spec _ K hK.2 hS C hC he
  obtain ⟨hloc, hn⟩ := characteristicNormalizerReplacement_local T v K hK hS C hC he
  have hm : ¬ K₁ ≤ centralizer ({z} : Set G) := by
    intro hc
    exact radical_moves_of_replacement_centralizes _ K hK.2 hS z hmoving C hC he hc hrad
  exact not_normalizes_characteristic_of_twoCore_eq_bot T v K₁ hidx C hC
    (hcore K₁ hloc hn hm) (hle.trans inf_le_right)

/-- Assertion (2) in the two-group radical case, using only the universal
first assertion in addition to the displayed local setup. -/
theorem radical_normalizer_lt_of_isTwoGroup
    (T : Sylow 2 G) (z v : G)
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hcore : ∀ K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({z} : Set G) → (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hmoving : ¬ K ≤ centralizer ({z} : Set G))
    (hR : IsPGroup 2 (solvableRadical K))
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic] (hC : C ≠ ⊥) :
    (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) < K :=
  radical_normalizer_lt_of_radical_centralizes T z v hz hvT hv hSylow hidx hcore
    K hK hS hmoving (radical_centralizes_seed_of_isTwoGroup T z v hz K hK hS hR) C hC

/-- Under assertion (1), failure of strictness produces a local, invariant
replacement which fixes z, although the original radical moves z. This is
the precise remaining branch, retaining the actual constructed subgroup. -/
theorem nonstrict_characteristicNormalizer_obstruction
    (T : Sylow 2 G) (z v : G)
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hcore : ∀ K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (K : Set G) →
      ¬ K ≤ centralizer ({z} : Set G) → (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥)
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hmoving : ¬ K ≤ centralizer ({z} : Set G))
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic] (hC : C ≠ ⊥)
    (hnlt : ¬ (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) < K) :
    let K₁ := characteristicNormalizerReplacement K (Tv (T : Subgroup G) v) C
    K₁ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v) ∧
    Tv (T : Subgroup G) v ≤ normalizer (K₁ : Set G) ∧
    K₁ ≤ K ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G) ∧
    (solvableRadical K).map K.subtype ⊔ K₁ = K ∧
    K₁ ≤ centralizer ({z} : Set G) ∧
    ¬ (solvableRadical K).map K.subtype ≤ centralizer ({z} : Set G) := by
  have he : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)) = K :=
    eq_of_le_of_not_lt (sup_le (map_subtype_le _) inf_le_left) hnlt
  obtain ⟨hle, _, _, hgen⟩ := characteristicNormalizerReplacement_spec _ K hK.2 hS C hC he
  obtain ⟨hloc, hn⟩ := characteristicNormalizerReplacement_local T v K hK hS C hC he
  have hc : characteristicNormalizerReplacement K (Tv (T : Subgroup G) v) C ≤
      centralizer ({z} : Set G) := by
    by_contra hm
    exact not_normalizes_characteristic_of_twoCore_eq_bot T v _ hidx C hC
      (hcore _ hloc hn hm) (hle.trans inf_le_right)
  exact ⟨hloc, hn, hle, hgen, hc,
    radical_moves_of_replacement_centralizes _ K hK.2 hS z hmoving C hC he hc⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
