module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
public import Theory.GroupTheory.PResidual.NormalizedGenerators
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Transporting the original natural flag through its action

The stabilizers below act on the actual elementary group, with its marked
subgroups. Their residuals are images of the literal source `F.Li`.
The action kernel normalizes these residuals; consequently generation in
the automorphism group lifts through the two-core. A Sylow supplement also
computes the intersection with the original point normalizer, independently
of any coordinate choice.

Source: Aschbacher--Smith, Notation 12.8.2 and 14.4.8(1), printed pp.849,1009.
The remaining finite natural-module calculations belong to `ElementaryEight`.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags

variable {E : Type*} [Group E]

/-- The setwise stabilizer of the marked subgroup in its full automorphism group. -/
def flagStabilizer (A : Subgroup E) : Subgroup (MulAut E) :=
  MulAction.stabilizer (MulAut E) A

/-- Its embedded two-residual, rather than the whole parabolic. -/
def flagResidual (A : Subgroup E) : Subgroup (MulAut E) :=
  twoResidual (flagStabilizer A)

/-- Displacements of the marked plane by the indicated automorphisms. -/
def flagMovement (B : Subgroup E) (R : Subgroup (MulAut E)) : Subgroup E :=
  closure {x | ∃ b ∈ B, ∃ a ∈ R, x = b * (a b)⁻¹}

variable {G : Type*} [Group G] [Finite G]
variable {L V : Subgroup G} {T : Sylow 2 G}

omit [Finite G] in
theorem stabilizer_preimage (d : NaturalThreeAction L V T)
    (A : Subgroup G) (hAV : A ≤ V) :
    (flagStabilizer (A.subgroupOf V)).comap (conjugation L V d.normalizes) =
      (normalizer (A : Set G)).subgroupOf L := by
  ext x
  change (A.subgroupOf V).map (conjugation L V d.normalizes x).toMonoidHom =
    A.subgroupOf V ↔ (x : G) ∈ normalizer (A : Set G)
  rw [← (map_injective V.subtype_injective).eq_iff]
  rw [map_map]
  have he : V.subtype.comp (conjugation L V d.normalizes x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp V.subtype := by
    ext v
    exact conjugation_apply L V d.normalizes x v
  rw [he, ← map_map, map_subgroupOf_eq_of_le hAV]
  exact mem_normalizer_iff_map_conj_eq.symm

omit [Finite G] in
theorem Li_eq_residual (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ) :
    F.Li L i = twoResidual (L ⊓ F.Gi i) := by
  simp [Chapter12.Section08.InvariantFlag.Li, twoResidual]

theorem Li_subgroupOf (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ) :
    (F.Li L i).subgroupOf L = twoResidual ((F.Gi i).subgroupOf L) := by
  apply map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L i).trans inf_le_left), twoResidual,
    map_embedded_pResidual, subgroupOf_map_subtype, inf_comm]
  exact Li_eq_residual F i

theorem Li_image (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ) :
    ((F.Li L i).subgroupOf L).map (conjugation L V d.normalizes) =
      flagResidual ((F.Vi i).subgroupOf V) := by
  rw [Li_subgroupOf, twoResidual, map_embedded_pResidual]
  rw [Chapter12.Section08.InvariantFlag.Gi,
    ← stabilizer_preimage d (F.Vi i) (F.le_seed i),
    map_comap_eq_self_of_surjective d.surjective]
  rfl

omit [Finite G] in
theorem Li_normalized (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ) :
    (T : Subgroup G) ≤ normalizer (F.Li L i : Set G) := by
  rw [Li_eq_residual]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ F.Gi i) (pResidual 2 (L ⊓ F.Gi i : Subgroup G)))
  exact (le_inf d.T_normalizes ((F.invariant i).trans (F.Gi i).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

theorem Li_residual (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ) :
    twoResidual (F.Li L i) = F.Li L i := by
  have hp : IsPPerfect 2 (F.Li L i) := by
    rw [Li_eq_residual]
    exact isPPerfect_embedded_pResidual 2 _
  simp only [twoResidual, (pResidual_eq_top_iff 2 _).mpr hp,
    ← MonoidHom.range_eq_map, range_subtype]

private theorem kernel_normalizes_Li (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ) :
    (conjugation L V d.normalizes).ker ≤
      normalizer ((F.Li L i).subgroupOf L : Set L) := by
  rw [Li_subgroupOf]
  apply le_trans _ (((F.Gi i).subgroupOf L).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _)))
  rw [Chapter12.Section08.InvariantFlag.Gi,
    ← stabilizer_preimage d (F.Vi i) (F.le_seed i)]
  exact ker_le_comap _ _

/-- Cubic core quotients lift through the actual two-group action kernel. -/
theorem Li_three (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (i : ℕ)
    (K : Subgroup G) (hK : L ⊓ F.Gi i ≤ K)
    (hc : Nat.card (coreQuotient (flagResidual ((F.Vi i).subgroupOf V))) = 3) :
    ThreeExtension K (T : Subgroup G) (F.Li L i) := by
  let R := (F.Li L i).subgroupOf L
  let f := conjugation L V d.normalizes
  have hk : IsPGroup 2 f.ker := by rw [d.kernel]; exact pCore_isPGroup
  have hkr : IsPGroup 2 (f.subgroupMap R).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap R)
    (f.subgroupMap_surjective R) hkr
  let j := subgroupOfEquivOfLe ((F.Li_le L i).trans inf_le_left)
  have hcard : Nat.card (coreQuotient (F.Li L i)) = 3 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).toEquiv,
      Nat.card_congr e.toEquiv]
    change Nat.card (coreQuotient (((F.Li L i).subgroupOf L).map f)) = 3
    rw [Li_image d F i]
    exact hc
  refine ⟨(F.Li_le L i).trans hK, Li_normalized d F i, Li_residual F i, ?_⟩
  have he := relIndex_map_map_of_injective (pCore 2 (F.Li L i)) ⊤
    (F.Li L i).subtype_injective
  simpa only [twoCore, ← MonoidHom.range_eq_map, range_subtype, relIndex_top_right,
    index_eq_card, hcard] using he

omit [Finite G] in
/-- The displacement construction is precisely the ambient group commutator. -/
theorem movement_map (d : NaturalThreeAction L V T)
    (B A : Subgroup G) (hBV : B ≤ V) (hAL : A ≤ L) :
    (flagMovement (B.subgroupOf V)
      ((A.subgroupOf L).map (conjugation L V d.normalizes))).map V.subtype = ⁅B, A⁆ := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro x ⟨b, hb, a, ha, rfl⟩
    obtain ⟨c, hc, rfl⟩ := ha
    change (b : G) * (conjugation L V d.normalizes c b : G)⁻¹ ∈ ⁅B, A⁆
    rw [conjugation_apply]
    have he : (b : G) * ((c : G) * (b : G) * (c : G)⁻¹)⁻¹ = ⁅(b : G), (c : G)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [he]
    exact commutator_mem_commutator hb hc
  · apply commutator_le.mpr
    intro b hb a ha
    let v : V := ⟨b, hBV hb⟩
    let l : L := ⟨a, hAL ha⟩
    refine ⟨v * (conjugation L V d.normalizes l v)⁻¹, ?_, ?_⟩
    · exact subset_closure ⟨v, hb, conjugation L V d.normalizes l,
        mem_map_of_mem _ ha, rfl⟩
    · change b * (conjugation L V d.normalizes l v : G)⁻¹ = ⁅b, a⁆
      rw [conjugation_apply]
      change b * (a * b * a⁻¹)⁻¹ = ⁅b, a⁆
      simp only [commutatorElement_def]
      group

theorem moved_eq_of_automorphisms (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3)
    (hm : flagMovement ((F.Vi 2).subgroupOf V)
      (flagResidual ((F.Vi 1).subgroupOf V)) = ⊤) :
    movedSpace (F.Vi 2) (F.Li L 1) = V := by
  have hh := movement_map d (F.Vi 2) (F.Li L 1) (F.le_seed 2)
    ((F.Li_le L 1).trans inf_le_left)
  rw [Li_image d F 1, hm, ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh.symm

theorem generated_of_image (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3)
    (hgen : flagResidual ((F.Vi 1).subgroupOf V) ⊔
      flagResidual ((F.Vi 2).subgroupOf V) = ⊤) :
    F.Li L 1 ⊔ F.Li L 2 = L := by
  let f := conjugation L V d.normalizes
  let A := (F.Li L 1).subgroupOf L
  let B := (F.Li L 2).subgroupOf L
  have hmap : (A ⊔ B).map f = ⊤ := by
    rw [Subgroup.map_sup, Li_image d F 1, Li_image d F 2]
    exact hgen
  have hcover : (A ⊔ B) ⊔ f.ker = ⊤ := by
    simpa only [comap_map_eq, comap_top] using congrArg (comap f) hmap
  have hp (i : ℕ) : IsPPerfect 2 ((F.Li L i).subgroupOf L) := by
    rw [Li_subgroupOf]
    exact isPPerfect_embedded_pResidual 2 _
  have hk : IsPGroup 2 f.ker := d.kernel ▸ pCore_isPGroup
  have hh := pResidual_eq_sup_of_normalized_generators A B f.ker
    (hp 1) (hp 2) hk (kernel_normalizes_Li d F 1) (kernel_normalizes_Li d F 2) hcover
  have htop : A ⊔ B = ⊤ := hh.symm.trans
    ((pResidual_eq_top_iff 2 L).mpr (isPPerfect_of_twoResidual_eq d.residual))
  have hm := congrArg (map L.subtype) htop
  simpa only [Subgroup.map_sup, A, B,
    map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
    map_subgroupOf_eq_of_le ((F.Li_le L 2).trans inf_le_left),
    ← MonoidHom.range_eq_map, range_subtype] using hm

private theorem normal_residual_sup_sylow (N : Subgroup G) [N.Normal] (T : Sylow 2 G) :
    twoResidual N ⊔ (T : Subgroup G) = N ⊔ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal N
  have hh := congrArg (map N.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, hS, subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, range_subtype] at hh
  apply le_antisymm (sup_le_sup (map_subtype_le _) le_rfl)
  apply sup_le _ le_sup_right
  exact hh.ge.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))

private theorem residual_sup_sylow (N : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (N : Set G)) :
    twoResidual N ⊔ (T : Subgroup G) = N ⊔ (T : Subgroup G) := by
  let K := N ⊔ (T : Subgroup G)
  let D := N.subgroupOf K
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le N.le_normalizer hn)
  have hNK : N ≤ K := le_sup_left
  have hTK : (T : Subgroup G) ≤ K := le_sup_right
  have hh := congrArg (map K.subtype) (normal_residual_sup_sylow D (T.subtype hTK))
  have hDN : D.map K.subtype = N := map_subgroupOf_eq_of_le hNK
  have hR : (twoResidual D).map K.subtype = twoResidual N := by
    change ((pResidual 2 D).map D.subtype).map K.subtype = _
    rw [map_embedded_pResidual, hDN]
    rfl
  simpa only [Subgroup.map_sup, hR, Sylow.coe_subtype, hDN,
    map_subgroupOf_eq_of_le hTK] using hh

/-- The literal flag intersection follows from normalization and Sylow supplementation. -/
theorem flag_intersection (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) :
    (L ⊔ (T : Subgroup G)) ⊓ F.H = F.Li L 1 ⊔ (T : Subgroup G) := by
  have hn : (T : Subgroup G) ≤ normalizer (L ⊓ F.H : Set G) :=
    (le_inf d.T_normalizes ((F.invariant 1).trans F.H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [Li_eq_residual, residual_sup_sylow _ T hn]
  apply le_antisymm
  · rintro x ⟨hx, hxH⟩
    obtain ⟨a, ha, t, ht, rfl⟩ :=
      (coe_mul_of_right_le_normalizer_left L (T : Subgroup G) d.T_normalizes ▸ hx)
    have haH : a ∈ F.H := by
      simpa only [mul_inv_cancel_right] using F.H.mul_mem hxH (F.H.inv_mem (F.invariant 1 ht))
    exact mul_mem_sup ⟨ha, haH⟩ ht
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right (F.invariant 1))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.NaturalFlags
