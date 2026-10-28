module
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.WeakClosure

/-!
# Symplectic root fixed spaces normalize the selected conjugate

The two standard long-root groups with upper-right diagonal entries (0,0)
and (1,1) have fixed hyperplanes whose sum is the whole natural four-space.
An equivariant group isomorphism transfers this spanning assertion to the
literal centralizers of their inverse images in an ambient actor A.

Each root has order four and index sixteen in the actual symmetric-matrix
plane radical over a field of order four. Thus every inverse image has
corank at most four in A. The bound r(G,V)>4 puts its ambient centralizer
in N_G(A), so the whole swapped natural module normalizes A.

The final application constructs A from W₀(T,V) inside the original R₂,
combines both normalizations, and retains its nontrivial action of rank at
least four. The marking of the swapped module and the literal R₂ action
remain explicit construction obligations. No triangle exclusion or rank
contradiction is asserted here.
Source: Aschbacher--Smith, 11.4.1(2), printed p.776, using 11.2.2(3,5).
-/

@[expose] public noncomputable section
open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
variable {F : Type*} [Field F]

private theorem fixed_root_zero (v : Vector F) (hv : v (.inr 0) = 0) :
    v ∈ TwoLocalCover.fixedSpace (RootSubgroup.group (F := F) 0) := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 0 g).mp hg
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootElement, rootMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, hv]

private theorem fixed_root_two (v : Vector F) (hv : v (.inr 1) = 0) :
    v ∈ TwoLocalCover.fixedSpace (RootSubgroup.group (F := F) 2) := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 2 g).mp hg
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootElement, rootMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, hv]

private theorem symplectic_root_fixed_sum (v : Vector F) :
    ∃ v₀ ∈ TwoLocalCover.fixedSpace (RootSubgroup.group (F := F) 0),
      ∃ v₂ ∈ TwoLocalCover.fixedSpace (RootSubgroup.group (F := F) 2), v₀ + v₂ = v := by
  classical
  let v₂ : Vector F := Pi.single (.inr 0) (v (.inr 0))
  refine ⟨v - v₂, fixed_root_zero _ ?_, v₂, fixed_root_two _ ?_, sub_add_cancel _ _⟩
  · simp [v₂]
  · simp [v₂]

variable {G : Type*} [Group G]

/-- The ambient preimage of A* intersect R*, under the same action map. -/
def rootPreimage (H A : Subgroup G) (α : H →* Sp F) (r : Fin 8) : Subgroup G :=
  (A.subgroupOf H ⊓ (RootSubgroup.group r).comap α).map H.subtype

/-- The root preimage is a subgroup of the original actor A. -/
theorem rootPreimage_le (H A : Subgroup G) (α : H →* Sp F) (r : Fin 8) :
    rootPreimage H A α r ≤ A := by
  rintro _ ⟨a, ha, rfl⟩
  exact ha.1

/-- A fixed model vector lifts to the actual centralizer of the root preimage. -/
theorem fixed_mem_rootPreimage_centralizer
    (H A U : Subgroup G) (α : H →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hHU : H ≤ normalizer (U : Set G))
    (hact : ∀ (a : H) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hHU a.property) u.val).mp u.property⟩).toAdd =
        α a • (e u).toAdd)
    (r : Fin 8) (u : U)
    (hu : (e u).toAdd ∈ TwoLocalCover.fixedSpace (RootSubgroup.group r)) :
    (u : G) ∈ centralizer (rootPreimage H A α r : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  have he := (hact a u).trans (hu (α a) ha.2)
  have hc := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective he))
  exact mul_inv_eq_iff_eq_mul.mp hc

/-- Two literal root-preimage centralizers generate the whole swapped module. -/
theorem rootPreimage_centralizers_span
    (H A U : Subgroup G) (α : H →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hHU : H ≤ normalizer (U : Set G))
    (hact : ∀ (a : H) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hHU a.property) u.val).mp u.property⟩).toAdd =
        α a • (e u).toAdd) :
    (U ⊓ centralizer (rootPreimage H A α 0 : Set G)) ⊔
      (U ⊓ centralizer (rootPreimage H A α 2 : Set G)) = U := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro u hu
  obtain ⟨v₀, hv₀, v₂, hv₂, hv⟩ := symplectic_root_fixed_sum (e ⟨u, hu⟩).toAdd
  let u₀ := e.symm (Multiplicative.ofAdd v₀)
  let u₂ := e.symm (Multiplicative.ofAdd v₂)
  have hm₀ : (u₀ : G) ∈ U ⊓ centralizer (rootPreimage H A α 0 : Set G) := by
    refine ⟨u₀.property, fixed_mem_rootPreimage_centralizer H A U α e hHU hact 0 u₀ ?_⟩
    simpa only [u₀, e.apply_symm_apply, toAdd_ofAdd] using hv₀
  have hm₂ : (u₂ : G) ∈ U ⊓ centralizer (rootPreimage H A α 2 : Set G) := by
    refine ⟨u₂.property, fixed_mem_rootPreimage_centralizer H A U α e hHU hact 2 u₂ ?_⟩
    simpa only [u₂, e.apply_symm_apply, toAdd_ofAdd] using hv₂
  have hprod : u₀ * u₂ = ⟨u, hu⟩ := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    simpa only [map_mul, toAdd_mul, u₀, u₂,
      e.apply_symm_apply, toAdd_ofAdd] using hv
  have hm := ( (U ⊓ centralizer (rootPreimage H A α 0 : Set G)) ⊔
      (U ⊓ centralizer (rootPreimage H A α 2 : Set G))).mul_mem
    (mem_sup_left hm₀) (mem_sup_right hm₂)
  change ((u₀ * u₂ : U) : G) ∈ _ at hm
  simpa only [hprod] using hm

private theorem root_le_plane_radical (r : Fin 8) (hr : r = 0 ∨ r = 2) :
    RootSubgroup.group (F := F) r ≤ Plane.radical.map planeLocal.subtype := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r g).mp hg
  have hs (i : Fin 2) : (Matrix.single i i t).IsSymm := by
    change (Matrix.single i i t)ᵀ = _
    rw [Matrix.transpose_single]
  rcases hr with rfl | rfl
  · exact mem_map.mpr ⟨Plane.shear ⟨Matrix.single 0 0 t, hs 0⟩,
      Plane.quotientMap_shear _, rfl⟩
  · exact mem_map.mpr ⟨Plane.shear ⟨Matrix.single 1 1 t, hs 1⟩,
      Plane.quotientMap_shear _, rfl⟩

private theorem root_relIndex_four [Finite F] (hF : Nat.card F = 4)
    (r : Fin 8) (hr : r = 0 ∨ r = 2) :
    (RootSubgroup.group (F := F) r).relIndex (Plane.radical.map planeLocal.subtype) = 16 := by
  let R := RootSubgroup.group (F := F) r
  let P := Plane.radical.map (planeLocal (F := F)).subtype
  have hRP : R ≤ P := root_le_plane_radical r hr
  have hcard := (R.subgroupOf P).card_mul_index
  have hcR : Nat.card (R.subgroupOf P) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv).trans ((RootSubgroup.card r).trans hF)
  have hcP : Nat.card P = 64 := by
    rw [Subgroup.card_map_of_injective planeLocal.subtype_injective,
      EvenTwoRank.card_plane_radical, hF]
    norm_num
  rw [hcR, hcP] at hcard
  change 4 * R.relIndex P = 64 at hcard
  change R.relIndex P = 16
  omega

/-- The root-preimage index is at most sixteen, even when the actor is only binary-linear. -/
theorem rootPreimage_relIndex_le [Finite F] (hF : Nat.card F = 4)
    (H A : Subgroup G) (hAH : A ≤ H) (α : H →* Sp F)
    (himage : (A.subgroupOf H).map α ≤ Plane.radical.map planeLocal.subtype)
    (r : Fin 8) (hr : r = 0 ∨ r = 2) :
    (rootPreimage H A α r).relIndex A ≤ 16 := by
  have hle : (RootSubgroup.group (F := F) r).relIndex ((A.subgroupOf H).map α) ≤ 16 := by
    have hi := root_relIndex_four hF r hr
    exact (Subgroup.relIndex_le_of_le_right himage (by rw [hi]; decide)).trans_eq hi
  have he : (rootPreimage H A α r).relIndex A =
      (RootSubgroup.group (F := F) r).relIndex ((A.subgroupOf H).map α) := by
    change ((A.subgroupOf H ⊓ (RootSubgroup.group r).comap α).map H.subtype).relIndex A = _
    conv_lhs => arg 2; rw [← map_subgroupOf_eq_of_le hAH]
    rw [relIndex_map_map_of_injective _ _ H.subtype_injective,
      inf_relIndex_left, relIndex_comap]
  exact he.trans_le hle

/-- Root fixed-space spanning and the original r bound give normalization of Vᵍ. -/
theorem natural_module_normalizes_conjugate [Finite F]
    (hF : Nat.card F = 4) (V H U : Subgroup G) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (α : H →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hHU : H ≤ normalizer (U : Set G))
    (hact : ∀ (a : H) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hHU a.property) u.val).mp u.property⟩).toAdd =
        α a • (e u).toAdd)
    (himage : ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map α ≤
      Plane.radical.map planeLocal.subtype)
    (hr : (4 : ℕ∞) < ChapterE.globalR V) :
    U ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  have hn (r : Fin 8) (hr' : r = 0 ∨ r = 2) :
      centralizer (rootPreimage H A α r : Set G) ≤ normalizer (A : Set G) := by
    apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR
      (rootPreimage_le H A α r)
    have hc : ChapterE.subgroupCorank A (rootPreimage H A α r) ≤ 4 := by
      exact (Nat.log_mono_right (rootPreimage_relIndex_le hF H A hg α himage r hr')).trans
        (by decide : Nat.log 2 16 ≤ 4)
    have hc' : (ChapterE.subgroupCorank A (rootPreimage H A α r) : ℕ∞) ≤ 4 := by
      exact_mod_cast hc
    exact hc'.trans_lt (by simpa only [A, ChapterE.globalR_map_equiv] using hr)
  rw [← rootPreimage_centralizers_span H A U α e hHU hact]
  exact sup_le (inf_le_right.trans (hn 0 (Or.inl rfl)))
    (inf_le_right.trans (hn 2 (Or.inr rfl)))

open CFSG.Quasithin Chapter11.ChosenNaturalSource ChapterE
variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- The actual flag application constructs a mutually normalizing conjugate with action rank at least four. -/
theorem ofFlag_exists_mutually_normalizing_conjugate [Finite F]
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (hF : Nat.card F = 4) (I U : Subgroup G)
    (hout : ¬ I ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G))
    (hC : (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2)
    (hU : IsPGroup 2 U) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ (ofFlag S f X z H₀).R₂)
    (hs : (4 : ℕ∞) ≤ @globalS G _ V D.elementary)
    (hr : (4 : ℕ∞) < globalR V)
    (α : (ofFlag S f X z H₀).R₂ →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hact : ∀ (a : (ofFlag S f X z H₀).R₂) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hTU (LocalGeometry.localRadical_le_sylow _ a.property))
          u.val).mp u.property⟩).toAdd = α a • (e u).toAdd)
    (himage : α.range ≤ Plane.radical.map planeLocal.subtype) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (ofFlag S f X z H₀).R₂ ∧
      V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (U : Set G) ∧
      U ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
      inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ ∧
      4 ≤ Representation.BinaryOffender.rank
        (inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom)) := by
  obtain ⟨g, hgR, hgT, hne, hrank⟩ :=
    flag_exists_large_conjugate_action D S f I U hout hN hC hU hTU hW hs
  refine ⟨g, hgR, hgT, hgT.trans hTU, ?_, hne, hrank⟩
  apply natural_module_normalizes_conjugate hF V ((ofFlag S f X z H₀).R₂) U g hgR α e
    ((LocalGeometry.localRadical_le_sylow _).trans hTU) hact _ hr
  exact (Subgroup.map_le_range α _).trans himage

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
