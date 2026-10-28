module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.ModuleMarking
public import Theory.GroupAction.SylowFixedElementaryDisplacement
public import Theory.GroupTheory.SylowLocalCore

/-!
# Moving seeds and the double commutator in 13.6.11

For the literal preimage of X* in G_v, restriction of the given Sylow T_v
produces a Sylow subgroup fixing z. Odd-orbit averaging then proves that
C_X([z,X]) fixes z. Two applications of the three-subgroup lemma show that
[ [z,X], L_v ] cannot vanish: otherwise X centralizes both v and [z,L_v],
and hence z. Containment of [z,X] in the literal U_X proves the second clause.

The reconstruction z ∈ ⟨v⟩[z,L_v] is deduced from the three singular conjugates
in the actual binary A₅ marking. Thus the marked application only takes the
earlier module and Sylow data, not the reconstruction or a nonvanishing premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the local setup
on printed p.926 and Lemma 13.6.11 on pp.928–929. These results do not use
B.5.6, the solvable exclusion, or a selected component.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open A5Module
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem starPreimage_normalizes_of_image (z v : G)
    (X : Subgroup (Gstar z v)) (H : Subgroup G) (hH : H ≤ Gv v)
    (hn : starImage z v H ≤ normalizer (X : Set _)) :
    H ≤ normalizer (starPreimage z v X : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg y hy
  obtain ⟨a, ha, rfl⟩ := hy
  let g' : Gv v := ⟨g, hH hg⟩
  have hg' : starMk z v g' ∈ normalizer (X : Set _) :=
    hn (mem_map.mpr ⟨g', hg, rfl⟩)
  refine mem_map.mpr ⟨g' * a * g'⁻¹, ?_, rfl⟩
  change starMk z v (g' * a * g'⁻¹) ∈ X
  simpa only [map_mul, map_inv] using
    (mem_normalizer_iff.mp hg' (starMk z v a)).mp ha

private theorem exists_sylow_fixing_seed (T : Subgroup G) (z v : G)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    (X : Subgroup G) (hX : X ≤ Gv v)
    (hn : Tv T v ≤ normalizer (X : Set G)) :
    ∃ P : Sylow 2 X, ∀ x : X, x ∈ P → (x : G) * z * (x : G)⁻¹ = z := by
  let N := Gv v ⊓ normalizer (X : Set G)
  have hXN : X ≤ N := le_inf hX X.le_normalizer
  have hSN : (S : Subgroup (Gv v)).map (Gv v).subtype ≤ N := by
    rw [hS]
    exact le_inf inf_le_right hn
  obtain ⟨Q, hQ⟩ := S.exists_map_subtype_eq_of_le (show N ≤ Gv v from inf_le_left) hSN
  obtain ⟨P, hP⟩ := Q.exists_map_subtype_eq_inf_of_normalizes hXN
    (show N ≤ normalizer (X : Set G) from inf_le_right)
  refine ⟨P, ?_⟩
  intro x hx
  have hm : (x : G) ∈ (P : Subgroup X).map X.subtype := mem_map.mpr ⟨x, hx, rfl⟩
  rw [hP, hQ, hS] at hm
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hfix hm.1))

private theorem centralizes_seed_of_centralizes_displacement
    (X W : Subgroup G) [IsElementaryAbelian 2 W] (z : G) (hz : z ∈ W)
    (hn : X ≤ normalizer (W : Set G))
    (P : Sylow 2 X) (hfix : ∀ x : X, x ∈ P → (x : G) * z * (x : G)⁻¹ = z) :
    X ⊓ centralizer ((⁅zpowers z, X⁆ : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨a, ha, _, he⟩ :=
    Theory.GroupAction.exists_conjugating_element_of_elementary_displacement X
      ⁅zpowers z, X⁆ W hn P ⟨z, hz⟩ hfix (fun x => by
        rw [commutator_comm]
        exact commutator_mem_commutator x.property (mem_zpowers z))
  intro x hx
  have hc : a * x = x * a := mem_centralizer_iff.mp hx.2 a ha
  have he' := he ⟨x, hx.1⟩
  have hzx : z * x * z⁻¹ = x := by
    rw [← he', hc, mul_inv_cancel_right]
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hzx).symm

/-- The three-subgroup and odd-orbit argument behind 13.6.11. -/
theorem seed_double_commutator_ne_bot
    (L T : Subgroup G) (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    (hseed : z ∈ zpowers v ⊔ ⁅zpowers z, Lv L v⁆)
    {X : Subgroup (Gstar z v)} (hX : X ∈ Xz L T z v) :
    ⁅⁅zpowers z, starPreimage z v X⁆, Lv L v⁆ ≠ ⊥ := by
  let A := starPreimage z v X
  let U := ⁅zpowers z, A⁆
  have hLA : Lv L v ≤ normalizer (A : Set G) :=
    starPreimage_normalizes_of_image z v X (Lv L v) (Lv_le_Gv L v)
      (le_sup_left.trans hX.1.1)
  have hTA : Tv T v ≤ normalizer (A : Set G) :=
    starPreimage_normalizes_of_image z v X (Tv T v) inf_le_right
      (le_sup_right.trans hX.1.1)
  obtain ⟨P, hP⟩ := exists_sylow_fixing_seed T z v S hS hfix A
    (starPreimage_le_Gv z v X) hTA
  have hcent := centralizes_seed_of_centralizes_displacement A (Uv z v) z
    (z_mem_Uv z v) ((starPreimage_le_Gv z v X).trans (Gv_normalizes_Uv z v)) P hP
  intro hzero
  change ⁅U, Lv L v⁆ = ⊥ at hzero
  have hAU : ⁅U, A⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right _ _)
  have hLAU : ⁅⁅A, Lv L v⁆, U⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm (Lv L v) U, hzero, commutator_bot_left]
    · exact eq_bot_iff.mpr ((commutator_mono hAU le_rfl).trans hzero.le)
  have hLAz : ⁅⁅A, Lv L v⁆, zpowers z⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have hc : ⁅A, Lv L v⁆ ≤ centralizer ({z} : Set G) :=
      (le_inf (le_normalizer_iff_commutator_le_left.mp hLA)
        (commutator_eq_bot_iff_le_centralizer.mp hLAU)).trans hcent
    simpa only [zpowers_eq_closure, centralizer_closure] using hc
  have hzLA : ⁅⁅zpowers z, Lv L v⁆, A⁆ = ⊥ := by
    rw [commutator_comm (zpowers z) (Lv L v)]
    exact commutator_commutator_eq_bot_of_rotate hzero hLAz
  have hspan : zpowers v ⊔ ⁅zpowers z, Lv L v⁆ ≤ centralizer (A : Set G) :=
    sup_le (zpowers_le.mpr (by
      apply mem_centralizer_iff.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp ((starPreimage_le_Gv z v X) hx)))
      (commutator_eq_bot_iff_le_centralizer.mp hzLA)
  have hzcent := hspan hseed
  apply hX.2
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzcent x hx)

/-- The second assertion of 13.6.11 uses the literal definition of U_X. -/
theorem UX_commutator_ne_bot
    (L T : Subgroup G) (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    (hseed : z ∈ zpowers v ⊔ ⁅zpowers z, Lv L v⁆)
    {X : Subgroup (Gstar z v)} (hX : X ∈ Xz L T z v) :
    ⁅UX L z v X, Lv L v⁆ ≠ ⊥ := by
  intro hzero
  apply seed_double_commutator_ne_bot L T z v S hS hfix hseed hX
  apply eq_bot_iff.mpr
  exact (commutator_mono (commutator_mono (le_conjugateSpanBy _ _) le_rfl) le_rfl).trans hzero.le

/-- The marked three-singular-vector product reconstructs z from v and [z,Lᵥ]. -/
theorem marked_seed_mem_line_sup_commutator
    {L V : Subgroup G} (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (markedZ s) (markedV s))] :
    markedZ s ∈ zpowers (markedV s) ⊔ ⁅zpowers (markedZ s), Lv L (markedV s)⁆ := by
  let z := markedZ s
  let v := markedV s
  let W := Uv z v
  let N := zpowers v ⊔ ⁅zpowers z, Lv L v⁆
  let q := QuotientGroup.mk' (N.subgroupOf W)
  let zW : W := ⟨z, z_mem_Uv z v⟩
  have hvW : v ∈ W := Vv_le_Uv L z v (markedV_mem_Vv s)
  let vW : W := ⟨v, hvW⟩
  have hvq : q vW = 1 := (QuotientGroup.eq_one_iff _).mpr
    (show v ∈ N from mem_sup_left (mem_zpowers v))
  have hconj (c : G) (hc : c ∈ Lv L v) : c * z * c⁻¹ ∈ W :=
    (mem_normalizer_iff.mp (Gv_normalizes_Uv z v (Lv_le_Gv L v hc)) z).mp zW.property
  have hqconj (c : G) (hc : c ∈ Lv L v) :
      q ⟨c * z * c⁻¹, hconj c hc⟩ = q zW := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change c * z * c⁻¹ / z ∈ N
    apply mem_sup_right
    rw [commutator_comm]
    simpa only [div_eq_mul_inv, commutatorElement_def] using
      (commutator_mem_commutator hc (mem_zpowers z))
  obtain ⟨c, hc, he⟩ := A5Module.exists_residual_triple s
  have heW : zW * (⟨c * z * c⁻¹, hconj c hc⟩ : W) *
      ⟨c ^ 2 * z * (c ^ 2)⁻¹, hconj (c ^ 2) ((Lv L v).pow_mem hc 2)⟩ = vW :=
    Subtype.ext he
  have heq := congrArg q heW
  rw [map_mul, map_mul, hqconj c hc, hqconj (c ^ 2) ((Lv L v).pow_mem hc 2), hvq] at heq
  have hz2 : (q zW) ^ 2 = 1 := by
    rw [← map_pow]
    exact congrArg q (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) zW)
  have hzq : q zW = 1 := by
    rw [← pow_two, hz2, one_mul] at heq
    exact heq
  exact (QuotientGroup.eq_one_iff (N := N.subgroupOf W) zW).mp hzq

/-- Both clauses of source 13.6.11, with the reconstruction premise discharged
by the actual A₅ marking and the supplied Sylow from the earlier local setup. -/
theorem marked_Xz_commutators_ne_bot
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (markedZ s) (markedV s))]
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype =
      Tv T (markedV s))
    (hfix : Tv T (markedV s) ≤ centralizer ({(markedZ s)} : Set G))
    {X : Subgroup (Gstar (markedZ s) (markedV s))}
    (hX : X ∈ Xz L T (markedZ s) (markedV s)) :
    ⁅⁅zpowers (markedZ s), starPreimage (markedZ s) (markedV s) X⁆,
      Lv L (markedV s)⁆ ≠ ⊥ ∧
      ⁅UX L (markedZ s) (markedV s) X, Lv L (markedV s)⁆ ≠ ⊥ := by
  have hseed := marked_seed_mem_line_sup_commutator s
  exact ⟨seed_double_commutator_ne_bot L T _ _ S hS hfix hseed hX,
    UX_commutator_ne_bot L T _ _ S hS hfix hseed hX⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
