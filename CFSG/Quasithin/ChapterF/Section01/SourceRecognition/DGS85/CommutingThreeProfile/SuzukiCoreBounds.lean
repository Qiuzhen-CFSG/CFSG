module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommonSylowIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NormalCoreProduct
public import Theory.SpecificGroups.Suzuki.SylowCommutator
public import Theory.SpecificGroups.Suzuki.SylowIntersections

/-!
# The Suzuki bound on the unproved middle-core quotient

Let m be the linear middle vertex and x,y its Suzuki neighbors. The first
index in DGS 12.3(a) identifies the image of V_x modulo Q_y with the center
of the actual Suzuki Sylow covered by Q_m. That center is the derived
subgroup of the Sylow. Lifting gives

  [Q_m,Q_m] ≤ V_x (Q_m ∩ Q_y) ≤ (Q_x ∩ Q_m)(Q_y ∩ Q_m).

The common-Sylow index is q² and the image of V_x has order q. Thus the
first product has index q in Q_m, and the second product has index dividing
q. These are proved bounds on the remaining product defect, not an assertion
that the defect vanishes. SuzukiCoreQuotient applies them to the literal
central quotient at m and its original parabolic image.

Source: DGS85, Groups and Graphs, (12.1)(c), (12.3)(a), printed pp.178--180.
The earlier critical pair and common Sylow remain explicit. All quotient
images use originalQuotient; no unmarked Sylow or binary Sz(2) row is used.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
variable {G : Type*} [Group G]

private theorem derived_le_seed_sup_kernel
    {M : Type*} [Group M] (A Q Y W : Subgroup G)
    (q : A →* M) (hQ : Q ≤ A) (hWQ : W ≤ Q)
    (hk : q.ker = Y.subgroupOf A)
    (himage : ⁅(Q.subgroupOf A).map q, (Q.subgroupOf A).map q⁆ ≤
      (W.subgroupOf A).map q) :
    ⁅Q,Q⁆ ≤ W ⊔ (Q ⊓ Y) := by
  have hQQ : ⁅Q,Q⁆ = (⁅Q.subgroupOf A,Q.subgroupOf A⁆).map A.subtype := by
    rw [map_commutator, map_subgroupOf_eq_of_le hQ]
  rw [hQQ]
  rintro _ ⟨a, ha, rfl⟩
  change (a : G) ∈ W ⊔ (Q ⊓ Y)
  have hqa : q a ∈ (W.subgroupOf A).map q := by
    apply himage
    rw [← map_commutator]
    exact mem_map_of_mem q ha
  obtain ⟨v, hv, he⟩ := hqa
  have hAQ : (a : G) ∈ Q := by
    have := commutator_le_self (Q.subgroupOf A) ha
    exact this
  have hvQ : (v : G) ∈ Q := hWQ hv
  have hker : a * v⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  have hY : ((a : G) * (v : G)⁻¹) ∈ Y := by
    change a * v⁻¹ ∈ Y.subgroupOf A
    rwa [← hk]
  have hN := (W ⊔ (Q ⊓ Y)).mul_mem
    ((show Q ⊓ Y ≤ W ⊔ (Q ⊓ Y) from le_sup_right) (show (a : G) * (v : G)⁻¹ ∈ Q ⊓ Y from
      ⟨Q.mul_mem hAQ (Q.inv_mem hvQ), hY⟩)) ((show W ≤ W ⊔ (Q ⊓ Y) from le_sup_left) hv)
  change (a : G) * (v : G)⁻¹ * (v : G) ∈ W ⊔ (Q ⊓ Y) at hN
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hN

namespace ReducedLayer
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The first Suzuki index places the full derived middle core in the proposed product. -/
theorem source_suzuki_middle_core_bounds
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let m := base F (!i)
    let y := base F i
    ⁅Q F m,Q F m⁆ ≤ V F x 1 ⊔ (Q F m ⊓ Q F y) ∧
      ⁅Q F m,Q F m⁆ ≤ (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) ∧
      (V F x 1 ⊔ (Q F m ⊓ Q F y)).relIndex (Q F m) = 2 ^ (2 * n + 1) ∧
      ((Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)).relIndex (Q F m) ∣ 2 ^ (2 * n + 1) := by
  let F := reducedFamily L S
  let A := star L S i
  let m := base F (!i)
  let y := base F i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hVx := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hVm := V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxm
  have hQA : Q F m ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  let q := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  obtain ⟨T, hT, hiCore, _⟩ := source_common_sylow_core_index h i eSuz R hR
  obtain ⟨hiV, _, U, hU⟩ := source_suzuki_first_index h i hb hc hxa hxm hadj hn eSuz eLin R hR
  have hUT : omegaOneAmbient (U : Subgroup (SuzukiMatrixGroup n)) ≤ T := by
    rw [← hU, ← hT]
    exact map_mono (subgroupOf_mono A hVm)
  have hne : omegaOneAmbient (U : Subgroup (SuzukiMatrixGroup n)) ≠ ⊥ := by
    intro he
    have hcard := suzukiSylow_omega_card hn (MulEquiv.refl _) U
    rw [he, Nat.card_unique] at hcard
    have hp : 1 < 2 ^ (2 * n + 1) := one_lt_pow₀ (by decide) (by omega)
    omega
  have he : U = T := suzuki_sylow_eq_of_inf_ne_bot n hn U T (by
    intro hh
    exact hne (bot_unique ((le_inf (omegaOneAmbient_le _) hUT).trans hh.le)))
  have hω : ((V F x 1).subgroupOf A).map q = omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup n)) := by
    simpa only [he] using hU
  have hk : q.ker = (Q F y).subgroupOf A := by
    have hk' : q.ker = pCore 2 A := by
      ext a
      change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff _ eSuz.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff a
    rw [hk', ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hderived := derived_le_seed_sup_kernel A (Q F m) (Q F y) (V F x 1) q hQA hVm hk (by
    rw [hT, hω, suzukiSylow_commutator_eq_omega hn (MulEquiv.refl _) T])
  have hseed : V F x 1 ⊔ (Q F m ⊓ Q F y) ≤
      (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) :=
    sup_le ((le_inf hVx hVm).trans le_sup_left)
      ((show Q F m ⊓ Q F y ≤ Q F y ⊓ Q F m from le_inf inf_le_right inf_le_left).trans le_sup_right)
  let B := Q F m ⊓ Q F y
  let : Finite B := Finite.of_injective
    (inclusion (show B ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m)))
    (inclusion_injective _)
  have hBnorm : B ≤ normalizer (V F x 1 : Set (G₀ L S)) :=
    (inf_le_left.trans (((source_Z_Q_U (reduced_triple h) m).2.trans
      (ballKernel_one_le_edge F hxm.symm)).trans inf_le_right)).trans
        (stabilizer_normalizes_V F x 1)
  have hinter : V F x 1 ⊓ B = V F x 1 ⊓ Q F y :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (le_inf inf_le_left (le_inf (inf_le_left.trans hVm) inf_le_right))
  have hiB : B.relIndex (V F x 1) = 2 ^ (2 * n + 1) := by
    rw [← inf_relIndex_left (V F x 1) B, hinter]
    exact hiV
  have hiQ : B.relIndex (Q F m) = (2 ^ (2 * n + 1)) ^ 2 :=
    hiCore.trans (suzukiSylow_card hn (MulEquiv.refl _) T)
  have hmul := relIndex_mul_relIndex B (V F x 1 ⊔ B) (Q F m)
    le_sup_right (sup_le hVm inf_le_left)
  rw [relIndex_sup_of_normalizes _ _ hBnorm, hiB, hiQ] at hmul
  have hindex : (V F x 1 ⊔ B).relIndex (Q F m) = 2 ^ (2 * n + 1) :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) _)
      (by simpa only [pow_two] using hmul)
  exact ⟨hderived, hderived.trans hseed, hindex,
    hindex ▸ relIndex_dvd_of_le_left (Q F m) hseed⟩

end ReducedLayer
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
