module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CanonicalCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreBounds
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# The exact remaining Suzuki middle-core alternative

For Suzuki neighbors x,y of the linear middle vertex m, the proposed
product N = (Q_x ∩ Q_m)(Q_y ∩ Q_m) is invariant under the full middle
stabilizer. Project into the original marked Suzuki quotient at y. The
image contains the entire Sylow center, by the first index of (12.3)(a),
and is invariant under its full Borel. The split torus scales the first
root coordinate, so this image is either the center or the full Sylow.

Lifting these alternatives through the literal quotient kernel gives
N = Q_m or N = V_x (Q_m ∩ Q_y) with index q in Q_m. In particular the
previous order-dividing-q central quotient has order exactly one or q.
The latter alternative remains an obligation; this does not establish
the middle-core equality or DGS (12.9)/(13.1). Earlier critical geometry
and common-Sylow markings remain explicit source inputs.

The intentional implementation import reuses this family's private
base-neighbor/Sylow-normalizer calculation without changing its API.
`SuzukiCoreApplication` retains both alternatives under the original
parabolic inclusion and on the actual central quotient.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3), printed pp.178--180. The root coordinate calculation uses
Huppert--Blackburn III, XI.3.1--3.3, in the existing Suzuki matrix convention.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.SchurCover.Family

private theorem root_subgroup_eq_center_or_full (n : ℕ) (hn : 0 < n)
    (E : Subgroup (SuzukiMatrixGroup n))
    (hEZ : (center (SuzukiRootSubgroup n)).map (SuzukiRootSubgroup n).subtype ≤ E)
    (hEU : E ≤ SuzukiRootSubgroup n)
    (hN : normalizer (SuzukiRootSubgroup n : Set (SuzukiMatrixGroup n)) ≤
      normalizer (E : Set (SuzukiMatrixGroup n))) :
    E = (center (SuzukiRootSubgroup n)).map (SuzukiRootSubgroup n).subtype ∨
      E = SuzukiRootSubgroup n := by
  by_cases hEZ' : E ≤ (center (SuzukiRootSubgroup n)).map (SuzukiRootSubgroup n).subtype
  · exact Or.inl (le_antisymm hEZ' hEZ)
  right
  apply le_antisymm hEU
  obtain ⟨u,hu,huZ⟩ := Set.not_subset.mp hEZ'
  let r : SuzukiRootSubgroup n := ⟨u,hEU hu⟩
  obtain ⟨a,b,hab⟩ := rootPoint_surjective n r
  have hu' : (rootPoint n a b).val ∈ E := by rw [← hab]; exact hu
  have ha : a ≠ 0 := by
    intro ha
    apply huZ
    refine ⟨r, ?_, rfl⟩
    rw [hab, ← root_commutator_eq_center n hn, ← rootCoordinate_ker n hn]
    change rootCoordinate n hn (rootPoint n a b) = 1
    rw [rootCoordinate_rootPoint, ha]
    rfl
  have hequal (v w : SuzukiRootSubgroup n)
      (he : rootCoordinate n hn v = rootCoordinate n hn w)
      (hw : w.val ∈ E) : v.val ∈ E := by
    have hker : v * w⁻¹ ∈ center (SuzukiRootSubgroup n) := by
      rw [← root_commutator_eq_center n hn, ← rootCoordinate_ker n hn]
      change rootCoordinate n hn (v * w⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hh := E.mul_mem (hEZ (mem_map_of_mem (SuzukiRootSubgroup n).subtype hker)) hw
    change (v.val * w.val⁻¹) * w.val ∈ E at hh
    simpa only [inv_mul_cancel_right] using hh
  intro v hv
  let s : SuzukiRootSubgroup n := ⟨v,hv⟩
  obtain ⟨c,d,hcd⟩ := rootPoint_surjective n s
  change s.val ∈ E
  rw [hcd]
  by_cases hc : c = 0
  · apply hequal (rootPoint n c d) 1
    · simp only [rootCoordinate_rootPoint, map_one, hc]; rfl
    · exact E.one_mem
  let t : (Field n)ˣ := Units.mk0 (c / a) (div_ne_zero hc ha)
  have ht : torusPoint n hn t ∈ normalizer (E : Set (SuzukiMatrixGroup n)) :=
    hN (suzukiSplitTorus_le_normalizer_root n (torusPoint_mem n hn t))
  have hh := (mem_normalizer_iff.mp ht (rootPoint n a b).val).mp hu'
  rw [torusPoint_conj] at hh
  have htca : (t : Field n) * a = c := div_mul_cancel₀ c ha
  rw [htca] at hh
  exact hequal (rootPoint n c d) (rootPoint n c (t * suzukiTits n t * b))
    ((rootCoordinate_rootPoint n hn c d).trans
      (rootCoordinate_rootPoint n hn c (t * suzukiTits n t * b)).symm) hh

private theorem suzuki_subgroup_eq_center_or_full
    {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : 0 < n)
    (e : X ≃* SuzukiMatrixGroup n) (T : Sylow 2 X)
    (E : Subgroup X)
    (hEZ : (center T).map (T : Subgroup X).subtype ≤ E)
    (hET : E ≤ T)
    (hN : normalizer (T : Set X) ≤ normalizer (E : Set X)) :
    E = (center T).map (T : Subgroup X).subtype ∨ E = T := by
  obtain ⟨f,hT,hB⟩ := suzukiSylow_aligned_equiv hn e T
  have hf : (T : Subgroup X).map f.symm.toMonoidHom = SuzukiRootSubgroup n := by
    rw [← hT, map_map]
    simp
  have hEZ' := map_mono (f := f.symm.toMonoidHom) hEZ
  rw [map_embeddedCenter _ _ f.symm.injective, hf] at hEZ'
  have hET' := map_mono (f := f.symm.toMonoidHom) hET
  rw [hf] at hET'
  have hN' := map_mono (f := f.symm.toMonoidHom) hN
  change (normalizer ((T : Subgroup X) : Set X)).map f.symm.toMonoidHom ≤
    (normalizer (E : Set X)).map f.symm.toMonoidHom at hN'
  rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq, hf] at hN'
  rcases root_subgroup_eq_center_or_full n hn _ hEZ' hET' hN' with he | he
  · left
    apply map_injective (f := f.symm.toMonoidHom) f.symm.injective
    rw [map_embeddedCenter _ _ f.symm.injective, hf]
    exact he
  · exact Or.inr ((map_injective f.symm.injective) (he.trans hf.symm))
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem source_sylow_normalizer_preimage
    {M : Type*} [Group M]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* M)
    (P : Sylow 2 M)
    (hP : ((Q (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf (star L S i)).map
      (((originalQuotient h i).symm.trans e).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (star L S i)))) = (P : Subgroup M)) :
    (normalizer (P : Set M)).comap
      (((originalQuotient h i).symm.trans e).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (star L S i)))) =
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf (star L S i) := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    ext a
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff a
  obtain ⟨R,hR⟩ := base_star_sylow_normalizer h i
  let T : Sylow 2 M := R.mapSurjective (f := q) hq
  have hRT : (T : Subgroup M).comap q = (R : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal R
  have hn : (normalizer (T : Set M)).comap q = normalizer (R : Set A) := by
    rw [← Sylow.coe_coe, comap_normalizer_eq_of_surjective _ hq, hRT, Sylow.coe_coe]
  have hPT : (P : Subgroup M) ≤ normalizer (T : Set M) := by
    rw [← hP]
    apply map_le_iff_le_comap.mpr
    rw [hn, ← hR]
    exact subgroupOf_mono A (Q_le_stabilizer F _)
  have hle : (P : Subgroup M) ≤ T := by
    rw [← inf_eq_left.mpr hPT, P.isPGroup'.inf_normalizer_sylow T]
    exact inf_le_right
  have he : P = T := Sylow.ext ((P.is_maximal' T.isPGroup' hle).symm)
  rw [he]
  exact hn.trans hR.symm

/-- The full-stabilizer invariant product is the middle core, or the literal seed product of index q. -/
theorem source_suzuki_middle_core_product_or_seed
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
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (T U : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hU : (U : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    let m := base F (!i)
    let y := base F i
    let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
    stabilizer F m ≤ normalizer (N : Set (G₀ L S)) ∧
      (N = Q F m ∨
        N = V F x 1 ⊔ (Q F m ⊓ Q F y) ∧ N.relIndex (Q F m) = 2 ^ (2 * n + 1)) := by
  let F := reducedFamily L S
  let A := star L S i
  let m := base F (!i)
  let y := base F i
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  let C := Q F m ⊓ Q F y
  let D := V F x 1 ⊔ C
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hne : x ≠ y := by
    intro he
    have hseed : Z F a ≤ V F x 1 :=
      le_iSup_of_le a (le_iSup_of_le ((mem_ball_one F x a).mpr (Or.inl hxa)) le_rfl)
    have hV := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
    exact hc.2 (hseed.trans (hV.trans (by rw [he]; exact hQU y)))
  have hgen : star L S (!i) = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h (!i) hxm.symm
      (by simpa only [Bool.not_not] using hne) T U
      (by simpa only [Bool.not_not] using hT) hU
    simpa only [Bool.not_not, sup_comm, sup_left_comm, sup_assoc] using hh
  have hnN : stabilizer F m ≤ normalizer (N : Set (G₀ L S)) :=
    middle_core_product_full_normalizer F hQU hxm hadj (star L S (!i))
      (star_le_stabilizer (!i)) hgen
      (fun v hv => star_locally_transitive h (!i) hadj.symm hv)
  refine ⟨hnN, ?_⟩
  have hVx := V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x
  have hVm := V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxm
  have hQN : N ≤ Q F m := sup_le inf_le_right inf_le_right
  have hDN : D ≤ N := sup_le ((le_inf hVx hVm).trans le_sup_left)
    ((le_inf inf_le_right inf_le_left).trans le_sup_right)
  have hCN : C ≤ N := le_sup_right.trans hDN
  have hQA : Q F m ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  let q := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := ((originalQuotient h i).symm.trans eSuz).surjective.comp
    (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP,hiCore,_⟩ := source_common_sylow_core_index h i eSuz R hR
  obtain ⟨hiV,_,P',hP'⟩ := source_suzuki_first_index h i hb hc hxa hxm hadj hn eSuz eLin R hR
  have hωP : omegaOneAmbient (P' : Subgroup (SuzukiMatrixGroup n)) ≤ P := by
    rw [← hP', ← hP]
    exact map_mono (subgroupOf_mono A hVm)
  have hωne : omegaOneAmbient (P' : Subgroup (SuzukiMatrixGroup n)) ≠ ⊥ := by
    intro he
    have hcard := suzukiSylow_omega_card hn (MulEquiv.refl _) P'
    rw [he, Nat.card_unique] at hcard
    have hp : 1 < 2 ^ (2 * n + 1) := one_lt_pow₀ (by decide) (by omega)
    omega
  have hPP : P' = P := suzuki_sylow_eq_of_inf_ne_bot n hn P' P (by
    intro hh
    exact hωne (bot_unique ((le_inf (omegaOneAmbient_le _) hωP).trans hh.le)))
  have hVP : ((V F x 1).subgroupOf A).map q = (center P).map (P : Subgroup (SuzukiMatrixGroup n)).subtype := by
    rw [hPP, suzukiSylow_omega_eq_center hn (MulEquiv.refl _) P] at hP'
    exact hP'
  have hker : q.ker = (Q F y).subgroupOf A := by
    have hk' : q.ker = pCore 2 A := by
      ext a
      change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff _ eSuz.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff a
    rw [hk', ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  let E := (N.subgroupOf A).map q
  have hEP : E ≤ P := by
    rw [← hP]
    exact map_mono (subgroupOf_mono A hQN)
  have hZE : (center P).map (P : Subgroup (SuzukiMatrixGroup n)).subtype ≤ E := by
    rw [← hVP]
    exact map_mono (subgroupOf_mono A (le_sup_left.trans hDN))
  have hNE : normalizer (P : Set (SuzukiMatrixGroup n)) ≤ normalizer (E : Set (SuzukiMatrixGroup n)) := by
    have hn := source_sylow_normalizer_preimage h i eSuz P hP
    intro g hg
    obtain ⟨a,rfl⟩ := hq g
    have ha : a ∈ (stabilizer F m).subgroupOf A := hn ▸ hg
    have haN : a ∈ normalizer (N.subgroupOf A : Set A) :=
      le_normalizer_comap A.subtype (hnN ha)
    exact (N.subgroupOf A).le_normalizer_map q (mem_map_of_mem q haN)
  have hindex : C.relIndex N = Nat.card E := by
    have hinter : N ⊓ C = N ⊓ Q F y :=
      le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
        (le_inf inf_le_left (le_inf (inf_le_left.trans hQN) inf_le_right))
    rw [← inf_relIndex_left N C, hinter, inf_relIndex_left,
      ← relIndex_subgroupOf (hQN.trans hQA), ← hker, relIndex_ker]
  have hcoreIndex : C.relIndex (Q F m) = (2 ^ (2 * n + 1)) ^ 2 :=
    hiCore.trans (suzukiSylow_card hn (MulEquiv.refl _) P)
  have hmul := relIndex_mul_relIndex C N (Q F m) hCN hQN
  rcases suzuki_subgroup_eq_center_or_full hn (MulEquiv.refl _) P E hZE hEP hNE with he | he
  · have hCE : Nat.card E = 2 ^ (2 * n + 1) := by
      rw [he, card_map_of_injective (P : Subgroup (SuzukiMatrixGroup n)).subtype_injective]
      exact (suzukiSylow_borel_structure hn (MulEquiv.refl _) P).1
    rw [hindex,hCE,hcoreIndex] at hmul
    have hiN : N.relIndex (Q F m) = 2 ^ (2 * n + 1) :=
      Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) _)
        (by simpa only [pow_two] using hmul)
    have hiD := (source_suzuki_middle_core_bounds h i hb hc hxa hxm hn eSuz eLin R hR).2.2.1
    have hm := relIndex_mul_relIndex D N (Q F m) hDN hQN
    change D.relIndex N * N.relIndex (Q F m) = D.relIndex (Q F m) at hm
    rw [hiN, hiD] at hm
    have hiDN : D.relIndex N = 1 := Nat.eq_of_mul_eq_mul_right
      (pow_pos (by decide : 0 < (2 : ℕ)) _) (by simpa only [one_mul] using hm)
    exact Or.inr ⟨le_antisymm (relIndex_eq_one.mp hiDN) hDN, hiN⟩
  · have hCE : Nat.card E = (2 ^ (2 * n + 1)) ^ 2 := by
      rw [he]
      exact suzukiSylow_card hn (MulEquiv.refl _) P
    rw [hindex,hCE,hcoreIndex] at hmul
    have hiN : N.relIndex (Q F m) = 1 := Nat.eq_of_mul_eq_mul_left
      (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)
      (by simpa only [mul_one] using hmul)
    exact Or.inl (le_antisymm hQN (relIndex_eq_one.mp hiN))
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
