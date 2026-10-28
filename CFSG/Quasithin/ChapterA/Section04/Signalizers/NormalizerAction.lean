module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Global

/-!
# Normalizer actions represented in a local-core normalizer

Let X be a finite two-perfect subgroup normalized by a Sylow two-subgroup T.
A.4.2 identifies O₂(XT) as a Sylow subgroup of C_N(X/O₂(X)), where N=N_G(X).
Frattini's argument gives N=C_N(X/O₂(X)) N_N(O₂(XT)). Consequently every
N-action killed by the section centralizer has a representative in the actual
intersection N_G(X) ∩ N_G(O₂(XT)).

No characteristic-two or classification hypothesis is required. The application
to the original quotient action appears in the Chapter 15 Xi-minus argument.
Source: Aschbacher--Smith, A.4.2(4--5), printed p.57, and the normalizer step of
3.2.13, printed pp.584--585.
-/

public section
open Subgroup

namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- The original local core is Sylow in the normalizer section centralizer. -/
theorem sylow_core_sectionCentralizer (T : Sylow 2 G) (X : Subgroup G)
    (hX : IsPPerfect 2 X) (hT : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    ∃ P : Sylow 2 (twoSectionCentralizer X (normalizer (X : Set G))),
      (P : Subgroup _).map (twoSectionCentralizer X (normalizer (X : Set G))).subtype =
        (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let N := normalizer (X : Set G)
  let P : Sylow 2 N := T.subtype hT
  have hP : (P : Subgroup N).map N.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf N).map N.subtype = _
    exact map_subgroupOf_eq_of_le hT
  have hn : (X.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hmax := normal_sylow_core_isMaximal X N X.le_normalizer le_rfl hX P
  rw [hP] at hmax
  exact (maximal_signalizer_iff_sylow X N _ X.le_normalizer hn.isSubnormal hX).mp hmax

private theorem relative_frattini (C N : Subgroup G) (hCN : C ≤ N)
    (hNC : N ≤ normalizer (C : Set G))
    (P : Sylow 2 C) :
    C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) = N := by
  let C' := C.subgroupOf N
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hNC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCN).symm
  let P' : Sylow 2 C' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : ((P' : Subgroup C').map C'.subtype).map N.subtype =
      (P : Subgroup C).map C.subtype := by
    change (((P : Subgroup C).map e.toMonoidHom).map C'.subtype).map N.subtype = _
    rw [map_map, map_map]
    rfl
  have hf := congrArg (fun K : Subgroup N => K.map N.subtype) P'.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, N.range_subtype] at hf
  change _ ⊔ (C.subgroupOf N).map N.subtype = N at hf
  rw [map_subgroupOf_eq_of_le hCN] at hf
  apply le_antisymm (sup_le hCN inf_le_left)
  apply hf.symm.le.trans
  apply sup_le _ le_sup_left
  apply le_trans _ le_sup_right
  apply le_inf (map_subtype_le _)
  have hh := ((P' : Subgroup C').map C'.subtype).le_normalizer_map N.subtype
  rwa [hm] at hh

/-- Frattini factorization through the literal normalizer of O₂(XT). -/
theorem normalizer_core_factorization (T : Sylow 2 G) (X : Subgroup G)
    (hX : IsPPerfect 2 X) (hT : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    twoSectionCentralizer X (normalizer (X : Set G)) ⊔
      (normalizer (X : Set G) ⊓ normalizer ((X ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) =
        normalizer (X : Set G) := by
  obtain ⟨P, hP⟩ := sylow_core_sectionCentralizer T X hX hT
  simpa only [hP] using relative_frattini _ _ (twoSectionCentralizer_le _ _)
    (twoSectionCentralizer_normalized _ _ le_rfl) P

/-- Every original action value has a representative normalizing the local core. -/
theorem normalizer_core_covers_action {A : Type*} [Group A]
    (T : Sylow 2 G) (X : Subgroup G)
    (hX : IsPPerfect 2 X) (hT : (T : Subgroup G) ≤ normalizer (X : Set G))
    (f : normalizer (X : Set G) →* A)
    (hker : (twoSectionCentralizer X (normalizer (X : Set G))).subgroupOf
      (normalizer (X : Set G)) ≤ f.ker)
    (n : normalizer (X : Set G)) :
    ∃ m : ↥(normalizer (X : Set G) ⊓
        normalizer ((X ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)),
      f ⟨m, m.property.1⟩ = f n := by
  let N := normalizer (X : Set G)
  let C := twoSectionCentralizer X N
  let H := N ⊓ normalizer ((X ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)
  have hCH : C ⊔ H = N := normalizer_core_factorization T X hX hT
  have hHC : H ≤ normalizer (C : Set G) :=
    inf_le_left.trans (twoSectionCentralizer_normalized X N le_rfl)
  have hmem : (n : G) ∈ ((C ⊔ H : Subgroup G) : Set G) := hCH.symm ▸ n.property
  rw [coe_mul_of_right_le_normalizer_left C H hHC] at hmem
  obtain ⟨c, hc, m, hm, he⟩ := hmem
  have hcN : c ∈ N := twoSectionCentralizer_le X N hc
  have hn : (n : N) = (⟨c, hcN⟩ : N) * ⟨m, hm.1⟩ := Subtype.ext he.symm
  refine ⟨⟨m, hm⟩, ?_⟩
  change f ⟨m, hm.1⟩ = f n
  rw [hn, map_mul, (show f ⟨c, hcN⟩ = 1 from hker hc), one_mul]

end CFSG.Quasithin.ChapterA.Section04
