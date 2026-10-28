module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathCartanExtension
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# Centralizing exchange for two neighboring full kernels

The intersection of the two neighboring full permutation kernels is
normalized by their common Cartan and by a linear exchanger at the middle
vertex. The Cartan intersection is a Hall subgroup there. Hall conjugacy
corrects the exchanger to normalize that intersection; the full edge
complement removes the Cartan part of the correction. The resulting
exchanger remains in the intrinsic local actor, so disjointness from that
actor makes its action on the Hall subgroup trivial.

This uses no middle-kernel containment. The displacement bound and the
natural middle center supply the retained disjointness in source 9.10(3).
The literal reduced-graph application is assembled with
`BetaKernelDisplacement` by the distance-three consumer.

Source: DGS, *Groups and Graphs* (1985), 9.10(3), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

private theorem hall_normalizer_correction (W D : Subgroup G) [Finite W]
    (hs : Group.IsSolvable W) (hDW : D ≤ W)
    (hD : IsHallSubgroup OddHall.oddPrimes (D.subgroupOf W))
    (t : G) (ht : t ∈ normalizer (W : Set G)) :
    ∃ w ∈ W, w⁻¹ * t ∈ normalizer (D : Set G) := by
  let a : MulAut W := W.normalizerMonoidHom ⟨t,ht⟩
  obtain ⟨w,hw⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hs
    hD (hD.map_mulAut a)
  have hmap : D.map (MulAut.conj t).toMonoidHom =
      D.map (MulAut.conj (w : G)).toMonoidHom := by
    have he := congrArg (Subgroup.map W.subtype) hw
    rw [map_map,map_map] at he
    have hleft : W.subtype.comp a.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp W.subtype := rfl
    have hright : W.subtype.comp (MulAut.conj w).toMonoidHom =
        (MulAut.conj (w : G)).toMonoidHom.comp W.subtype := rfl
    rw [hleft,hright,←map_map,←map_map,map_subgroupOf_eq_of_le hDW] at he
    exact he
  refine ⟨w,w.property,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  change D.map (MulAut.conj ((w : G)⁻¹*t)).toMonoidHom = D
  have he := congrArg (Subgroup.map (MulAut.conj (w : G)⁻¹).toMonoidHom) hmap
  simp only [map_map] at he
  have hleft : (MulAut.conj (w : G)⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj ((w : G)⁻¹*t)).toMonoidHom := by ext; simp [mul_assoc]
  have hright : (MulAut.conj (w : G)⁻¹).toMonoidHom.comp (MulAut.conj (w : G)).toMonoidHom =
      MonoidHom.id G := by ext; simp [mul_assoc]
  simpa only [hleft,hright,map_id] using he

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full Cartan intersection of two neighboring kernels has a
centralizing exchanger once it avoids the middle intrinsic actor. -/
theorem full_cartan_two_kernel_centralizing_exchange
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x beta a' : Vertex (family P)}
    (hxb : (graph (family P)).Adj x beta) (hxa : (graph (family P)).Adj x a')
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (C : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) x ⊓ stabilizer (family P) beta)
    (hCa : C ≤ stabilizer (family P) a') (ho : Odd (Nat.card C))
    (hgen : C ⊔ (stabilizer (family P) x ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2 =
      stabilizer (family P) x ⊓ stabilizer (family P) beta)
    (hd : Disjoint (C ⊓ (ballKernel (family P) beta 1 ⊓ ballKernel (family P) a' 1))
      (graphLocalGroup (family P) x)) :
    ∃ g ∈ graphLocalGroup (family P) x ⊓
        centralizer ((C ⊓ (ballKernel (family P) beta 1 ⊓ ballKernel (family P) a' 1) : Subgroup G) : Set G),
      g • beta = a' ∧ g • a' = beta := by
  let := finite_endpoints h
  let Γ := family P
  let E := stabilizer Γ x ⊓ stabilizer Γ beta
  let S := E.pCoreIn 2
  let H := graphLocalGroup Γ x
  let W := ballKernel Γ beta 1 ⊓ ballKernel Γ a' 1
  let D := C ⊓ W
  have hWE : W ≤ E := (inf_le_left.trans (ballKernel_one_le_edge Γ hxb.symm)).trans
    (by rw [inf_comm])
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ x from inf_le_left))
    (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWE) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion hCE) (inclusion_injective _)
  let : Finite S := Finite.of_injective (inclusion (pCoreIn_le 2 E)) (inclusion_injective _)
  have hES : E ≤ normalizer (S : Set G) := E.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hCW : C ≤ normalizer (W : Set G) := by
    exact (le_inf ((hCE.trans inf_le_right).trans (stabilizer_le_normalizer_ballKernel Γ beta 1))
      (hCa.trans (stabilizer_le_normalizer_ballKernel Γ a' 1))).trans
      inf_normalizer_le_normalizer_inf
  have hHallC := OddHall.oddHall_of_normalized_sup (isPGroup_pCoreIn 2 E)
    ho.coprime_two_left (hCE.trans hES) (show S ⊔ C = E by rw [sup_comm]; exact hgen)
  have hHallD : IsHallSubgroup OddHall.oddPrimes (D.subgroupOf W) := by
    simpa only [D,inf_subgroupOf_right] using
      OddHall.hall_restrict_of_normalizes hHallC hCE hWE hCW
  have hsolv : Group.IsSolvable E := by
    let : Group.IsSolvable S := @IsNilpotent.to_isSolvable _ _ (isPGroup_pCoreIn 2 E).isNilpotent
    have hh := Group.isSolvable_sup_of_normalizes S C (hCE.trans hES)
    rwa [sup_comm,hgen] at hh
  let := hsolv
  have hsolvW : Group.IsSolvable W :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hWE)
  obtain ⟨t,htb,hta,_⟩ := linear_local_neighbor_exchange h hB hS hxb hxa e
  have htW : (t : G) ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change W.map (MulAut.conj (t : G)).toMonoidHom = W
    rw [show W = ballKernel Γ beta 1 ⊓ ballKernel Γ a' 1 from rfl,
      map_inf _ _ _ (MulAut.conj (t : G)).injective,
      ←ballKernel_translate,←ballKernel_translate,htb,hta,inf_comm]
  obtain ⟨w,hw,hwn⟩ := hall_normalizer_correction W D hsolvW inf_le_right hHallD t htW
  have hwprod : w ∈ (S : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left S C (hCE.trans hES),sup_comm,hgen]
    exact hWE hw
  obtain ⟨s,hs,c,hc,rfl⟩ := hwprod
  have hcn : c ∈ normalizer (D : Set G) :=
    (Subgroup.centralizer_le_normalizer _) ((centralizer_le (show D ≤ C from inf_le_left))
      (le_centralizer C hc))
  have hsn : s⁻¹ * (t : G) ∈ normalizer (D : Set G) := by
    have hh := (normalizer (D : Set G)).mul_mem hcn hwn
    simpa only [mul_inv_rev,←mul_assoc,mul_inv_cancel,one_mul] using hh
  have hsH : s ∈ H := by
    obtain ⟨R,hR⟩ := local_edge_sylow h hB hS hxb
    change s ∈ (stabilizer Γ x ⊓ stabilizer Γ beta : Subgroup G).pCoreIn 2 at hs
    rw [←hR] at hs
    exact map_subtype_le _ hs
  have hsfixb : s • beta = beta := (pCoreIn_le 2 E hs).2
  have hsfixa : s • a' = a' := by
    have hh := (ballKernel_le_stabilizer Γ a' 1) hw.2
    change (s*c) • a' = a' at hh
    rwa [mul_smul,hCa hc] at hh
  let g := s⁻¹ * (t : G)
  have hgH : g ∈ H := H.mul_mem (H.inv_mem hsH) t.property
  refine ⟨g,⟨hgH,?_⟩,?_,?_⟩
  · intro d hdD
    have hdHn : d ∈ normalizer (H : Set G) :=
      sylowGenerated_normalized _ ((hCE hdD.1).1)
    have hcommD : g*d*g⁻¹*d⁻¹ ∈ D := D.mul_mem
      ((mem_normalizer_iff.mp hsn d).mp hdD) (D.inv_mem hdD)
    have hcommH : g*d*g⁻¹*d⁻¹ ∈ H := by
      have hh := (mem_normalizer_iff.mp hdHn g⁻¹).mp (H.inv_mem hgH)
      simpa only [mul_assoc] using H.mul_mem hgH hh
    have he := disjoint_def.mp hd hcommD hcommH
    exact (mul_inv_eq_one.mp he |> mul_inv_eq_iff_eq_mul.mp).symm
  · change (s⁻¹*(t : G)) • beta = a'
    rw [mul_smul,htb,inv_smul_eq_iff]
    exact hsfixa.symm
  · change (s⁻¹*(t : G)) • a' = beta
    rw [mul_smul,hta,inv_smul_eq_iff]
    exact hsfixb.symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
