module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralFixerTerminal
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualNormalizerAt
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreAction
public import Theory.GroupAction.RankTwoCosetGeometry.ShortPaths
public import Theory.GroupTheory.SylowKernelCore

/-!
The index-two centralizer mover in Goldschmidt (6.11.2), printed p.402.
A subgroup of index at most two cannot have its edge intersection contained
in the opposite two-core: (2.15) and the existing index-two Sylow lift would
produce the excluded normal local three-subgroup.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem local_core_nontrivial (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (i : Bool) : (F i).pCoreIn 2 ≠ ⊥ := by
  intro he
  have hc : pCore 2 (F i) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (F i).subtype_injective).mp he
  have hn := h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA (RankTwo.base F i)
  have hbase : RankTwo.stabilizer F (RankTwo.base F i) = F i := stabilizer_base F i
  rw [hbase] at hn
  have ht : (⊤ : Subgroup (F i)) ≤ ⊥ := by
    intro x _
    rw [hc] at hn
    apply hn
    intro y hy
    have hy1 : y = 1 := mem_bot.mp hy
    rw [hy1, one_mul, mul_one]
  obtain ⟨e⟩ := h.local_quotient_symmetricThree_of_large_residual hC hA i
  have hi := SymmetricThreeTwoCore.core_index e
  have heq : pCore 2 (F i) = ⊤ := by rw [hc]; exact top_unique ht
  rw [heq, index_top] at hi
  omega

private theorem small_index_opposite_core_impossible (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (i : Bool) (H : Subgroup G) (hHA : H ≤ F i)
    (hind : H.relIndex (F i) ≤ 2)
    (hHC : H ⊓ (F false ⊓ F true) ≤ (F (!i)).pCoreIn 2) : False := by
  classical
  let : Finite (F i) := h.finite i
  let : Finite (F (!i)) := h.finite (!i)
  let : Finite H := Finite.of_injective (inclusion hHA) (inclusion_injective hHA)
  let T := F false ⊓ F true
  let Q := (F (!i)).pCoreIn 2
  let U := H ⊓ T
  have hTA : T ≤ F i := by
    cases i
    · exact inf_le_left
    · exact inf_le_right
  let : Finite T := Finite.of_injective (inclusion hTA) (inclusion_injective hTA)
  have hQT : Q ≤ T ∧ Q.relIndex T = 2 := by
    cases i
    · exact h.right_twoCore_overlap_of_large_residual hC hA
    · have hs := h.swap.right_twoCore_overlap_of_large_residual
        (fun j => hC (!j)) (fun j => hA (!j))
      change (F false).pCoreIn 2 ≤ F true ⊓ F false ∧
        ((F false).pCoreIn 2).relIndex (F true ⊓ F false) = 2 at hs
      change (F false).pCoreIn 2 ≤ T ∧ ((F false).pCoreIn 2).relIndex T = 2
      simpa only [T, inf_comm] using hs
  let : Finite Q := Finite.of_injective (inclusion hQT.1) (inclusion_injective hQT.1)
  have hUT : U.relIndex T ≤ 2 := by
    rw [show U = H ⊓ T from rfl, inf_relIndex_right]
    exact (relIndex_le_of_le_right (H := H) hTA (H.subgroupOf (F i)).index_ne_zero_of_finite).trans hind
  have hQU : Q = U := by
    have hm := relIndex_mul_relIndex U Q T hHC hQT.1
    rw [hQT.2] at hm
    have hn : 0 < U.relIndex Q := Nat.pos_of_ne_zero (U.subgroupOf Q).index_ne_zero_of_finite
    have he : U.relIndex Q = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp he) hHC
  have hUA : U.relIndex (F i) = 6 := by
    rw [← relIndex_mul_relIndex U T (F i) inf_le_right hTA, ← hQU,
      hQT.2, h.overlap_relIndex i]
  have hHind : H.relIndex (F i) = 2 := by
    have hp : 0 < H.relIndex (F i) := Nat.pos_of_ne_zero (H.subgroupOf (F i)).index_ne_zero_of_finite
    have hn : H.relIndex (F i) ≠ 1 := by
      intro he
      have hH : H = F i := le_antisymm hHA (relIndex_eq_one.mp he)
      have hU : U = T := by change H ⊓ T = T; rw [hH, inf_eq_right.mpr hTA]
      have hu : U.relIndex T = 1 := by rw [hU]; exact relIndex_self T
      rw [← hQU, hQT.2] at hu
      omega
    omega
  have hUH : U.relIndex H = 3 := by
    have hm := relIndex_mul_relIndex U H (F i) inf_le_left hHA
    rw [hHind, hUA] at hm
    omega
  let P : Sylow 2 H :=
    ((isPGroup_pCoreIn 2 (F (!i))).comap_subtype : IsPGroup 2 (Q.subgroupOf H)).toSylow
        (by change ¬ 2 ∣ Q.relIndex H; rw [hQU, hUH]; decide)
  have hPQ : (P : Subgroup H).map H.subtype = Q := by
    apply map_subgroupOf_eq_of_le
    change Q ≤ H
    rw [hQU]
    exact inf_le_left
  have hBN : F (!i) ≤ normalizer (Q : Set G) :=
    (F (!i)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F (!i))))
  have hnP : ¬ (P : Subgroup H).Normal := by
    intro hpn
    let : (H.subgroupOf (F i)).Normal := normal_of_index_eq_two hHind
    let : (P : Subgroup H).Characteristic := P.characteristic_of_normal hpn
    have hAN : F i ≤ normalizer (Q : Set G) := by
      rw [← hPQ]
      exact (le_normalizer_of_normal_subgroupOf hHA).trans
        (normalizer_le_normalizer_characteristic_image H (P : Subgroup H))
    have htop : (⊤ : Subgroup G) ≤ normalizer (Q : Set G) := by
      rw [← h.generated]
      cases i
      · exact sup_le hAN hBN
      · exact sup_le hBN hAN
    let : Q.Normal := normalizer_eq_top_iff.mp (top_unique htop)
    have hbot : Q = ⊥ := bot_unique
      ((normal_le_normalCore.mpr hQT.1).trans h.common_core_eq_bot.le)
    exact local_core_nontrivial h hC hA (!i) hbot
  have hiP : (P : Subgroup H).index = 3 := by change Q.relIndex H = 3; rw [hQU, hUH]
  obtain ⟨e⟩ := sylow_index_three_core_quotient P hiP
    (lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P)
      (fun he => hnP (by rw [← he]; infer_instance)))
  have hall := h.normal_three_of_opposite_normalized_sylow_at i H hHA P
    (hPQ ▸ hQT.1) (hPQ ▸ hBN) e
  let K := H.subgroupOf (F i)
  let f : K ≃* H := subgroupOfEquivOfLe hHA
  let S : Sylow 3 H := default
  let R : Sylow 3 K := S.mapSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  have hnR : (R : Subgroup K).Normal := (hall S).map f.symm.toMonoidHom f.symm.surjective
  obtain ⟨W, hW⟩ := normal_three_sylow_of_index_two K hHind R hnR
  exact h.local_sylow_three_not_normal_of_large_residual hC i W hW

private theorem small_index_vertex_core_impossible (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (H : Subgroup G) (hHA : H ≤ RankTwo.stabilizer F a)
    (hind : H.relIndex (RankTwo.stabilizer F a) ≤ 2)
    (hHC : H ⊓ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b) ≤
      (RankTwo.stabilizer F b).pCoreIn 2) : False := by
  obtain ⟨g, ha, hb⟩ := RankTwo.incident_common_translate F hab.2
  have htypes : b.type = !a.type := by
    have hn := hab.1
    cases h0 : a.type <;> cases h1 : b.type <;> simp_all
  rw [htypes] at hb
  let f := MulAut.conj g
  have hAa : (F a.type).map f.toMonoidHom = RankTwo.stabilizer F a := by
    conv_rhs => rw [← ha]
    simp only [RankTwo.stabilizer, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      RankTwo.base, stabilizer_base]
    rfl
  have hBb : (F (!a.type)).map f.toMonoidHom = RankTwo.stabilizer F b := by
    conv_rhs => rw [← hb]
    simp only [RankTwo.stabilizer, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      RankTwo.base, stabilizer_base]
    rfl
  let H₀ := H.map f.symm.toMonoidHom
  have hH : H₀.map f.toMonoidHom = H := by
    change (H.map f.symm.toMonoidHom).map f.toMonoidHom = H
    rw [map_map]
    simp
  have hH₀A : H₀ ≤ F a.type := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hH, hAa]
    exact hHA
  have hindex : H₀.relIndex (F a.type) ≤ 2 := by
    rw [← relIndex_map_map_of_injective H₀ (F a.type) (f := f.toMonoidHom) f.injective, hH, hAa]
    exact hind
  have hQ : H₀ ⊓ (F false ⊓ F true) ≤ (F (!a.type)).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [map_inf _ _ f.toMonoidHom f.injective, hH, map_pCoreIn_of_injective 2 _ f.toMonoidHom f.injective,
      hBb]
    have hT : (F false ⊓ F true).map f.toMonoidHom =
        RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b := by
      have he : F false ⊓ F true = F a.type ⊓ F (!a.type) := by
        cases a.type <;> simp [inf_comm]
      rw [he, map_inf _ _ f.toMonoidHom f.injective, hAa, hBb]
    rw [hT]
    exact hHC
  exact small_index_opposite_core_impossible h hC hA a.type H₀ hH₀A hindex hQ

private theorem two_path_fixer_le_core (h : CubicTreeAction F)
    {a b c : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hbc : (RankTwo.graph F).Adj b c) (hac : a ≠ c) {g : G}
    (ha : g • a = a) (hb : g • b = b) (hc : g • c = c) :
    g ∈ (RankTwo.stabilizer F b).pCoreIn 2 := by
  let B := RankTwo.stabilizer F b
  let E := (RankTwo.stabilizer F b ⊓ RankTwo.stabilizer F a).subgroupOf B
  have hp : IsPGroup 2 E := (h.edgeStabilizer_isPGroup hab.symm).comap_subtype
  have hcore : E.normalCore = pCore 2 B := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hp.to_le E.normalCore_le⟩
    · apply normal_le_normalCore.mpr
      intro x hx
      exact h.vertexTwoCore_le_edge hab ⟨x, hx, rfl⟩ |>.symm
  let p : SimpleGraph.BasedWalk (RankTwo.graph F) 2 a :=
    ⟨⟨b, hab⟩, ⟨⟨c, hbc⟩, PUnit.unit⟩⟩
  have hnb : p.Nonbacktracking := ⟨hac.symm, trivial⟩
  have hg : g ∈ RankTwo.pathStabilizer F p := by
    change ∀ x ∈ [a, b, c], g • x = x
    simp [ha, hb, hc]
  rw [RankTwo.pathStabilizer_two_eq_ballKernel_one F p hnb (h.card_neighbor b),
    RankTwo.ballKernel_one_eq_map_normalCore F hab.symm] at hg
  change g ∈ E.normalCore.map B.subtype at hg
  rwa [hcore] at hg

/-- Any index-at-most-two subgroup of the first vertex group has an edge
mover. This stronger form supplies the centralizer application without an
extra fixed-point premise on the centralized element. -/
theorem CubicTreeAction.exists_small_index_edge_mover (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    {a b c : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hbc : (RankTwo.graph F).Adj b c) (hac : a ≠ c)
    (H : Subgroup G) (hHA : H ≤ RankTwo.stabilizer F a)
    (hind : H.relIndex (RankTwo.stabilizer F a) ≤ 2) :
    ∃ x : G, x ∈ H ∧ x • b = b ∧ x • c ≠ c := by
  by_contra hn
  push Not at hn
  apply small_index_vertex_core_impossible h hC hA hab H hHA hind ?_
  intro x hx
  exact two_path_fixer_le_core h hab hbc hac hx.2.1 hx.2.2 (hn x hx.1 hx.2.2)

/-- The mover used immediately after Goldschmidt (6.11.2). -/
theorem CubicTreeAction.exists_centralizer_edge_mover (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    {a b c : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hbc : (RankTwo.graph F).Adj b c) (hac : a ≠ c)
    (v : G) (hind : (centralizer ({v} : Set G)).relIndex (RankTwo.stabilizer F a) ≤ 2) :
    ∃ x : G, Commute v x ∧ x • a = a ∧ x • b = b ∧ x • c ≠ c := by
  obtain ⟨x, hx, hxb, hxc⟩ := h.exists_small_index_edge_mover hC hA hab hbc hac
    (centralizer ({v} : Set G) ⊓ RankTwo.stabilizer F a) inf_le_right
    (by rwa [inf_relIndex_right])
  exact ⟨x, hx.1 v (Set.mem_singleton v), hx.2, hxb, hxc⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

